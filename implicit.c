/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Jungle Hi",
    /* First member's full name */
    "Implicit free list",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
/* 매크로 */
#define WSIZE 4     // 워드와 헤더/푸터 사이즈
#define DSIZE 8     // 더블 워드 사이즈
#define CHUNKSIZE (1<<12)   // 힙을 한번 늘릴 때 필요한 사이즈 = 이 양만큼 힙을 확장함 (4kb 분량)

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* 정렬 유지를 위해 가까운 배수로 반올림 */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 return */
#define PACK(size, alloc) ((size) | (alloc))

/* 인자 p가 참조하는 워드 읽어서 return */
/* 인자 p는 대개 (void*) 포인터. 직접적으로 역참조 불가 */ 
#define GET(p) (*(unsigned int*)(p))
/* p가 가리키는 워드에 val 저장 */
#define PUT(p, val) (*(unsigned int*)(p)=(val))

/* 주소 p에 있는 사이즈와 할당된 필드를 읽는다 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)     // 1이면 allocated 0이 free

/* 블록 포인터 bp가 주어지면, 각각 블록 헤더와 풋터를 가리키는 포인터 return */
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp가 주어지면, 각각 다음과 이전 블록의 블록 포인터를 return */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

/* 함수 선언 */
static void *find_fit(size_t asize);
static void *coalesce(void* bp);
static void placement(void *bp, size_t asize);
static void *extend_heap(size_t words);

/* 정적 전역 변수 */
static void *heap_listp;  // first_fit에서 사용하기 위한 정적 전역변수
static void *next_bp;     // next_fit에서 사용하기 위한 정적 전역변수

/* 
 * mm_init - 할당기 초기화
 */
int mm_init(void) {   
    /* 초기값으로 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void*)-1)
        return -1;
        
    PUT(heap_listp, 0);     // padding을 한 워드 크기만큼 생성
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // 에필로그 헤더
    heap_listp += (2*WSIZE);    // 프롤로그 헤더와 프롤로그 푸터 사이로 포인터 옮김

    // CHUNKSIZE = 4096, 빈 힙을 CHUNKSIZE 바이트의 사용 가능한 블록으로 확장
    // 공간이 없다면 return -1
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap - 새로운 free block과 함께 heap 확장
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 64bit 운영체제는 주소 단위를 8바이트로 읽기 때문에 최소 8바이트가 필요
    // 짝수 * 4 = 무조건 8의 배수이기 때문에 홀수일 때 짝수로 만들어서 *4를 함
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    
    // size 크기만큼 heap을 확장시킨다. 확장할 공간이 없다면 return NULL
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* 가용 블럭의 헤더, 푸터 & 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size, 0));    // free block 헤더
    PUT(FTRP(bp), PACK(size, 0));    // free block 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    // new 에필로그 헤더

    /* 이전 블록이 free라면 병합 */
    return coalesce(bp);
}

/* 
 * mm_malloc - 가용 리스트에서 size 바이트의 메모리 블록 할당 요청   
 */
void *mm_malloc(size_t size) {
    size_t asize;       // 블록 사이즈 조정
    size_t extendsize;  // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;   // 

    // 거짓된 요청 무시
    if (size == 0)
        return NULL;

    // 오버헤드, alignment 요청 포함해서 블록 사이즈 조정
    if (size <= DSIZE)
        asize = 2 * DSIZE;    // 헤더와 푸터를 포함해서 블록 사이즈를 다시 조정해야되니까 DSIZE의 2배
    
    else
        /* 할당할 크기가 8바이트보다 크면 8의 배수로 맞춰줘야 하기 때문에
        header+footer의 크기인 (8바이트 + 7바이트 + 할당할 크기) / 8
        을 하면 나머지는 버려지고 몫만 남는데 그 몫 * 8을 하면
        할당할 크기를 담을 수 있는 최소한의 크기의 8의 배수를 구할 수 있음 */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    // find_fit으로 asize의 크기를 넣을 수 있는 공간이 있다면
    if ((bp = find_fit(asize)) != NULL) {
        placement(bp, asize);
        return bp;     // placement를 마친 블록의 위치를 리턴
    }
    // find_fit 맞는게 없는 경우 = 새 가용블록으로 힙을 확장
    extendsize = MAX(asize,CHUNKSIZE);  // asize와 CHUNKSIZE(우리가 원래 처음에 세팅한 사이즈) 중에 더 큰거 넣음
    // 확장할 공간이 더 남아있지 않다면 NULL 반환
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    // 확장이 됐다면, asize만큼 공간을 할당하고 잘라줌
    placement(bp,asize);
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/*
 * find_fit - 할당할 가용 블록 크기(asize)가 가용 리스트에 있는지 탐색
 */
static void *find_fit(size_t asize) {
    /* first-fit */
    void *bp;
    
    // GET_SIZE(HDRP(bp)) > 0
    for (bp=heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)) {
        // 현재, 블록이 가용 상태이고 할당하고 싶은 사이즈(asize)가 현재 블록보다 작거나 같을 때 bp 반환
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    // for문 종료됐다면 알맞는 크기가 없다는 것이므로 NULL 반환
    return NULL;
}

static void *find_fit(size_t asize) {
    /* next-fit */
    void *bp;
    
    // next_fit 전용 bp부터 찾기 시작
    for (bp=next_bp; GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)) {
        // 현재, 블록이 가용 상태이고 할당하고 싶은 사이즈(asize)가 현재 블록보다 작거나 같을 때 bp 반환
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    
    // 끝까지 갔는데도 없으면 다시 처음부터 돌기 시작
    for (bp=heap_listp; bp!=next_bp; bp=NEXT_BLKP(bp)) {
        // 현재, 블록이 가용 상태이고 할당하고 싶은 사이즈(asize)가 현재 블록보다 작거나 같을 때 bp 반환
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
}

/*
 * placement - 할당할 크기와 맞는 블록을 찾으면(find_fit 통과) 블록을 배치
 */
static void placement(void *bp, size_t asize) {
    // 여기서 현재 사이즈 = 할당이 될 블록
    size_t cur_size = GET_SIZE(HDRP(bp));
    
    // asize만큼 넣고도 나머지가 최소블록크기(16byte) 이상이라면 분할 가능
    if ((cur_size - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));  // 헤더 위치에 asize 넣고 할당 상태로 변경  
        PUT(FTRP(bp), PACK(asize, 1));  // 푸터 위치에 asize 넣고 할당 상태로 변경
        bp = NEXT_BLKP(bp);  // bp위치를 다음 블록 위치로 갱신
    
        // asize 할당 후 남은 공간 분할해서 가용 상태로 변경
        PUT(HDRP(bp), PACK(cur_size-asize, 0)); // 나머지 블록(cur-asize)은 free라는 걸 헤더에 표시
        PUT(FTRP(bp), PACK(cur_size-asize, 0)); // 푸터도 표시
    }
    // 분할할 정도의 크기는 아니라면 그냥 할당
    else {
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
    }
}

/*
 * mm_free - 요청한 블록 반환하고, 경계 태그 연결 사용해서 상수 시간에 인접한 가용 블럭들과 병합
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    // 헤더 & 푸터 free
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesc - 가용 블럭 생성시 통합 
 */
static void *coalesce(void* bp) {
    // 직전 블록의 푸터, 직후 블록의 헤더 통해 가용 여부 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));   // 현재 블록의 사이즈

    // CASE 1: 전후 모두 할당이면
    if (prev_alloc && next_alloc) {
        next_bp = bp;  // next_bp에 bp위치를 저장
        return bp;
    }

    // CASE 2: 이전은 할당, 다음은 free
    else if (prev_alloc && !next_alloc) { 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // CASE 3: 이전은 free, 다음은 할당
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);     // free 시작점 변경
    }

    // CASE 4: 전후 모두 free
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    next_bp = bp;  // next_bp에 bp위치를 저장
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}