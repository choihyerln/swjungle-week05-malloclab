#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "week5-team2","yoon","science627@naver.com","",""
};

#define WSIZE 4 //Word Size 4byte
#define DSIZE 8 //Double Word Size 8byte
#define CHUNKSIZE (1<<10) //초기 가용블럭과 힙확장을 위한 기본 크기
#define MAX(x,y) ((x)>(y)?(x):(y))
#define PACK(size,alloc) ((size)|(alloc)) //size와 할당여부를 하나의 숫자로 묶기
#define GET(p) (*(unsigned int*)(p)) //GET:p의 참조값을 가져옴
#define PUT(p,val) (*(unsigned int*)(p)=(val)) //PUT: p의 참조값(p가 가리키는 워드값)을 val로 바꿔줌
#define GET_SIZE(p) (GET(p) & ~0x7) //GET_SIZE: p의 주소에 있는 헤더,푸터의 사이즈값 리턴
#define GET_ALLOC(p) (GET(p) & 0x1) //GET_ALLOC: p의 주소에 있는 헤더,푸터의 할당여부 리턴
#define HDRP(bp) ((char*)(bp)-WSIZE) //HDRP 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char*)(bp)+GET_SIZE(HDRP(bp))-DSIZE) //FTRP 푸터를 가리키는 포인터 리턴
#define NEXT_BLKP(bp) ((char*)(bp)+GET_SIZE(((char*)(bp)-WSIZE))) //NEXT_BLKP 다음 블록을 가리키는 포인터 리턴
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE(((char*)(bp)-DSIZE))) //PREV_BLKP 이전 블록을 가리키는 포인터 리턴

#define PRED_P(bp) (*(void**)(bp)) //가용블록 리스트중 이전 블록을 가리키는 포인터
#define SUCC_P(bp) (*(void**)(bp+WSIZE)) //가용블록 리스트중 다음 블록을 가리키는 포인터

static void *heap_listp; //heap의 시작점을 알려줌
static void *coalesce(void *bp); //가용블록들 연결
static void *extend_heap(size_t words); //힙의 메모리가 부족할때 늘려줌
static void *find_fit(size_t asize); //구현된 방식에 따라 적절한 가용블록 찾아줌
static void place(void *p,size_t size); // 

static void list_add(void *p); //리스트에 가용블록 추가
static void list_remove(void *p); //리스트에 가용블록 제거

//////////////////// START OF HELPER FUNCTION ////////////////////
static void list_add(void *bp){
    void *ptr = heap_listp;
    if(SUCC_P(ptr)==ptr){//heaplist가 비어있는 경우
        PRED_P(bp) = ptr;
        SUCC_P(bp) = ptr;
        PRED_P(ptr) = bp;
        SUCC_P(ptr) = bp;
    }else{
        for(ptr=SUCC_P(heap_listp);!GET_ALLOC(HDRP(ptr));ptr=SUCC_P(ptr)){
            if(ptr<bp){
                PRED_P(SUCC_P(ptr)) = bp;
                SUCC_P(bp) = SUCC_P(ptr);
                PRED_P(bp) = ptr;
                SUCC_P(ptr) = bp;
                break;                    
            }
            //저장된 모든 ptr가 bp보다 커서 제일 앞에 연결시켜 저장해주는 경우
            if(SUCC_P(ptr)==heap_listp){
                PRED_P(SUCC_P(heap_listp)) = bp;
                SUCC_P(bp) = SUCC_P(heap_listp);
                SUCC_P(heap_listp) = bp;
                PRED_P(bp) = heap_listp;
            }
        }
    }
}
static void list_remove(void *bp){
    SUCC_P(PRED_P(bp)) = SUCC_P(bp);
    PRED_P(SUCC_P(bp)) = PRED_P(bp);
}
//extend_heap: 남은 가용블록들중에서 새로 들어갈 데이터의 자리가 없는 경우 heap의 크기를 늘려준다.
static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    size = (words%2) ? (words+1)*WSIZE:words*WSIZE;
    if((long)(bp=mem_sbrk(size))==-1){
        return NULL;
    }
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    return coalesce(bp);
}
//find_fit: 사이즈크기가 맞는 가용블록을 찾아간다.
static void *find_fit(size_t asize){
    void *bp;
    for (bp=SUCC_P(heap_listp);!GET_ALLOC(HDRP(bp));bp=SUCC_P(bp)){
        if(asize<=GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}
//place: 가용블록의 크기가 필요이상이라면 그 가용블럭을 조각내서 사용한다.
static void place(void *p, size_t size){
    size_t free_block = GET_SIZE(HDRP(p));//현재 할당된 크기
    list_remove(p);
    if((free_block-size)>=(2*DSIZE)){
        PUT(HDRP(p),PACK(size,1));
        PUT(FTRP(p),PACK(size,1));
        p = NEXT_BLKP(p);
        PUT(HDRP(p),PACK(free_block-size,0));
        PUT(FTRP(p),PACK(free_block-size,0));
        list_add(p);
    }else{
        PUT(HDRP(p),PACK(free_block,1));
        PUT(FTRP(p),PACK(free_block,1));
    }
}
//coalesce: free되거나 extend_heap을 하였을때 앞뒤에 가용블록이 있다면 연결해주는 함수
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && !next_alloc){
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }else if(!prev_alloc && next_alloc){
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }else if(!prev_alloc && !next_alloc){
        list_remove(PREV_BLKP(bp));
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    list_add(bp);
    return bp;
}
//////////////////// END OF HELPER FUNCTION ////////////////////


//mm_init: 프롤로그 블록, 에필로그 블록만들어 초기화시켜준다.
int mm_init(void){
    if((heap_listp = mem_sbrk(6*WSIZE))==(void*)-1){
        return -1;
    }
    PUT(heap_listp,0); //0번째 빈칸
    PUT(heap_listp+(1*WSIZE),PACK(2*DSIZE,1)); // prologue header
    PUT(heap_listp+(2*WSIZE),heap_listp+(3*WSIZE)); // predecessor
    PUT(heap_listp+(3*WSIZE),heap_listp+(2*WSIZE)); // successor
    PUT(heap_listp+(4*WSIZE),PACK(2*DSIZE,1)); // prologue footer
    PUT(heap_listp+(5*WSIZE),PACK(0,1)); // eplilogue block header
    heap_listp += (2*WSIZE);
    if (extend_heap(CHUNKSIZE/WSIZE)==NULL){
        return -1;
    }
    return 0;
}

//mm_malloc: size만큼의 가용블록을 할당시켜준다.
void *mm_malloc(size_t size){
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size==0){
        return NULL;
    }

    if(size<=DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE);
    }

    if((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        // next_p = bp;
        return bp;
    }
    extendsize = MAX(asize,CHUNKSIZE);

    if((bp=extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }
    place(bp,asize);
    return bp;
}

//mm_free: 할당된 블록을 free시켜준다.
void mm_free(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    coalesce(bp);
}

//mm_realloc: size만큼 메모리 재할당
void *mm_realloc(void *ptr, size_t size){
    void *oldptr = ptr;
    void *newptr;
    size_t copy_size;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copy_size = GET_SIZE(HDRP(oldptr));
    if (size < copy_size)
      copy_size = size;
    memcpy(newptr, oldptr, copy_size);
    mm_free(oldptr);
    return newptr;
}