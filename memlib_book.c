#include <stdio.h>
#include <stdlib.h>

extern int mm_init(void);//^extern : 외부 변수. 외부에 있는 변수를 사용하기 위한 키워드
extern void *mm_malloc (size_t size);
extern void mm_free (void *ptr); 

/*private global variables
    아래 변수들은 전역적이지만, 해당 소스 파일내에서만 사용 될 수 있다.
    다른 파일에서 접근할 수 없는 private 변수이다*/
static char *mem_heap; //^할당된 힙의 시작 주소
static char *mem_brk; //^현재 힙의 끝 또는 break 위치를 가리킴. 다음 할당이 시작 될 위치
static char *mem_max_addr; //^힙의 최대주소를 가리킴. mem_heap으로부터 MAX_HEAP만큼 떨어진 위치에 해당한다

void mem_init(void) {
    mem_heap = (char *)Malloc(MAX_HEAP); //^MAX_HEAP 크기만큼의 메모리를 할당하고 시작 주소를 mem_heap에 저장
    mem_brk = (char *)mem_heap; //^mem_brk를 힙의 시작 주소인 mem_heap으로 설정. 이는 힙이 아직 사용되지 않았음을 나타낸다.
    mem_max_addr = (char *)(mem_heap + MAX_HEAP); //^mem_max_addr을 힙의 최대 가능한 주소로 설정

}

void *mem_sbrk(int incr){  //^힙에서 메모리를 할당하거나 반환하는 역할
    char *old_brk = mem_brk;//^현재의 mem_brk 위치를 old_brk에 저장
    //^incr : 메모리 증가량
    //^요청된 메모리 증가량(incr)이 유효한지 검사한다
    if ((incr<0) || ((mem_brk + incr) > mem_max_addr)) { //^incr이 0보다 작은 경우, 또는 요청 후 mem_brk의 위치가 mem_brk_addr을 초과하는 경우, 메모리 할당에 실패했음을 나타낸다
        errno = ENOMEM; 
        fprintf(stderr, "ERROR : mem_sbrk failed. Ran out of memory...\n")
        return (void *)-1; //^메모리 할당에 실패한 경우, 에러메세지를 출력하고 -1(void포인터로 형변환)을 반환
    }
	/*void*로 형변환하는 이유는 mem_sbrk 함수의 반환 타입이 void*이기 때문. 
    함수는 성공할 경우 메모리의 시작 주소를 반환하고, 실패할 경우 -1을 반환.
    이 -1 값을 반환하기 위해 void*로 형변환하는 것.*/
    mem_brk += incr; //^mem_brk를 incr만큼 증가시켜 새로운 break위치를 설정
    return (void *)old_brk; //^이전의 mem_brk위치, 즉 old_brk를 반환. 이는 할당된 메모리 블록의 시작 주소를 나타낸다.
}