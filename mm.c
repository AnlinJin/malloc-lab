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
	"ateam",
	/* First member's full name */
	"Harry Bovik",
	/* First member's email address */
	"bovik@cs.cmu.edu",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define NUMBER_OF_LISTS 13

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define PACK(size, alloc) ((size) | (alloc)) // 0 if free, 1 if allocated

#define GET(p) (*(unsigned int *)(p))						 // get an unsigned int value given a location
#define SET(p, val) (*(unsigned int *)(p) = (val))			 // set an unsigned int value to a given location
#define SET_POINTER(p, newp) (*(p) = ((unsigned int *)newp)) // set the next and prev pointer for each chunk

#define GET_SIZE(p) (GET(p) & ~0x7) //get the size of the chunk given the address of the header or footer
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HEADERP(bp) ((char *)(bp)-WSIZE - 2 * DSIZE)
#define FOOTERP(bp) ((char *)(bp) + GET_SIZE(HEADERP(bp)) - 2 * WSIZE - 2 * DSIZE) // calculate footer based on header
#define PREVFOOTER(bp) ((char *)(bp)-3 * DSIZE)
//different pointer arithmetic for allocated chunk since it does not have pointers
#define HEADERPALLOCATED(bp) ((char *)(bp)-WSIZE)
#define FOOTERPALLOCATED(bp) ((char *)(bp) + GET_SIZE(HEADERPALLOCATED(bp)) - 2 * WSIZE)

//get prev and next node in the linked list
#define GETNEXT(bp) ((unsigned int **)((char *)(bp)-2 * DSIZE))
#define GETPREV(bp) ((unsigned int **)((char *)(bp)-DSIZE))

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HEADERP(bp))) //assume all the chunks have the next and prev pointer
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-3 * DSIZE))

#define PREV_BLKP_ALLOCATED(bp) (((char *)(bp)-GET_SIZE((char *)(bp)-3 * DSIZE) - 2 * DSIZE))
#define NEXT_BLKP_ALLOCATED(bp) (((char *)(bp) + GET_SIZE(HEADERP(bp))) - 2 * DSIZE)

#define CHANGE_BKP_TO_FREEBKP(bp) ((char *)(bp) + 2 * DSIZE)

#define MAX(a, b) (a >= b ? a : b)

/*Block layout:
*		Allocated block:
*
*			[Header: <size><1>]
* 			[Payload...]
			[Footer: <size><1>]
*
*		Free block:
*
*			[Header: <size><0>]
*			[4-byte pointer to next block in the segregated list]
*			[4-byte pointer to previous block in the segregated list]	
*			[Footer: <size><0>]*/


//#define DEBUG
//#define DEBUG2
//#define DEBUG3

void *segregated_list[NUMBER_OF_LISTS];
static char *heap_listp;

void *find_fit(size_t asize);
static void *extend_heap(size_t words);
void place(void *bp, size_t asize);
static void *coalesce(void *bp);
void insert_list(void *bp, size_t size);
int getIndex(unsigned long size);
void deleteNodeFromList(void *bp);
//check function
int mm_check(void);
void printHeap();
int check1();
int check2();
int check3();
int checkPointerConsistency();
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	
	for (int i = 0; i < NUMBER_OF_LISTS; i++)
	{
		segregated_list[i] = NULL;
	}
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;
	SET(heap_listp, 0);
	SET(heap_listp + WSIZE, PACK(DSIZE, 1));
	//SET_POINTER((unsigned int **)(heap_listp + DSIZE), NULL);
	//SET_POINTER((unsigned int **)(heap_listp + 2 * DSIZE), NULL);
	SET(heap_listp + DSIZE, PACK(DSIZE, 1));
	SET(heap_listp + 3 * WSIZE, PACK(0, 1));
	heap_listp += 2 * WSIZE; //point to the first block
	if (extend_heap(4 * DSIZE / WSIZE) == NULL)
		return -1;

#ifdef DEBUG
	mm_check();
#endif
	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	/*#ifdef DEBUG
		mm_check();
	#endif*/
	size_t asize;
	size_t extendSize;
	char *bp;

	if (size == 0)
		return NULL;
	if (size <= DSIZE)
		asize = 4 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);
	if ((bp = find_fit(asize)) != NULL)
	{
		place(bp, asize);
#ifdef DEBUG
		//printf("allocated %p\n", bp - 2 * DSIZE);
		mm_check();
#endif
		return bp - 2 * DSIZE;
	}
	/*int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }*/
	extendSize = MAX(asize, CHUNKSIZE);
	if ((bp = (char *)extend_heap(extendSize / WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
#ifdef DEBUG
	//printf("allocated %p and heap is extended\n", bp - 2 * DSIZE);
	mm_check();
#endif
	return bp - 2 * DSIZE;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	/*#ifdef DEBUG
		printf("free %ptr\n",ptr);
		mm_check();
	#endif*/
	size_t size = GET_SIZE(HEADERPALLOCATED(ptr));

#ifdef DEBUG3
	if (size == 27832 && ptr == (void *)(0xf73814f8))
		mm_check();
#endif
	SET(HEADERPALLOCATED(ptr), PACK(size, 0));
	SET(FOOTERPALLOCATED(ptr), PACK(size, 0));
	ptr = ptr + 2 * DSIZE;
	//SET_POINTER(GETPREV(ptr), NULL);
	//SET_POINTER(GETNEXT(ptr), NULL);
	coalesce(ptr);

#ifdef DEBUG2
	if (size == 1832)
		printHeap();
#endif
#ifdef DEBUG
	//printf("free %ptr\n",ptr);
	mm_check();
#endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	if (ptr == NULL)
		return mm_malloc(size);
	else if (size == 0)
	{
		free(ptr);
		return NULL;
	}
	else
	{
		/*size_t asize;
		if (size == 0)
			return NULL;
		if (size <= DSIZE)
			asize = 2 * DSIZE;
		else
			asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);
		size_t old_chunk_size = GET_SIZE(HEADERPALLOCATED(ptr));
		char *nextheader = (char *)ptr + old_chunk_size;
		if (GET_ALLOC(nextheader) == 0 && (GET_SIZE(nextheader) + old_chunk_size) > asize)
		{
			place(CHANGE_BKP_TO_FREEBKP(ptr), asize);
			return ptr;
		}
		else*/
		//{
		void *oldptr = ptr;
		void *newptr;
		size_t copySize;

		newptr = mm_malloc(size);
		if (newptr == NULL)
			return NULL;
		copySize = GET_SIZE(HEADERPALLOCATED(oldptr));
		if (size < copySize)
			copySize = size;
		memcpy(newptr, oldptr, copySize);
		mm_free(oldptr);
		return newptr;

		//}
	}
}
//get a new chunk of memory and call the coalesce
//the bp
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	size = words % 2 ? (WSIZE + 1) * words : WSIZE * words;
	if ((bp = (char *)mem_sbrk(size)) == (void *)(-1))
		return NULL;
	bp = bp + 2 * DSIZE;
	SET(HEADERP(bp), PACK(size, 0));
	SET(FOOTERP(bp), PACK(size, 0));
	SET_POINTER(GETNEXT(bp), NULL);
	SET_POINTER(GETPREV(bp), NULL);

	SET(HEADERP(NEXT_BLKP(bp)), PACK(0, 1));

	//we assume that the bp is pointing a free block
	return coalesce(bp);
}

void *find_fit(size_t asize)
{
	int index = getIndex(asize);
	void *bp;
	for (int j = index; j < NUMBER_OF_LISTS; j++)
	{
		bp = segregated_list[j];
		if (bp != NULL)
		{
			unsigned int **next = (unsigned int **)GETNEXT(bp);
			while (next != NULL && bp != NULL)
			{
				size_t csize = GET_SIZE(HEADERP(bp));
				if (csize >= asize)
					return bp;
				else
				{
					bp = *next;
					next = (unsigned int **)GETNEXT(bp);
				}
			}
		}
	}
	return NULL;
}

//change the head and footer of the allocated chunk
void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HEADERP(bp));
	//void *nextbp, *prevbp; //previous and next chunks in the linked list
	//void * nextadjbp;

	deleteNodeFromList(bp);
	//if the allocated chunk is greater than the demand, we divide it into two parts
	//The available chunk has to be at least 32 bytes long
	//since many of the function is assuming the input is at least 32 bytes
	if (csize - asize >= 4 * DSIZE)
	{
		SET(HEADERP(bp), PACK(asize, 1));
		SET(FOOTERP(bp), PACK(asize, 1));
		//in case the size of the chunk that bp is pointing has been changed by extend or coalesce
		//deleteNodeFromList(bp);
		//next bp is free and has pointers
		bp = NEXT_BLKP(bp);
		SET(HEADERP(bp), PACK(csize - asize, 0));
		SET(FOOTERP(bp), PACK(csize - asize, 0));
		insert_list(bp, csize - asize);
	}
	else
	{
		SET(HEADERP(bp), PACK(csize, 1));
		SET(FOOTERP(bp), PACK(csize, 1));
	}

	/*
	// reset the next pointer of the last chunk and the previous pointer of the next chunk
	nextbp = *GETNEXT(bp);
	prevbp = *GETPREV(bp);
	//nextadjbp = NEXT_BLKP(bp);
	if (prevbp != NULL)
		SET_POINTER(GETNEXT(prevbp), nextbp);
	if (nextbp != NULL)
		SET_POINTER(GETPREV(nextbp), prevbp);
	//reset the current pointer to zero
	SET_POINTER(GETPREV(bp), NULL);
	SET_POINTER(GETNEXT(bp), NULL);*/
}

// insert current node into segregated list and set the next and prev pointer for the current chunk
// input bp contains pointers which are initialized in this function
void insert_list(void *bp, size_t size)
{
	int index = getIndex(size);

	unsigned int *head = segregated_list[index];
	unsigned int *node = head;
	int match = 0;
	while (node != NULL)
	{
		if (node == (unsigned int *)bp)
		{
			match = 1;
			break;
		}
		node = *GETNEXT(node);
	}
	if (match == 0)
	{
		if (head == NULL)
		{
			segregated_list[index] = (unsigned int *)bp;
			SET_POINTER(GETPREV(bp), NULL);
			SET_POINTER(GETNEXT(bp), NULL);

			//unsigned int *prevbp = *GETPREV(bp);
			//return;
		}
		else
		{
			SET_POINTER(GETPREV(bp), NULL);
			SET_POINTER(GETNEXT(bp), head);

			SET_POINTER(GETPREV(head), bp);
			segregated_list[index] = (unsigned int *)bp;
		}
	}
}

//input bp has pointers
static void *coalesce(void *bp)
{
	void *nextbp, *prevbp;
	size_t prev_alloc = GET_ALLOC(PREVFOOTER(bp));
	size_t next_alloc = GET_ALLOC(HEADERP(NEXT_BLKP(bp)));
	if (prev_alloc)
		prevbp = PREV_BLKP_ALLOCATED(bp);
	else
	{
		prevbp = PREV_BLKP(bp);
	}
	if (next_alloc)
		nextbp = NEXT_BLKP_ALLOCATED(bp);
	else
	{
		nextbp = NEXT_BLKP(bp);
	}

	size_t size = GET_SIZE(HEADERP(bp));

	if (prev_alloc && next_alloc)
	{ /* Case 1 */
		insert_list(bp, size);
		return bp;
	}
	else if (prev_alloc && !next_alloc)
	{ /* Case 2 */
		deleteNodeFromList(nextbp);
		size += GET_SIZE(HEADERP(NEXT_BLKP(bp)));
		SET(HEADERP(bp), PACK(size, 0));
		SET(FOOTERP(bp), PACK(size, 0));
		insert_list(bp, size);
	}
	else if (!prev_alloc && next_alloc)
	{ /* Case 3 */
		size += GET_SIZE(HEADERP(PREV_BLKP(bp)));
		//!!we must delete the node from the list before its size is changing since the
		// delete function will depend on the size to find the right size class
		//delete the old node before inserting a new node
		deleteNodeFromList(prevbp);
		SET(FOOTERP(bp), PACK(size, 0));
		SET(HEADERP(prevbp), PACK(size, 0));
		bp = PREV_BLKP(bp);

		insert_list(bp, size);
	}
	else
	{ /* Case 4 */
		size += GET_SIZE(HEADERP(PREV_BLKP(bp))) +
				GET_SIZE(FOOTERP(NEXT_BLKP(bp)));
		deleteNodeFromList(prevbp);
		deleteNodeFromList(nextbp);
		SET(HEADERP(PREV_BLKP(bp)), PACK(size, 0));
		SET(FOOTERP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		insert_list(bp, size);
	}
	return bp;
}

//input is adjusted size
int getIndex(unsigned long size)
{
	int index;
	if (size < 64)
	{
		index = 0;
		return index;
	}
	else if(size > (1 << (NUMBER_OF_LISTS + 4))) {
		return NUMBER_OF_LISTS - 1;
	}
	else
	{
		for (index = 1; index < NUMBER_OF_LISTS; index++)
		{
			if (size <= (1 << (index + 5)))
				return index;
		}
		
	}
	return -1;
}

//reset the pointer of current chunk and the previous and next node
//input has pointers
void deleteNodeFromList(void *bp)
{
	
	unsigned int *nextbp = *GETNEXT(bp);
	unsigned int *prevbp = *GETPREV(bp);
	#ifdef DEBUG3
		mm_check();
		printHeap();
	#endif
	size_t size = GET_SIZE(HEADERP(bp));
	int index = getIndex(size);
	unsigned int *node = segregated_list[index];
	int match = 0;
	while (node != NULL)
	{
		if (node == (unsigned int *)bp)
		{
			match = 1;
			break;
		}
		node = *GETNEXT(node);
	}
	if (match == 1)
	{
		if (prevbp == NULL)
		{
			//bp is the head
			if (nextbp == NULL)
			{
				segregated_list[index] = NULL;
			}
			else
			{
				segregated_list[index] = nextbp;
				SET_POINTER(GETNEXT(bp), NULL);
				SET_POINTER(GETPREV(nextbp), NULL);
			}
		}
		else if (nextbp == NULL)
		{
			SET_POINTER(GETPREV(bp), NULL);
			SET_POINTER(GETNEXT(prevbp), NULL);
		}
		else
		{
			#ifdef DEBUG3
				unsigned int * next_of_prev1 = *GETNEXT(prevbp);
				unsigned int * prev_of_next1 = *GETPREV(nextbp);
			#endif
			SET_POINTER(GETPREV(bp), NULL);
			SET_POINTER(GETNEXT(bp), NULL);
			SET_POINTER(GETPREV(nextbp), prevbp);
			SET_POINTER(GETNEXT(prevbp), nextbp);
			#ifdef DEBUG3
				unsigned int * prev_of_next = *GETPREV(nextbp);
				unsigned int * next_of_prev = *GETNEXT(prevbp);
				mm_check();
			#endif 
		}
	}

}

int mm_check(void)
{
	//Is every block in the free list marked as free?
	/*if(!check1()) {
		return 0;
	}*/
	/*if(!check2()) {
		return 0;
	}*/
	/*if(!check3()) {
		return 0;
	}*/
	//Are there any contiguous free blocks that somehow escaped coalescing?
	//check2()
	//Is every free block actually in the free list?
	//check3();
	if(!checkPointerConsistency()) {
		return 0;
	}
	return 1;
}

int checkPointerConsistency()
{
	for (int i = 0; i < NUMBER_OF_LISTS; i++)
	{
		unsigned int *node = segregated_list[i];
		unsigned int * next, *prev_of_next;
		while (node != NULL)
		{
			next = *GETNEXT(node);
			if(next != NULL) {
				prev_of_next = *GETPREV(next);
				if(node != prev_of_next) {
					printf("Pointer inconsistency\n");
					printHeap();
					return 0;
				}
			}
			node = next;
		}
	}
	return 1;
}
//Is every block in the free list marked as free?
int check1()
{
	for (int i = 0; i < NUMBER_OF_LISTS; i++)
	{
		unsigned int *node = segregated_list[i];
		while (node != NULL)
		{
			if (GET_ALLOC(HEADERP(node)))
			{
				printf("Not every block in the free list marked as free\n");
				printHeap();
				return 0;
			}
			node = *GETNEXT(node);
		}
	}
	return 1;
}
//Are there any contiguous free blocks that somehow escaped coalescing?
int check2()
{
	char *nextheader = heap_listp + WSIZE;
	int i = 1;
	char *bp;
	while (GET_SIZE(nextheader) != 0)
	{
		if (GET_ALLOC(nextheader))
			bp = nextheader + WSIZE;
		else
		{
			bp = nextheader + WSIZE + 2 * DSIZE;
			if (!GET_ALLOC(PREVFOOTER(bp)) || !GET_ALLOC(nextheader + GET_SIZE(nextheader)))
			{
				printf("There exists contiguous free block that somehow escaped coalescing\n");
				printHeap();
				return 0;
			}
			
		}
		nextheader += GET_SIZE(nextheader);
		i++;
	}
	return 1;
}
//Is every free block actually in the free list?
int check3()
{
	char *nextheader = heap_listp + WSIZE;
	int i = 1;
	char *bp;
	while (GET_SIZE(nextheader) != 0)
	{
		if (!GET_ALLOC(nextheader))

		{
			bp = nextheader + WSIZE + 2 * DSIZE;
			int k = getIndex(GET_SIZE(nextheader));
			unsigned int *node = segregated_list[k];
			char match = 0;
			while (node != NULL)
			{
				if (node == (unsigned int *)bp)
				{
					match = 1;
					break;
				}
				node = *GETNEXT(node);
			}
			if (match == 0)
			{
				printf("Not every free block is actually in the free list\n");
				printf("chunk %d: address:%p, size:%d, allocated:%d should be in size class %d\n", i, bp, GET_SIZE(nextheader), GET_ALLOC(nextheader), k);
				printHeap();
				//return 0;
			}
		}
		nextheader += GET_SIZE(nextheader);
		i++;
	}
	return 1;
}
void printHeap()
{
	//return the current information of each chunk
	/*printf("Prologue: address:%p, size:%d, allocated:%d\n", heap_listp, GET_SIZE(HEADERPALLOCATED(heap_listp)), GET_ALLOC(HEADERPALLOCATED(heap_listp)));
	char *nextheader = heap_listp + WSIZE;
	int i = 1;
	char *bp;
	while (GET_SIZE(nextheader) != 0)
	{
		if (GET_ALLOC(nextheader))
			bp = nextheader + WSIZE;
		else
		{
			bp = nextheader + WSIZE + 2 * DSIZE;
		}

		printf("chunk %d: address:%p, size:%d, allocated:%d\n", i, bp, GET_SIZE(nextheader), GET_ALLOC(nextheader));
		nextheader += GET_SIZE(nextheader);
		i++;
	}
	printf("epilogue: address:%p, size:%d, allocated:%d\n", nextheader + WSIZE, GET_SIZE(nextheader), GET_ALLOC(nextheader));*/

	printf("\nSegregated list information");
	for (int i = 0; i < NUMBER_OF_LISTS; i++)
	{
		unsigned int *node = segregated_list[i];
		if (node != NULL)
			printf("\nSize class: %d address:", i);
		while (node != NULL)
		{
			printf("%p ", node);
			node = *GETNEXT(node);
		}
	}
	printf("\n");
	printf("......\n");
}

