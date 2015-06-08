/* 
 * Simple, 32-bit and 64-bit clean allocator based on an explicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to 8-byte alignment. The minimum size
 * of block is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Bojun Wang",
	/* First member's full name */
	"Bojun Wang",
	/* First member's email address */
	"bw6@rice.edu",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 15)      /* Extend heap by this amount (bytes) */


#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(WSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given bp, compute address of precedent and succeeding block in list */
#define EFL_PBP(bp)  (*((void **)bp))
#define EFL_SBP(bp)  (*((void **)((char*)bp + WSIZE)))
#define SET_EFL_PBP(bp, ptr)  ((EFL_PBP(bp)) = (ptr))
#define SET_EFL_SBP(bp, ptr)  ((EFL_SBP(bp)) = (ptr))

/* Global variables: */
static char *heap_listp; /* Pointer to first block in heap */  
static void *ef_listp;  /* Pointer to first block in explicit free list */
static int extendorfree;  /* Integer flag for extend_heap and free */
static size_t lastfailedsize;  /* Last failed size of find_fit */
static int debug = 0;  /* Integer flag for debug */


/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Function prototype for printing out free list: */
static void printlist();

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 *   Initialize global flags as well as explicit free list pointer.
 */
int
mm_init(void) 
{

	extendorfree = 0;  /* no extend or free happened. */
	lastfailedsize = 0; /* no size failed. */
	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(3 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (2 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (1 * WSIZE);
	ef_listp = NULL;  /* The explicit free list has nothing. */
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap((CHUNKSIZE)/ WSIZE) == NULL)
		return (-1);
	if (debug) {
		printlist();
		checkheap(true);
	}
	
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;
	
	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignments. */
	if (size <= WSIZE)
		asize = 4 * WSIZE;
	else
		asize = WSIZE * (((size + WSIZE - 1)) / WSIZE) + DSIZE;

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		if (debug) {
			printlist();
			checkheap(true);
		}
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	bp = extend_heap(extendsize / WSIZE);
	if (bp == NULL){
		return (NULL);
	}
	place(bp, asize);
	if (debug) {
		printlist();
		checkheap(true);
	}
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	extendorfree = 1;  /* Update global flag */
	
	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
	if (debug) {
		printlist();
		checkheap(true);
	}
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" is returned. If the block
 *   is followed by a free block and the total size is larger than size,
 *   change header and footer of ptr, and return ptr.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	size_t asize;
	size_t fblk_size;
	size_t newsize;
	void* newptr;
	void* nextbp;
	void* pptr;
	void* sptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));
	/* If old size is larger than new size, */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size <= WSIZE)
		asize = 4 * WSIZE;
	else
		asize = WSIZE * (((size + WSIZE - 1)) / WSIZE) + DSIZE;
	
	if (oldsize > asize)
		return ptr;
	
	/* check if the block following ptr is free */
	if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) {
		nextbp = NEXT_BLKP(ptr);
		fblk_size = GET_SIZE(HDRP(nextbp));
		if ((newsize = (GET_SIZE(HDRP(ptr)))+fblk_size) > asize) {
			/*slice nextbp out of ef_list */
			pptr = EFL_PBP(nextbp);
			sptr = EFL_SBP(nextbp);
			if (pptr != NULL) {
				SET_EFL_SBP(pptr, sptr);
			}
			else {
				ef_listp = sptr;
			}
			if (sptr != NULL) {
				SET_EFL_PBP(sptr, pptr);
			}
			PUT(HDRP(ptr), PACK(newsize, 0x1));
			PUT(FTRP(ptr), PACK(newsize, 0x1));
			if (debug) {
				printlist();
				checkheap(true);
			}
			return ptr;
			
			
		}
		
	}
	newptr = mm_malloc(size);
	if (newptr == NULL)
		return (NULL);
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);
	mm_free(ptr);
	if (debug) {
		printlist();
		checkheap(true);
	}
	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 *   For explicit list implementation, check prev and next, then always put
 *   coalesced block pointer to the start of list
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	uintptr_t *pptr;
	uintptr_t *sptr;

	/* In case of debugging, print free list before and after coalescing*/
	if (debug) {
		printlist();
		checkheap(true);
	}
	if (prev_alloc && next_alloc) {                 /* Case 1 */
		/* no coalescing happens , just put bp to the start */
		EFL_PBP(bp) = NULL;
		EFL_SBP(bp) = ef_listp;
		if (ef_listp != NULL) {
			SET_EFL_PBP(ef_listp, bp);
		}
		ef_listp = bp;
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		/* slice out next block from list */
		pptr = EFL_PBP(NEXT_BLKP(bp));
		sptr = EFL_SBP(NEXT_BLKP(bp));
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		/* insert into heap free list. */
		SET_EFL_PBP(bp, NULL);
		SET_EFL_SBP(bp, ef_listp);
		if (ef_listp != NULL) {
			SET_EFL_PBP(ef_listp, bp);
		}
		ef_listp = bp; /* update beginning of list. */
		
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* slice out previous block from list */
		pptr = EFL_PBP(PREV_BLKP(bp));
		sptr = EFL_SBP(PREV_BLKP(bp));
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		/* insert into heap free list. */
		SET_EFL_PBP(bp, NULL);
		SET_EFL_SBP(bp, ef_listp);
		if (ef_listp != NULL) {
			SET_EFL_PBP(ef_listp, bp);
		}
		ef_listp = bp; /* update beginning of list. */
		
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		/* slice out next block from list */
		pptr = EFL_PBP(NEXT_BLKP(bp));
		sptr = EFL_SBP(NEXT_BLKP(bp));
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
		/* slice out previous block from list */
		pptr = EFL_PBP(PREV_BLKP(bp));
		sptr = EFL_SBP(PREV_BLKP(bp));
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		/* insert into heap free list and update heap_listp */
		SET_EFL_PBP(bp, NULL);
		SET_EFL_SBP(bp, ef_listp);
		if (ef_listp != NULL) {
			SET_EFL_PBP(ef_listp, bp);
		}
		ef_listp = bp;
	}
	/* In case of debugging, print free list before and after coalescing*/
	if (debug) {
		printlist();
		checkheap(true);
	}
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return the coalesced block.
 */
static void *
extend_heap(size_t words) 
{
	uintptr_t *bp;
	size_t size;
	extendorfree = 1;
	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   From the start of explicit free list, 
 *   find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	uintptr_t *bp;
	if (asize == lastfailedsize) {
		if (extendorfree == 0) {
			return NULL;
		}
	}
	/* Search for the first fit. */
	for (bp = ef_listp; bp!=NULL ; bp = EFL_SBP(bp)) {
		if (asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	
	/* No fit was found. */
	lastfailedsize = asize;
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *   and block "bp" is part of explicit free list.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size and insert the remainder to free list.
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	void **pptr;
	void **sptr;

	if ((csize - asize) >= (4 * WSIZE)) { /* splitting */
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		/* slice bp out of list */
		pptr = EFL_PBP(bp);
		sptr = EFL_SBP(bp);
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
		/* insert next block to list */
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		SET_EFL_PBP(bp, NULL);
		SET_EFL_SBP(bp, ef_listp);
		if (ef_listp != NULL) {
			SET_EFL_PBP(ef_listp, bp);
		}
		ef_listp = bp;
		
	} else { /* no splitting */
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		/* slice bp out of list */
		pptr = EFL_PBP(bp);
		sptr = EFL_SBP(bp);
		if (pptr != NULL) {
			SET_EFL_SBP(pptr, sptr);
		}
		else {
			ef_listp = sptr;
		}
		if (sptr != NULL) {
			SET_EFL_PBP(sptr, pptr);
		}
	}
}






/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Checks a block in the heap if it has size >= minimum size
 *   and if the size is multiple of 8, and if footer and header matches.
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % WSIZE)
		printf("Error: %p is not 8 bytes aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
	if (GET_SIZE(HDRP(bp)) < 4*WSIZE)
		printf("Error: block is smaller than minimum size\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Checks for every block in the heap if it has size >= minimum size
 *   and if the size is multiple of 8.
 *   It also checks the entire explicit free list to see if there
 *   are errors of existing allocated block in free list.
 */
void
checkheap(bool verbose) 
{
	void *bp;
	
	/*check explicit free list */
	for (bp = ef_listp; bp != NULL; bp = EFL_SBP(bp)) {
		if (GET_ALLOC(HDRP(bp))) {
			printf("One allocated block exists in free list\n");
			printblock(bp);
		}
	}
	
	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * Requires: Nothing.
 * 
 * Effects: Print out entire free list.
 *
 */
static void
printlist()
{
	void* bp = ef_listp;
	printf("printing free list: ");
	while (bp != NULL ) {
		printf("-->");
		printblock(bp);
		bp = EFL_SBP(bp);
	}
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
