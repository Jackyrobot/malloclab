/*
 * Name: Jacky Liu
 * Andrew id: jackyl1
 ******************************************************************************
 *                               mm-baseline.c                                *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_mask = 0x2;

static const word_t size_mask = ~(word_t)0xF;

typedef struct dll node;

struct dll {
    size_t size;
    node *next;
    node *prev;
};

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown

     */
    union {
        char payload[0];
        struct list {
            struct block *next;
            struct block *prev;
        } list_t;
    };
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool footer_bit);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc, bool footer_bit);
static void write_footer(block_t *block, size_t size, bool alloc, bool footer_bit);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static word_t get_footer(block_t *block);

static block_t *last_block = NULL;

static block_t *first_free = NULL; //assign it when you get your first free block.
// Then keep assigning and chaining it

bool in_list(block_t *block) {
    block_t *start;
    for(start = first_free; start != NULL; start=start->list_t.next) {
        if(start == block) return true;
    }
    return false;
}

// Inserts to front
void insert_node(block_t *block) {
    dbg_printf("Inserting block %p\n", block);
    dbg_requires(!get_alloc(block));
    dbg_requires(!in_list(block));
    if(first_free != NULL) { // Not empty
        block_t *temp = first_free;
        first_free = block;
        block->list_t.next = temp;
        temp->list_t.prev = block;
        block->list_t.prev = NULL;
    }
    else { // Empty list
        first_free = block;
        block->list_t.next = NULL;
        block->list_t.prev = NULL;
    }
    dbg_ensures(in_list(block));
    dbg_printf("Done inserting %p\n", block);
    return; //return block;
}

block_t delete_node(block_t *block) {
    dbg_printf("Deleting block %p\n", block);
    dbg_requires(mm_checkheap(__LINE__));
    dbg_requires(in_list(block));
    // Case 1: first node
    if (block->list_t.prev == NULL && block->list_t.next != NULL) {
        dbg_printf("First node\n");
        first_free = block->list_t.next;
        block->list_t.next->list_t.prev = NULL;
        block->list_t.next = NULL;

    }
    //Case 2: end node
    else if (block->list_t.next == NULL && block->list_t.prev != NULL) {
        dbg_printf("End node\n");
        block->list_t.prev->list_t.next = NULL;
        block->list_t.prev = NULL;
    }
    //Case 3: middle node
    else if (block->list_t.next != NULL && block->list_t.prev != NULL) {
        dbg_printf("Middle node\n");

        block_t *left_node = block->list_t.prev;
        block_t *right_node = block->list_t.next;
        left_node->list_t.next = right_node;
        right_node->list_t.prev = left_node;
        block->list_t.next = NULL;
        block->list_t.prev = NULL;
        dbg_assert(in_list(left_node));
        dbg_assert(in_list(right_node));
    }
    // Case 4: empty list
    else {
        dbg_printf("Empty list\n");
        block->list_t.next = NULL;
        block->list_t.prev = NULL;
        first_free = NULL;
    }
    dbg_ensures(mm_checkheap(__LINE__));
    dbg_ensures(!in_list(block));
    dbg_printf("Done deleting\n");
    return *block;
}

/*
 * <what does mm_init do?>
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    first_free = NULL;
    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, false); // Prologue footer
    start[1] = pack(0, true, false); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    last_block = heap_start;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 */
void *malloc(size_t size)
{
    dbg_printf("Entering malloc size = %zu\n", size);
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(max(size + wsize, min_block_size), dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    dbg_printf("malloc returning %p\n", block);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 * <what does free do?>
 */
void free(void *bp)
{
    dbg_printf("Entering free\n");
    if (bp == NULL)
    {
        return;
    }


    block_t *block = payload_to_header(bp);
    dbg_printf("free(%p)\n", block);
    size_t size = get_size(block);

    write_header(block, size, false, get_prev_alloc(block));
    write_footer(block, size, false, get_prev_alloc(block));
    block_t *block_next = find_next(block);
    bool alloc_next = get_alloc(block_next);

    dbg_printf("%p alloc_next = %d\n", block_next, alloc_next);
    write_header(block_next, get_size(block_next), alloc_next, false);
    if(!alloc_next) write_footer(block_next, get_size(block_next), alloc_next, false);

    dbg_printf("header = %zu footer = %zu\n", block_next->header, get_footer(block_next));
    insert_node(block);
    dbg_printf("header = %zu footer = %zu\n", block_next->header, get_footer(block_next));
    coalesce(block);
    dbg_printf("done freeing\n");
}

/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
    if(ptr == NULL) return NULL;
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 */
static block_t *extend_heap(size_t size)
{
    dbg_printf("Entering extend_heap...\n");
    dbg_requires(mm_checkheap(__LINE__));
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    if(bp == NULL) return NULL;
    block_t *block = payload_to_header(bp);
    bool last_alloc = get_alloc(last_block);
    dbg_printf("last_block = %p last_alloc = %d\n", last_block, last_alloc);
    write_header(block, size, false, last_alloc);
    write_footer(block, size, false, last_alloc);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false);

    // Coalesce in case the previous block was free
    insert_node(block);
    dbg_assert(in_list(block));
    last_block = coalesce(block);
    dbg_ensures(mm_checkheap(__LINE__));
    return last_block;
}

/*
 * <what does coalesce do?>
 */
static block_t *coalesce(block_t * block)
{
    dbg_requires(in_list(block));
    block_t *block_next = find_next(block);
    block_t *block_prev = NULL;

    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
    if (!prev_alloc) {
        block_prev = find_prev(block);
    }
    dbg_printf("prev = %p block = %p next = %p\n", block_prev, block, block_next);


    if (prev_alloc && next_alloc)              // Case 1
    {
        dbg_printf("Case 1\n");
        // insert_node(block);
        dbg_requires(mm_checkheap(__LINE__));

        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        dbg_printf("Case 2\n");
        if(block_next == last_block) {
            last_block = block;
        }
        delete_node(block_next);
        delete_node(block);
        size += get_size(block_next);
        write_header(block, size, false, true);
        write_footer(block, size, false, true);
        insert_node(block);
        dbg_printf("Joined %p and %p\n", block, block_next);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        dbg_printf("Case 3\n");
        dbg_printf("block_prev %p block %p\n", block_prev, block);
        if(block == last_block) {
            last_block = block_prev;
        }
        // block = block_prev;

        dbg_requires(in_list(block));
        delete_node(block_prev);
        dbg_requires(in_list(block));
        delete_node(block);
        // block = block_next;
        size += get_size(block_prev);
        write_header(block_prev, size, false, get_prev_alloc(block_prev));
        write_footer(block_prev, size, false, get_prev_alloc(block_prev));

        dbg_printf("Joined %p and %p\n", block_prev, block);
        block = block_prev;
        insert_node(block);

    }

    else   // !prev_alloc && !next_alloc          // Case 4
    {
        dbg_printf("Case 4\n");
        if(block == last_block || block_next == last_block) {
            last_block = block_prev;
        }

        delete_node(block_next);
        delete_node(block_prev);
        delete_node(block);
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false, get_prev_alloc(block_prev));
        write_footer(block_prev, size, false, get_prev_alloc(block_prev));
        insert_node(block_prev);
        dbg_printf("Joined %p and %p and %p\n", block_prev, block, block_next);
        block = block_prev;
    }
    dbg_requires(mm_checkheap(__LINE__));
    return block;
}

/*
 * <what does place do?>
 */
static void place(block_t *block, size_t asize)
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t csize = get_size(block);

    if ((csize - asize) >= min_block_size)
    {
        dbg_printf("splitting = %p\n", block);
        delete_node(block);
        block_t *block_next;
        write_header(block, asize, true, get_prev_alloc(block));
        write_footer(block, asize, true, get_prev_alloc(block));

        block_next = find_next(block);
        write_header(block_next, csize-asize, false, true);
        write_footer(block_next, csize-asize, false, true);
        insert_node(block_next);
        if(block == last_block) {
            last_block = block_next;
        }


    }

    else
    {
        delete_node(block);
        write_header(block, csize, true, get_prev_alloc(block));
        write_footer(block, csize, true, get_prev_alloc(block));
        block_t *block_next = find_next(block);
        write_header(block_next, get_size(block_next), true, true);
        dbg_printf("not splitted = %p\n", block);
    }
    dbg_requires(mm_checkheap(__LINE__));

}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    block_t *attemptBlock = NULL;
    int limit = 0;

    block = first_free;
    while (block != NULL) {
        //printf("%p\n", block);

        if ( !(get_alloc(block)) && (asize <= get_size(block)))
        {
            limit ++;
            if(limit >= 7) break;
            if(attemptBlock == NULL || get_size(block) < get_size(attemptBlock)){
                attemptBlock = block;
            }
        }
        block = block->list_t.next;
    }

    return attemptBlock;
}

// Somewhere in between first fit and best fit?
// static block_t *find_fit(size_t asize)
// {
//     block_t *block;
//     // Finds a block that is no larger than 3 size greater than asize.
//     for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
//         if( !(get_alloc(block)) && get_size(block)-asize <= 3) {
//             return block;
//         }
//     }
//     // Else, just use first fit.
//     for (block = heap_start; get_size(block) > 0; block = find_next(block))
//     {

//         if ( !(get_alloc(block)) && (asize <= get_size(block)))
//         {
//             return block;
//         }
//     }
//     return NULL; //no fit found
// }

/*
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    /* you will need to write the heap checker yourself. As a filler:
     * one guacamole is equal to 6.02214086 x 10**23 guacas.
     * one might even call it
     * the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap,
     * do you eat it with a pair of chopsticks, or with a spoon?
     * (Delete these lines!)
     */

    (void)line; // delete this line; it's a placeholder so that the compiler
                // will not warn you about an unused variable.

    block_t *block;
    if(first_free != NULL) {
        for(block = first_free; block!=NULL&&get_size(block) > 0; block = block->list_t.next) {
            // Check if it is a valid doubly linked list
            if(block->list_t.next != NULL) {
                if(block->list_t.next->list_t.prev != block) {
                    dbg_printf("Not valid dll\nblock = %p next = %p next.prev = %p\n",
                            block, block->list_t.next, block->list_t.next->list_t.prev);
                    return false;
                }
            }
            if(block->list_t.prev != NULL) {
                if(block->list_t.prev->list_t.next != block) {
                    dbg_printf("Not valid dll\nblock = %p prev = %p prev.next = %p\n",
                            block, block->list_t.prev, block->list_t.prev->list_t.next);
                    return false;
                }
            }
            // Check if every block is free
            if(get_alloc(block)) {
                dbg_printf("Not every block is free\n");
                return false;
            }
            //Header and footer match
            word_t *footerp = (word_t *)((block->payload) + get_payload_size(block) - wsize);
            if(block->header != *footerp) {
                dbg_printf("header (%zu) and footer (%zu) not matched\n",
                            block->header, *footerp);
                return false;
            }
            if((unsigned long)block->payload % wsize != 0) {
                dbg_printf("not aligned\n");
                return false;
            }
            //Contiguous free blocks
            // if(get_alloc(block->list_t.prev) || get_alloc(block->list_t.next)) {
            //     return false;
            // }
            // block = start->next;
        }
    }

    block_t *block2;
    block_t *prev_block = NULL;
    if(heap_start == NULL) return false;
    for(block2 = heap_start; block2!=NULL && get_size(block2) > 0; block2 = find_next(block2)) {
        //contingency
        /*if(get_alloc(block2)) {
            if(block2->list_t.next != NULL && get_alloc(block2->list_t.next)) {
                return false;
            }
        }
        if(!get_alloc(block2)) {
            if(block2->list_t.next != NULL && !get_alloc(block2->list_t.next)) {
                return false;
            }
        }*/
        //check bits
        if(prev_block != NULL && get_alloc(prev_block) != get_prev_alloc(block2)) {
            dbg_printf("%p bit (%d) does not match alloc of %p (%d)\n",
                block2, get_prev_alloc(block2), prev_block, get_alloc(prev_block));
            return false;
        }
        prev_block = block2;

    }
    return true;


}


/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad be ef 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */


/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool footer_bit)
{
    // int result = 0;
    if(alloc) {
        size = size | alloc_mask;
    }
    if(footer_bit) {
        size = size | prev_mask;
    }
    return size;

    // return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

static bool get_prev_alloc(block_t *block)
{
    return block->header & prev_mask;
    // return extract_alloc(block->list_t.prev->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc, bool footer_bit)
{
    block->header = pack(size, alloc, footer_bit);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc, bool footer_bit)
{
    word_t *footerp = (word_t *)((block->payload) + get_payload_size(block) - wsize);
    *footerp = pack(size, alloc, footer_bit);
}

static word_t get_footer(block_t *block) {
    word_t *footerp = (word_t *)((block->payload) + get_payload_size(block) - wsize);
    return *footerp;
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    dbg_requires(!get_prev_alloc(block));

    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}
