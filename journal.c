#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <time.h>
#include <assert.h>

#define FS_MAGIC 0x56534653U
#define JOURNAL_MAGIC 0x4A524E4CU // in ASCII, means JRNL

// from mkfs.c
#define BLOCK_SIZE        4096U
#define INODE_SIZE         128U
#define JOURNAL_BLOCK_IDX    1U
#define JOURNAL_BLOCKS      16U
#define INODE_BLOCKS         2U
#define DATA_BLOCKS         64U
#define INODE_BMAP_IDX     (JOURNAL_BLOCK_IDX + JOURNAL_BLOCKS)
#define DATA_BMAP_IDX      (INODE_BMAP_IDX + 1U)
#define INODE_START_IDX    (DATA_BMAP_IDX + 1U)
#define DATA_START_IDX     (INODE_START_IDX + INODE_BLOCKS)
#define TOTAL_BLOCKS       (DATA_START_IDX + DATA_BLOCKS)

#define REC_DATA 0xD001    // Record type for data blocks
#define REC_COMMIT 0xC002  // Record type for commit marker

#define NAME_LEN 28         // Max filename length
#define DIRECT_POINTERS 8   // Num of direct block pointers
#define INODES_PER_BLOCK (BLOCK_SIZE / INODE_SIZE) // How many inodes fit in one block
#define TOTAL_INODES (INODES_PER_BLOCK * INODE_BLOCKS) // Total inodes in file system
#define DEFAULT_IMAGE "vsfs.img"

struct superblock {
    uint32_t magic;
    uint32_t block_size;
    uint32_t total_blocks;
    uint32_t inode_count;

    uint32_t journal_block;
    uint32_t inode_bitmap;
    uint32_t data_bitmap;
    uint32_t inode_start;
    uint32_t data_start;

    uint8_t  _pad[128 - 9 * 4];
};

struct inode {
    uint16_t type;
    uint16_t links;
    uint32_t size;

    uint32_t direct[8];

    uint32_t ctime;
    uint32_t mtime;

    uint8_t _pad[128 - (2 + 2 + 4 + 8 * 4 + 4 + 4)];
};

struct dirent {
    uint32_t inode;
    char name[28];
};

// Journal Structures

struct journal_header {
    uint32_t magic;         // Magic num "JRNL" #0x4A524E4C
    uint32_t nbytes_used;   // How many bytes in journal are currently used
};

struct rec_header {
    uint16_t type;          // Record type: REC_DATA or REC_COMMIT
    uint16_t size;          // Total size of this record in bytes
};

struct data_record {
    struct rec_header hdr;    // Record header (type=REC_DATA)
    uint32_t block_no;        // target block number in filesystem
    uint8_t data[BLOCK_SIZE]; // Full 4096 byte block image
};

struct commit_record {
    struct rec_header hdr;   // Record header (type = REC_COMMIT)
};

// Thorwing errors in compile time
_Static_assert(sizeof(struct superblock) == 128, "superblock must be 128 bytes");
_Static_assert(sizeof(struct inode) == 128, "inode must be 128 bytes");
_Static_assert(sizeof(struct dirent) == 32, "dirent must be 32 bytes");
_Static_assert(sizeof(struct journal_header) == 8, "journal header must be 8 bytes");
_Static_assert(sizeof(struct data_record) == sizeof(struct rec_header) + 4 + BLOCK_SIZE, "data record size mismatch");
_Static_assert(sizeof(struct commit_record) == sizeof(struct rec_header), "commit record size mismatch");

// Global var
static int fd = -1;                         // File descriptor
static struct superblock sb;                // Superblock read from disk
static uint8_t block_buffer[BLOCK_SIZE];    // Resuable buffer for block operations

// Helper Functions

static void die(const char *msg) {
    perror(msg);
    if (fd >= 0) close(fd);
    exit(EXIT_FAILURE);
}

// To read a block from a disk into buf
static void read_block(uint32_t block_no, void *buf) {
    // calculate byte offset: block number * block size
    off_t offset = (off_t)block_no * BLOCK_SIZE;

    // Moving file pointer to that specific offset
    if (lseek(fd, offset, SEEK_SET) != offset) {
        die("lseek");
    }

    // Reading exactly one block of 4096 bytes
    ssize_t n = read(fd, buf, BLOCK_SIZE);
    if (n != (ssize_t)BLOCK_SIZE) {
        die("read");                            // Error if it can't read full disk
    }
}

// To write a block from a disk into buf
static void write_block(uint32_t block_no, const void *buf){
    // Calculate byte offset (same as before)
    off_t offset = (off_t)block_no * BLOCK_SIZE;

    // Moving file pointer to that specific offset (again same)
    if (lseek(fd, offset, SEEK_SET) != offset) {
        die("lseek");
    }

    // Now writing exactly one block
    ssize_t n = write(fd, buf, BLOCK_SIZE);
    if (n != (ssize_t)BLOCK_SIZE) {
        die("write");
    }
}

// Read and validate superblock
static void read_superblock(void){
    read_block(0, &sb);             // superblock is always at block 0

    // Checking magic number to be sur ethat it is a valid VSFS
    if (sb.magic != FS_MAGIC) {
        fprintf(stderr, "ERROR: Not a valid VSFS fs\n");
        exit(EXIT_FAILURE);
    }
}

// Testing if a specific bit is set in a bitmap
static int test_bitmap(const uint8_t *bitmap, uint32_t index) {
    return (bitmap[index / 8] >> (index % 8)) & 1;
}

// Set a specific bit in a bitmap to mark it as USED
static void mark_bitmap(uint8_t *bitmap, uint32_t index){
    // OR operation with bit mask to set the bit
    bitmap[index / 8] |= (uint8_t)(1U << (index % 8));
}

// Clear a specific bit in a bitmap to mark it as FREE
static void clear_bitmap(uint8_t *bitmap, uint32_t index){
    // AND operation with inverted bit mask to clear the bit
    bitmap[index / 8] &= (uint8_t)~(1U << (index % 8));
}

// Find first free inode in the inode bitmap
static uint32_t find_free_inode(const uint8_t *inode_bitmap){
    // Looping through all the inodes
    for (uint32_t i = 0; i < sb.inode_count; i++){
        if (!test_bitmap(inode_bitmap, i)) {
            return i;
        }
    }
    return (uint32_t)-1;                                     // Return -1 if no free inodes
}

// Find first free directory entry slot in a directory block
static int find_free_dirent_slot(const uint8_t *dir_block, uint32_t current_entries) {
    // Cast the block to directory entries array
    struct dirent *dirents = (struct dirent *)dir_block;

    // Starting search from current entries
    for (uint32_t i = current_entries; i < BLOCK_SIZE / sizeof(struct dirent); i ++) {
        if (dirents[i].inode == 0) {
            return i;
        }
    }
    return -1;
}

// Initializing empty journal
static void init_journal(void){
    struct journal_header jh = {
        .magic = JOURNAL_MAGIC,
        .nbytes_used = sizeof(struct journal_header)
    };

    write_block(sb.journal_block, &jh);

    memset(block_buffer, 0, BLOCK_SIZE);
    for (uint32_t i=1; i < JOURNAL_BLOCKS; i++) {
        write_block(sb.journal_block + i, block_buffer);
    }
}

static struct journal_header read_journal_header(void){
    struct journal_header jh;
    read_block(sb.journal_block, &jh);

    return jh;
}

static int journal_exists(void) {
    struct journal_header jh = read_journal_header();
    return jh.magic == JOURNAL_MAGIC;
}

static uint32_t get_journal_free_space(const struct journal_header *jh){
    uint32_t total_journal_bytes = JOURNAL_BLOCKS * BLOCK_SIZE;
    return total_journal_bytes - jh->nbytes_used;             // total - used = free
}

static uint32_t append_to_journal(const void *data, uint32_t size) {
    struct journal_header jh = read_journal_header();

    if (jh.magic != JOURNAL_MAGIC) {
        init_journal();
        jh = read_journal_header();
    }

    if (get_journal_free_space(&jh) < size) {
        return 0;
    }

    uint32_t journal_offset = jh.nbytes_used;
    uint32_t block_offset = journal_offset % BLOCK_SIZE;
    uint32_t current_block = sb.journal_block + (journal_offset / BLOCK_SIZE);

    if (block_offset + size <= BLOCK_SIZE) {
        read_block(current_block, block_buffer);
        memcpy(block_buffer + block_offset, data, size);
        write_block(current_block, block_buffer);
    } else {
        uint32_t first_chunk = BLOCK_SIZE - block_offset;
        uint32_t second_chunk = size - first_chunk;

        read_block(current_block, block_buffer);
        memcpy(block_buffer + block_offset, data, first_chunk);
        write_block(current_block, block_buffer);

        read_block(current_block + 1, block_buffer);
        memcpy(block_buffer, (uint8_t*)data + first_chunk, second_chunk);
        write_block(current_block + 1, block_buffer);
    }

    jh.nbytes_used += size;
    write_block(sb.journal_block, &jh);

    return size;
}

void journal_create(const char *filename) {
    if (strlen(filename) >= NAME_LEN) {
        fprintf(stderr, "ERROR: Filename too long (max %d characters)\n", NAME_LEN - 1);
        exit(EXIT_FAILURE);
    }

    uint8_t inode_bitmap[BLOCK_SIZE];
    uint8_t data_bitmap[BLOCK_SIZE];
    uint8_t inode_block[BLOCK_SIZE];
    uint8_t dir_block[BLOCK_SIZE];

    read_block(sb.inode_bitmap, inode_bitmap);
    read_block(sb.data_bitmap, data_bitmap);
    read_block(sb.inode_start, inode_block);
    read_block(DATA_START_IDX, dir_block);

    uint32_t free_inode = find_free_inode(inode_bitmap);
    if (free_inode == (uint32_t)-1) {
        fprintf(stderr, "ERROR: No free inodes available\n");
        exit(EXIT_FAILURE);
    }

    struct inode *root_inode = (struct inode *)inode_block;
    uint32_t current_dir_entries = root_inode->size / sizeof(struct dirent);
    int free_slot = find_free_dirent_slot(dir_block, current_dir_entries);
    if (free_slot < 0) {
        fprintf(stderr, "ERROR: No free directory slots in root directory\n");
        exit(EXIT_FAILURE);
    }

    struct inode new_inode = {0};
    new_inode.type = 1;
    new_inode.links = 1;
    new_inode.size = 0;
    new_inode.ctime = (uint32_t)time(NULL);
    new_inode.mtime = new_inode.ctime;

    struct dirent new_dirent = {0};
    new_dirent.inode = free_inode;
    strncpy(new_dirent.name, filename, NAME_LEN - 1);
    new_dirent.name[NAME_LEN - 1] = '\0';

    struct dirent *dirents = (struct dirent *)dir_block;
    dirents[free_slot] = new_dirent;

    uint32_t inode_block_index = free_inode / INODES_PER_BLOCK;
    uint32_t inode_offset = free_inode % INODES_PER_BLOCK;

    if (inode_block_index == 0) {
        struct inode *inodes = (struct inode *)inode_block;
        inodes[free_inode] = new_inode;
    } else {
        read_block(sb.inode_start + 1, inode_block);
        struct inode *inodes = (struct inode *)inode_block;
        inodes[inode_offset] = new_inode;
    }

    mark_bitmap(inode_bitmap, free_inode);

    uint32_t needed_space = 0;

    needed_space += sizeof(struct data_record);
    needed_space += sizeof(struct data_record);
    needed_space += sizeof(struct data_record);
    needed_space += sizeof(struct commit_record);

    struct journal_header jh = read_journal_header();
    if (jh.magic != JOURNAL_MAGIC) {
        init_journal();
        jh = read_journal_header();
    }

    if (get_journal_free_space(&jh) < needed_space) {
        fprintf(stderr, "ERROR: Journal full. Run 'install' to apply changes and free space.\n");
        exit(EXIT_FAILURE);
    }

    struct data_record dr_bitmap = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = sb.inode_bitmap
    };
    memcpy(dr_bitmap.data, inode_bitmap, BLOCK_SIZE);
    append_to_journal(&dr_bitmap, sizeof(dr_bitmap));

    struct data_record dr_inode = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = sb.inode_start + inode_block_index
    };
    memcpy(dr_inode.data, inode_block, BLOCK_SIZE);
    append_to_journal(&dr_inode, sizeof(dr_inode));

    struct data_record dr_dir = {
        .hdr = {.type = REC_DATA, .size = sizeof(struct data_record)},
        .block_no = DATA_START_IDX
    };
    memcpy(dr_dir.data, dir_block, BLOCK_SIZE);
    append_to_journal(&dr_dir, sizeof(dr_dir));

    struct commit_record cr = {
        .hdr = {.type = REC_COMMIT, .size = sizeof(struct commit_record)}
    };
    append_to_journal(&cr, sizeof(cr));

    printf("Logged creation of file '%s' (inode %u) in journal\n", filename, free_inode);
}

void journal_install(void) {
    struct journal_header jh = read_journal_header();
    if (jh.magic != JOURNAL_MAGIC) {
        fprintf(stderr, "ERROR: Journal does not exist or is corrupted\n");
        exit(EXIT_FAILURE);
    }

    if (jh.nbytes_used == sizeof(struct journal_header)) {
        printf("Journal is empty, nothing to install\n");
        return;
    }

    printf("Installing journaled metadata changes...\n");

    uint32_t pos = sizeof(struct journal_header);
    uint32_t bytes_processed = 0;
    int in_transaction = 0;
    int transaction_count = 0;

    while (pos < jh.nbytes_used) {
        uint32_t block_num = sb.journal_block + (pos / BLOCK_SIZE);
        uint32_t block_offset = pos % BLOCK_SIZE;

        read_block(block_num, block_buffer);

        struct rec_header *rh = (struct rec_header *)(block_buffer + block_offset);

        if (rh->size == 0 || rh->size > (JOURNAL_BLOCKS * BLOCK_SIZE)) {
            fprintf(stderr, "ERROR: Invalid record size %u at position %u\n", rh->size, pos);
            break;
        }

        if (rh->type == REC_DATA) {
            struct data_record dr;

            if (block_offset + rh->size <= BLOCK_SIZE) {
                memcpy(&dr, block_buffer + block_offset, rh->size);
            } else {
                uint32_t first_part = BLOCK_SIZE - block_offset;
                memcpy(&dr, block_buffer + block_offset, first_part);

                uint8_t next_block[BLOCK_SIZE];
                read_block(block_num + 1, next_block);
                memcpy((uint8_t*)&dr + first_part, next_block, rh->size - first_part);
            }

            write_block(dr.block_no, dr.data);
            in_transaction = 1;

        } else if (rh->type == REC_COMMIT) {
            if (in_transaction) {
                transaction_count++;
                in_transaction = 0;
            } else {
                fprintf(stderr, "WARNING: COMMIT record without preceding DATA records\n");
            }
        } else {
            fprintf(stderr, "ERROR: Unknown record type 0x%04x at position %u\n", rh->type, pos);
            break;
        }

        pos += rh->size;
        bytes_processed += rh->size;

        if (bytes_processed > jh.nbytes_used) {
            fprintf(stderr, "ERROR: Journal parsing overflow\n");
            break;
        }
    }

    init_journal();

    printf("Successfully installed %d transaction(s) from journal\n", transaction_count);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <command> [args]\n", argv[0]);
        fprintf(stderr, "Commands:\n");
        fprintf(stderr, "  create <filename>  - Log creation of a file in journal\n");
        fprintf(stderr, "  install            - Apply journaled changes to filesystem\n");
        return EXIT_FAILURE;
    }

    fd = open(DEFAULT_IMAGE, O_RDWR);
    if (fd < 0) {
        die("open");
    }

    read_superblock();

    if (strcmp(argv[1], "create") == 0) {
        if (argc != 3) {
            fprintf(stderr, "Usage: %s create <filename>\n", argv[0]);
            close(fd);
            return EXIT_FAILURE;
        }
        journal_create(argv[2]);
    } else if (strcmp(argv[1], "install") == 0) {
        if (argc != 2) {
            fprintf(stderr, "Usage: %s install\n", argv[0]);
            close(fd);
            return EXIT_FAILURE;
        }
        journal_install();
    } else {
        fprintf(stderr, "Unknown command: %s\n", argv[1]);
        fprintf(stderr, "Valid commands: create, install\n");
        close(fd);
        return EXIT_FAILURE;
    }

    if (close(fd) < 0) {
        die("close");
    }

    return EXIT_SUCCESS;
}
