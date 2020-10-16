#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#include "cJSON.h"

#ifndef NULL
#define NULL (void*)0
#endif

#ifndef __cplusplus
#define true 1
#define false 0
#define inline __inline
#endif

/* Return the offset of the given field in the given type */
#ifndef offsetof
#define offsetof(Type, field) ((size_t)(&((Type *)0)->field))
#endif

typedef uint8_t uint8;
typedef int8_t int8;
typedef uint16_t uint16;
typedef int16_t int16;
typedef uint32_t uint32;
typedef int32_t int32;

#define BH_MALLOC malloc
#define BH_FREE free

#define BITMASK_SIGN_BIT         0x0001
#define BITMASK_LEAST_FOUR_BITS  0x000F
#define BITMASK_LEAST_FIVE_BITS  0x001F
#define BITMASK_CONTINUATION_BIT 0x0020

#if 0
static const char *BASE64_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                     "abcdefghijklmnopqrstuvwxyz"
                                     "0123456789+/";
#endif

static bool
vlqchar_decode(const char ch, int32 *p_number)
{
    if (ch >= 'A' && ch <= 'Z') {
        *p_number = ch - 'A';
    }
    else if (ch >='a' && ch <= 'z') {
        *p_number = 26 + ch - 'a';
    }
    else if (ch >= '0' && ch <= '9') {
        *p_number = 52 + ch - '0';
    }
    else if (ch == '+') {
        *p_number = 62;
    }
    else if (ch == '/') {
        *p_number = 63;
    }
    else {
        printf("Invalid base64vlq character.\n");
        return false;
    }

    return true;
}

static int32
vlqs_decode(int32 *vlqs, int32 size)
{
  bool is_negative = false;
  int32 x = 0, sextet, i;

  for (i = size - 1; i >=0; i--) {
      sextet = vlqs[i];
      if (i == 0) {
          if (sextet & BITMASK_SIGN_BIT)
              is_negative = true;
          sextet >>= 1;
          x <<= 4;
          x |= sextet & BITMASK_LEAST_FOUR_BITS;
      }
      else {
          x <<= 5;
          x |= sextet & BITMASK_LEAST_FIVE_BITS;
      }
  }

  return is_negative ? -x : x;
}

static bool
base64vlq_decode(const char *base64vlq,
                 int32 *numbers, int32 number_size)
{
    const char *p = base64vlq;
    const char *p_end = p + strlen(base64vlq);
    int32 vlqs[10], vlq_index = 0, number_index = 0;
    bool is_terminated;

    while (p < p_end) {
        if (number_index >= number_size) {
            printf("Malformed VLQ sequence.\n");
            return false;
        }

        is_terminated = 0;
        vlq_index = 0;
        while (p < p_end) {
            if (vlq_index >= 7) {
                printf("Malformed VLQ sequence.\n");
                return false;
            }

            if (!vlqchar_decode(*p++, &vlqs[vlq_index++])) {
                return false;
            }

            if (!(vlqs[vlq_index - 1] & BITMASK_CONTINUATION_BIT)) {
                is_terminated = 1;
                break;
            }
        }

        if (!is_terminated) {
            printf("Malformed VLQ sequence.\n");
            return false;
        }

        numbers[number_index++] = vlqs_decode(vlqs, vlq_index);
    }

    if (number_index != number_size) {
        printf("Malformed VLQ sequence.\n");
        return false;
    }
    return true;
}

static int
print_help()
{
    printf("Usage: sourcemap-sourcemap-dump sourcemap_file\n");
    return 1;
}

char*
bh_read_file_to_buffer(const char *filename, uint32 *ret_size)
{
    char *buffer;
    int file;
    uint32 file_size, read_size;
    struct stat stat_buf;

    if (!filename || !ret_size) {
        printf("Read file to buffer failed: invalid filename or ret size.\n");
        return NULL;
    }

    if ((file = open(filename, O_RDONLY, 0)) == -1) {
        printf("Read file to buffer failed: open file %s failed.\n",
               filename);
        return NULL;
    }

    if (fstat(file, &stat_buf) != 0) {
        printf("Read file to buffer failed: fstat file %s failed.\n",
               filename);
        close(file);
        return NULL;
    }

    file_size = (uint32)stat_buf.st_size;

    if (!(buffer = BH_MALLOC(file_size))) {
        printf("Read file to buffer failed: alloc memory failed.\n");
        close(file);
        return NULL;
    }

    read_size = (uint32)read(file, buffer, file_size);
    close(file);

    if (read_size < file_size) {
        printf("Read file to buffer failed: read file content failed.\n");
        BH_FREE(buffer);
        return NULL;
    }

    *ret_size = file_size;
    return buffer;
}

#define CHECK_ITEM_TYPE(item, type) do {    \
    if (!cJSON_Is##type(item)) {            \
      printf("Invalid item type of %s\n",   \
             item->string);                 \
      return;                               \
    }                                       \
  } while (0)

static void
dump_sourcemap_json(cJSON *json_obj)
{
    int i, size;
    cJSON *item, *item_src, *item_name, *item_src_content;
    char *mappings, *mapping, sources_content, *p, *p_end;
    int32 mapping_values[10], mapping_value_count = 4;
    int32 abs_values[10] = { 0 };

    if (!cJSON_IsObject(json_obj)) {
        printf("Invalid json format.\n");
        return;
    }

    cJSON_ArrayForEach(item, json_obj) {
        printf("%s: ", item->string);
        if (!strcmp(item->string, "version")) {
            CHECK_ITEM_TYPE(item, Number);
            printf("%d\n", item->valueint);
        }
        else if (!strcmp(item->string, "sourceRoot")) {
            CHECK_ITEM_TYPE(item, String);
            printf("%s\n", item->valuestring);
        }
        else if (!strcmp(item->string, "sources")) {
            CHECK_ITEM_TYPE(item, Array);

            size = cJSON_GetArraySize(item);
            printf("%d items\n", size);
            for (i = 0; i < size; i ++) {
                item_src = cJSON_GetArrayItem(item, i);
                CHECK_ITEM_TYPE(item_src, String);
                printf("  %s\n", item_src->valuestring);
            }
        }
        else if (!strcmp(item->string, "names")) {
            CHECK_ITEM_TYPE(item, Array);

            size = cJSON_GetArraySize(item);
            printf("%d items\n", size);
            for (i = 0; i < size; i ++) {
                item_name = cJSON_GetArrayItem(item, i);
                CHECK_ITEM_TYPE(item_name, String);
                printf("  %s\n", item_name->valuestring);
            }
        }
        else if (!strcmp(item->string, "mappings")) {
            CHECK_ITEM_TYPE(item, String);
            printf("\n");
            p = mapping = mappings = item->valuestring;
            p_end = p + strlen(p);
            while (p < p_end) {
                while (*p != ',' && *p != '\0')
                    p++;
                *p++ = '\0';
                printf("  %-8s => [", mapping);
                if (!base64vlq_decode(mapping,
                                      mapping_values,
                                      mapping_value_count)) {
                    return;
                }

                for (i = 0; i < mapping_value_count; i++) {
                    printf("%4d", mapping_values[i]);
                    if (i < mapping_value_count - 1)
                        printf(",");
                    abs_values[i] += mapping_values[i];
                }
                printf("] => [");

                printf("code offset 0x%04x, file %2d, line %3d, column %2d]\n",
                       abs_values[0], abs_values[1],
                       abs_values[2], abs_values[3]);

                mapping = p;
            }
        }
        else if (!strcmp(item->string, "sourcesContent")) {
            CHECK_ITEM_TYPE(item, Array);

            size = cJSON_GetArraySize(item);
            printf("%d items\n", size);
            for (i = 0; i < size; i ++) {
                item_src_content = cJSON_GetArrayItem(item, i);
                CHECK_ITEM_TYPE(item_src_content, String);
                /*printf("  %s\n", item_src_content->valuestring);*/
                printf("  ignored.\n");
            }
        }
        else {
            printf("Unknown item %s.\n", item->string);
            return;
        }
        printf("\n");
    }

    (void)sources_content;
}

int
main(int argc, char **argv)
{
    char *sourcemap_file = NULL;
    uint8 *sourcemap_file_buf = NULL;
    uint32 sourcemap_file_size;
    cJSON *json = NULL;

    if (argc != 2)
        return print_help();

    sourcemap_file = argv[1];

    /* load WASM byte buffer from WASM bin file */
    if (!(sourcemap_file_buf = (uint8*)
                bh_read_file_to_buffer(sourcemap_file, &sourcemap_file_size)))
        return 0;

    if (!(json = cJSON_Parse(sourcemap_file_buf))) {
        printf("Parse json format of SourceMap file failed.\n");
        goto fail1;
    }

    dump_sourcemap_json(json);

    cJSON_Delete(json);

fail1:
    BH_FREE(sourcemap_file_buf);
    return 0;
}

