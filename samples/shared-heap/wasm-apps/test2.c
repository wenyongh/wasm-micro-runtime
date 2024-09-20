#include <stdio.h>

extern void
shared_free(void *ptr);

void
print_buf(char *buf)
{
    printf("wasm app2's wasm func received buf: %s\n\n", buf);
    shared_free(buf);
}
