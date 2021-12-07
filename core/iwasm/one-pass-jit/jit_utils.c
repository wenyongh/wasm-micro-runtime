#include "jit_utils.h"

JitBitmap *
jit_bitmap_new(unsigned begin_index, unsigned bitnum)
{
    JitBitmap *bitmap;

    if ((bitmap = jit_calloc(offsetof(JitBitmap, map) + (bitnum + 7) / 8))) {
        bitmap->begin_index = begin_index;
        bitmap->end_index = begin_index + bitnum;
    }

    return bitmap;
}
