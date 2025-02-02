#ifndef QPOOL_H
#define QPOOL_H

#include <stddef.h> /* for size_t (according to C89) */

#include "macros.h"

Q_STARTCXX /* */

  typedef struct qt_mpool_s qpool;

void *qpool_alloc(qpool *pool);

void qpool_free(qpool *restrict pool, void *restrict mem);

qpool *qpool_create(size_t const item_size);
qpool *qpool_create_aligned(size_t const item_size, size_t const alignment);

void qpool_destroy(qpool *pool);

Q_ENDCXX /* */

#endif // ifndef QPOOL_H
  /* vim:set expandtab: */
