# See LICENSE for license details.

#*****************************************************************************
# move.S
#-----------------------------------------------------------------------------
#
# Test move instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

# Test move chains

    # 1 move
    TEST_CASE( 1, x14, 0xeadcafedeadcafed, \
      la x1, ptr_to_tdat; \
      ld x1, 0(x1); \
      addi x2, x1, 0; \
      ld x14, 8(x2); \
    )

    # 0 moves from same address
    TEST_CASE( 2, x13, 0xeadcafedeadcafed, \
      la x1, ptr_to_tdat; \
      ld x1, 0(x1); \
      ld x13, 8(x1); \
    )

    # 3 moves from same address
    TEST_CASE( 3, x13, 0xeadcafedeadcafed, \
      la x1, ptr_to_tdat; \
      ld x1, 0(x1); \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      ld x13, 8(x2); \
    )

    # 15 moves from same address
    TEST_CASE( 4, x13, 0xeadcafedeadcafed, \
      la x1, ptr_to_tdat; \
      ld x1, 0(x1); \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      addi x1, x2, 0; \
      addi x2, x1, 0; \
      ld x13, 8(x2); \
    )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

ptr_to_tdat:
    .dword tdat

tdat:
tdat1:  .dword 0xdeadcafedeadcafe
tdat2:  .dword 0xeadcafedeadcafed
tdat3:  .dword 0xadcafedeadcafede
tdat4:  .dword 0xdcafedeadcafedea

RVTEST_DATA_END
