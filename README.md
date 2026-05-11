The modified versions of Toooba implementing move elimination can be found in `implementations/maximal` and `implementations/move-table` respectively, these are both snapshots from the https://github.com/soweli-pali/Toooba Toooba fork from the following branches:
- maximal: `CHERI` (6af3c2686f7079e1708062fbee109c255b777d37)
- move-table: `performance/move-table-v2` (c78a6b74b02b648af69e8346a2a545c5466a44cc)

A further script change to the Toooba repository used in evaluation can be the `Konata` directory.

To run the microbenchmarks (found in `evaluation/microbenchmarks`) the tests were written in the mv.S file and built in a fork of Flute (https://github.com/soweli-pali/Flute) to take advantage of existing tooling. This produced the `rv64ui-p-mv` and `rv64ui-p-mv.dump` files, which can be placed in the `Tests/isa` directory of the Toooba repository under test to be ran as normal. The builds used have been included here for reproducibility.

Script and makefile changes used to run TestRIG on the modified implementations can be found in the `TestRIG` directory along with a brief explanation of how to use them.
