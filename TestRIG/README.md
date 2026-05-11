This folder contains the modified script and makefile used to run TestRIG on the modified implementations.

To use these replace their original versions in the TestRIG repository and include the modified Toooba repo in a new `riscv-implementations/Toooba-mod` directory, you can do this via symlink. After this the tests are ready to be ran as normal, for example via the commands

```
  make vengines
  make toooba-rv64
  make toooba-mod-rv64
  utils/scripts/runTestRIG.py -a toooba -b toooba-mod -r rv64i --timeout 600
```
