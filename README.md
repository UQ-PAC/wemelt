## Requirements
* Java 8
* Scala (tested with 2.12.8)

## Supported Platforms
* Mac OS (hopefully)
* Linux


## Building

The tool should build by typing `make` in the top-level directory.

```
make
```

This should produce a shell script `armlogictool.sh` for running it.

## Running

Run `armlogictool.sh`, supplying a list of files to analyse as command line
arguments.

`-v` can be used ato print the P, D, and Gamma values after each statement

`-d` can be used to print additional debug information 

```
./armlogictool.sh file1 file2 ..
./armlogictool.sh -v file1 file2 ..
./armlogictool.sh -d file1 file2 ..
```

## Input file format

### Variable definitions
```
_var z:
_Mode: NoW

_var x:
_L: z % 2 == 0
_Mode: NoW

_var r_secret:
_L: FALSE
```
Variables must be defined at the start of the file, before any statements. Variables can have the mode `NoW` (No Write), `NoRW` (No Read/Write) or `RW` (Read/Write). Variables with `r_` at the start of their names are Local, and automatically have the mode `NoRW`. All other variables are Global. If the L predicate is not defined for a variable, it will be `TRUE` by default. 

### P_0 and Gamma_0 definitions
```
_P_0: z == 0
_Gamma_0: x -> LOW, r_secret -> HIGH
```
Defining the P_0 and/or Gamma_0 is optional, but can occur between the variable definitions and the program. By default, P_0 will be set to `TRUE` and Gamma_0 will be set to `HIGH` for all variables in its domain. Predicates in P_0 can be separated with `,`.

### While statements
```
while(TRUE)
_invariant: z % 2 == 0
_Gamma: x -> LOW, r_secret -> HIGH
{
  z = z + 1;
  fence;
  x = r_secret;
  x = 0;
  fence;
  z = z + 1;
}
```
While statements must have the loop invariants for P and Gamma defined with `_invariant: ` for P' and `_Gamma:` for Gamma'.


### Supported operations
* `=` assignment
* `==` equality
* `<=` less than or equal to
* `<` less than
* `>=` greater than or equal to
* `>` greater than
* `!` logical not
* `&&` logical and
* `||` logical or
* `+` addition
* `-` subtraction
* `*` multiplication
* `/` integer division
* `%` modulus
* `|` bitwise or
* `&` bitwise and
* `^` bitwise xor
* `~` bitwise not
* `>>` logical shift right
* `>>>` arithmetic shift right
* `<<` shift left

