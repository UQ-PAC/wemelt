## Requirements
* Java 8
* Scala (tested with 2.12.8)

## Supported Platforms
* Mac OS (hopefully)
* Linux


## Building

WeMeLT should build by typing `make` in the top-level directory.

```
make
```

This should produce a shell script `wemelt.sh` for running it.

## Running

Run `wemelt.sh`, supplying a list of files to analyse as command line
arguments.

`-v` can be used ato print the P, D, and Gamma values after each statement

`-d` can be used to print additional debug information 

```
./wemelt.sh file1 file2 ..
./wemelt.sh -v file1 file2 ..
./wemelt.sh -d file1 file2 ..
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

_var r12:
_L: TRUE
```
Variables must be defined at the start of the file, before any statements. Variables can have the mode `NoW` (No Write), `NoRW` (No Read/Write) or `RW` (Read/Write). Variables with `r_`  at the start of their names or of the form `r#` (where `#` is a sequence of digits) are Local, and automatically have the mode `NoRW`. All other variables are Global. If the L predicate is not defined for a variable, it will be `TRUE` by default. 

### Array definitions
```
_array z[2]:
_L: TRUE
_Mode: NoW

_array x[2]:
_L[0]: z[0] % 2 == 0
_L[1]: z[1] % 2 == 0
_Mode: NoW
```
Arrays can be defined in the same section as variables, with `_array` instead of `_var`, and the size of the array specified between square brackets. An L predicate can be specified for the entire array with `_L:` or for each index with `_L[0]:`, `_L[1]:` and so on. Modes are specified for the entire array.

### P_0 and Gamma_0 definitions
```
_P_0: z == 0
_Gamma_0: x -> LOW, r_secret -> HIGH, q[*] -> LOW
```
Defining the P_0 and/or Gamma_0 is optional, but can occur between the variable definitions and the program. By default, P_0 will be set to `TRUE` and Gamma_0 will be set to `HIGH` for all variables in its domain. Predicates in P_0 can be separated with `,`. Gamma_0 can be specified for all members of an array with the wildcard `q[*]` for the array `q`.

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
A previously unstable variable can also be specified to be stable for the loop's duration with the annotation `_Stable: `.

### Do While statements
```
do
_invariant: TRUE
_Gamma: r1 -> LOW, r2 -> HIGH, z -> LOW
{
  r1 = z;
} while ((r1 % 2) != 0)
```
Do While statements are supported similarly to While statements and must have their loop invariants specified. 

### Other statements
```
r_cas_result = CAS(head, r_h, r_h + 1);
if (r_cas_result == 0) {
  r_task = 0;
}
```
If statements and the atomic compare-and-swap (CAS) operation are also supported. The CAS statement assigns 1 to its result variable if the CAS is successful and 0 if it is not. CAS cannot be used in other expressions.

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

### Differences from paper
* arrays
* cas
* updated forwarding
* don't restrict locals
* cfence
* no infeasible paths (must be enabled with -p due to potentially causing issues with D invariant calculation for while rule)