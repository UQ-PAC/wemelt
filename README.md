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

`-v` can be used to print the P, D, and Gamma values after each statement

`-d` can be used to print additional debug information 

```
./wemelt.sh file1 ..
./wemelt.sh -v file1 file2 ..
./wemelt.sh -d file1 file2 ..
```

## Examples
Please use the provided examples in /examples and /tests as an example of the input file format. The programs in /examples should all pass with no errors, and the programs in /tests should all fail, each checking for a particular type of error, but all are syntactically correct.

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
