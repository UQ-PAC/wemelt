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

This version is not complete and cannot perform proper analysis. There are some available input files in the /bilexamples folder, but secret_write_bil is not finished, and the others all have major errors when ran.
