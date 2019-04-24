# Go/0

## Introduction

In the last chapter of his book Algorithms + Data Structures = Programs, Niklaus
Wirth explained the basics of compiler theory by implementing a toy language of
his own devising, called PL/0 (for Programming Language 0). To facilitate its
exposition in 40 pages it lacked any means of data structuring, with only the
basic integer type being supported. On the other hand, all the usual methods of
algorithm construction were available, including control flow statements and
procedure calls (though with some restrictions). PL/0's implementation,
moreover, was a tour de force, its development by stepwise refinement having
been made explicit for the reader to learn by example how to control the
complexity of writing a relatively large, non-trivial program using an iterative
design process. The final product included a P-code interpreter to shield the
compiler code from the ideoscyncracies of any one particular machine's ISA in
use at the time, further demonstrating the feasability of using a high-level,
machine-independent language for the precise description of a processor
architecture.

The present repository marks an attempt at identifying a strict subset of the
Go programming language that corresponds roughly to PL/0 in terms of
expressivity. In keeping with its source of inspiration, we have named this
fragment Go/0. Our motivation for choosing Go derives from the `Wirthean' feel
present in its minimalistic design philosophy and the borrowing of more than a
few ideas from Oberon-2.

The current exercise served self-educational purposes, having had in mind a
close study of prior art on the topic of compiler theory as well as the
acquiring of some hands-on experience through the controlled recombination of
the key ideas found therein.

## Requirements

* A C99-compatible compiler (e.g., GCC or Clang)

## Installation and Usage

Clone or download the sources. E.g,
```
wget https://github.com/arnobastenhof/gozero/archive/master.zip
unzip master.zip
```
In keeping with the source material, we have kept the program to a single file.
Thus, simply invoking `gcc gozero.c` or `clang gozero.c` (for GCC or Clang)
should result in an executable `a.out`. Subsequently running
```
./a.out test.go
```
tests the compiler on a sample program adapted from Wirth's treatise on PL/0.
