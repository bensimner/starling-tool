# Starling (Matt Windsor's experimental fork)

_Starling_ is an automated verification tool for concurrent programs.
It accepts programs written in a C-like language and annotated with
_Concurrent Views Framework_-style assertions, as well as a series
of constraints binding those assertions to concrete facts about the
program's shared state, and tries to prove soundness.

For a quick example of the flavour of Starling scripts, see
`Examples/Pass/ticketLock.cvf`.

This is an experimental fork adding .NET Core support.  For a more stable
experience, see the `mw-locals` branch of
[`septract/starling-tool`](https://github.com/septract/starling-tool).

## Current work

Starling is a work in progress, but currently it can check
correctness of fully-specified programs written in a limited command
language (integer and Boolean variables; arrays; basic statements; atomic
assignment and compare-and-swap; parameter-less methods with no
calling).

Starling can be used on its own to check complete proofs of programs
using the `Z3` SMT solver, or combined with other tools:

* With the `HSF` Horn clause solver, Starling can perform limited definition
  inference for proofs, helping to complete partial proofs;
* (Experimental.)  With the `GRASShopper` separation logic solver, Starling can
  prove properties of programs using linked heap-based data structures.

## Future work

* Methods with call/return syntax;
* Structs;
* Proof of soundness of the tool itself;
* Clean-up and general user interface polish.

## Requirements

- [.NET SDK 5](https://www.microsoft.com/net/learn/get-started/), and its version of FSharp;
- [Z3 4.6.0](http://z3prover.github.io): -both the native library (`libz3`) and the .NET Core bindings
  (`Microsoft.Z3.dll`).  At the time of writing, the .NET Core build needs a
  few workarounds (to be documented).

The helper scripts mentioned below require a POSIX environment:
cygwin or MSYS should work on Windows.

To use HSF, you will need a copy of `qarmc`.  An [outdated but
useable version of `qarmc`](https://www7.in.tum.de/~popeea/research/synthesis/)
is available.  Install it in your `PATH` to be able to use
`starling-hsf.sh`.

To use GRASShopper, you will need a copy of `grasshopper.native`.
This can be compiled from source available at
[this GitHub repository](https://github.com/wies/grasshopper).  Install it
in your `PATH` to be able to use `starling-gh.sh`.

## Build

- Compile `Microsoft.Z3.dll` for .NET Core, and copy it to the root directory.
- Run:
  - `dotnet tool restore`;
  - `dotnet paket restore`;
  - `dotnet build`.

## Usage

* To check a Starling file using Z3, use `./starling.sh -ssmt-failures /path/to/file`.
  Examples using Z3 can be found in `Examples/Pass` and `Examples/Fail`.
* To check a Starling file using HSF/qarmc, use `./starling-hsf.sh /path/to/file`.
  Examples using HSF can be found in `Examples/PassHSF`.
* To check a Starling file using `GRASShopper`, use `./starling-gh.sh /path/to/file`.
  Examples using GRASShopper can be found in `Examples/PassGH`.
* To run the regression tests, use `./regress.sh`.

## Editor support

A very basic major mode (highlighting only) for GNU Emacs, based on `cc-mode`,
is available in `syntax/starling-mode.el`.  This is fairly outdated.

## People

* [Matt Windsor](https://www-users.cs.york.ac.uk/~mbw500/)
* [Mike Dodds](https://www-users.cs.york.ac.uk/~miked/)
* [Matthew Parkinson](http://research.microsoft.com/en-us/people/mattpark/)
* Ben Simner

## Licence

MIT; see `LICENSE`.
