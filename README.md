# MinCaml to Zebius [![Build Status](https://travis-ci.org/koba-e964/min-caml.svg?branch=master)](https://travis-ci.org/koba-e964/min-caml)

A min-caml compiler whose target is [Zebius](https://github.com/ProcessorCompilerExperiment2014-Team0/Zebius).

## Progress

| item | status |
| --- | --- |
| compilation of fib | ok |
| execution of fib on simulator | ok |
| execution of fib on FPGA | ok |
| I/O | ok |
| sin, cos | incomplete (reduction by 2*pi is not exact) |
| atan | ok |
| compilation of *library form* | ok |
| parsing of raytracer | ok |
| compilation of raytracer | ok |
| execution of raytracer on simulator | ok |
| execution of raytracer on FPGA | no |

## How to use
```
git clone https://github.com/koba-e964/min-caml/ min-caml-koba
cd min-caml-koba
make min-caml
./min-caml test/fib
```
## Requirement
* ocaml

