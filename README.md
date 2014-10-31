# MinCaml to Zebius [![Build Status](https://travis-ci.org/koba-e964/min-caml.svg?branch=master)](https://travis-ci.org/koba-e964/min-caml)

A min-caml compiler whose target is [Zebius](https://github.com/ProcessorCompilerExperiment2014-Team0/Zebius).

## Progress

| item | status |
| --- | --- |
| compilation of fib | ok |
| execution of fib on simulator | ok |
| execution of fib on FPGA | ok |
| I/O | no |
| sin, cos | incomplete (not reduced by 2*pi) |
| atan | no |
| compilation of *library form* | no |
| parsing of raytracer | yes |
| compilation of raytracer | no |
| execution of raytracer on simulator | no |
| execution of raytracer on FPGA | no |

## How to use
```
git clone https://github.com/koba-e964/min-caml/ min-caml-koba
cd min-caml-koba
./to_zebius; make min-caml
./min-caml test/fib
```
## Requirement
* ocaml

