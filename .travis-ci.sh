case "$OCAML_VERSION" in
4.00.1) ppa=avsm/ocaml40+opam10 ;;
4.01.0) ppa=avsm/ocaml41+opam10 ;;
*) echo "Unknown ocaml version:"$OCAML_VERSION; exit 1 ;;
esac

echo "yes" | sudo add-apt-repository ppa:$ppa
sudo apt-get update -qq
sudo apt-get install ocaml
make -f Makefile.${ARCH} min-caml
# Currently, no tests are available.
# make test

# Compiles test/fib.ml and displays the result.
./min-caml test/fib
echo "*** the content of assembly ***"
cat test/fib.s

