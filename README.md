# CoinductionExamples

Examples on how to use the coq-coinduction library, a library for doing proofs by (enhanced) coinduction based on the notion of 'companion', from the paper:
Coinduction All the Way Up. Damien Pous. In Proc. LICS, 2016.

 - a formalisation of Hur et al's toy example on divergence 
 - a formalisation of Rutten's stream calculus
 - a formalisation of Milner's calculus of communicating systems (CCS)
 - a formalisation of automata and regular expression equivalence
 - an example on how to use the companion to avoid the need for generalized parameterized coinduction
 
## Modules
 + `divergence.v`  : Hur et al's example on divergence 
 + `streams.v`     : Rutten's stream calculus 
 + `ccs.v`         : Milner's CCS, strong and weak bisimilarity 
 + `automata.v`    : Automata equivalence, regular expressions 
 + `gpaco.v`       : generalized paco via the companion

## Meta

- Author(s):
  - Damien Pous (initial)
- Coq-community maintainer(s):
  - Damien Pous ([**@damien-pous**](https://github.com/damien-pous))
- License: [GNU LGPL](LICENSE)
- Additional dependencies: coq-coinduction, and coq-aac-tactics + coq-relation-algebra for the CCS example
- Coq namespace: `CoinductionExamples`
- Related publication(s):
  - [Coinduction All the Way Up](https://hal.archives-ouvertes.fr/hal-01259622) doi:[10.1145/2933575.2934564](http://dx.doi.org/10.1145/2933575.2934564)

## Building and installation instructions

The easiest way to install the latest released version of CoinductionExamples
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-coinduction-examples
```

To instead build and install manually, do:

``` shell
git clone https://github.com/damien-pous/coinduction-examples.git
cd coinduction-examples
make
make install
```

## Compatibility

to see how to port code from coq-coinduction v1.6 to v1.7, 
check the following commit 7afec25f051cc4b45820c333bfd4b4689d86abef
