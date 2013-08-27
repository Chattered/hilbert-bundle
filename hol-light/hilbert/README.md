hilbert
=======

This is my HOL Light verification for the first two groups of axioms in Hilbert's Foundations of Geometry.

Notes
=====

* Everything in this repo requires a *lot* of cleanup. It's mostly here to keep me honest. The theorems proven are the same as those claimed in the thesis up to alpha-conversion, adding explicit universal quantifiers and currying of implications.
* Possibly the most useful file in this repository is mizar_extra.ml, since it contains detailed comments and commentary on Mizar Light.
* I have only built on Ocaml 3.12, and have made documented modifications to the camlp5 preprocessors for HOL Light and Mizar light (see pa_j_phil.ml and pa_f_phil.ml). These need to be copied to pa_j.ml and hilbert/pa_f.ml, and then compiled with ocamlc as shown in JRH's Makefile.
* Many of the ideas in this code evolved over time, and only my latest thoughts made it into the thesis. My original idea for navigating around a maze when proving the PJCT was to think about a player grabbing a wall with their "hand". This metaphor is still present in theorems such as squeeze.
* Many theorems are proven *extremely* slowly. I think it takes me about 30 minutes to get the theory through. Speed generally wasn't my main concern in proving theorems: getting close to the prose was.