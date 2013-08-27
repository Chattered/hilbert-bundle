hilbert-bundle
==============

Verification of Hilbert's first two groups of axioms and elementary consequences.

Bundled are versions of Ocaml, batteries, camlp5, hol light and ounit that should work together.

After installing, run with:

    cd hilbert-bundle/hol-light
    make
    ocaml
    # #use "hol_finite.ml";;
    # #use "hilbert/hilbert.ml";;
