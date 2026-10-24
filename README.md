# Homogeneous plane continua in Lean: the classification alone

This repository holds the declarations of the Lean formalization in the repository
[homogeneous-plane-continua][full] that the proof of the classification of homogeneous plane
continua uses. The documentation, the records and the other results are in the full repository.

[full]: https://github.com/DavidVFeldman/homogeneous-plane-continua

The two final theorems, `HPC.BJ59.ho16_classification₄` and
`HPC.BJ59.ho16_classification_plane₄`, are in `HPC/BJ59/BJ59E.lean`.

## How this repository was made

It was derived from the full repository in two steps, using the full repository's dependency
census (`doc/depcensus/` there; its README defines the census and says which state of the sources
it describes). A declaration is *used* when the census finds it in the closure of the two final
theorems under the constants occurring in types and proof terms.

1. `scripts/make_minimal.py` kept the library `HPC`, and of the 709 modules of the import closure
   of `HPC.BJ59.BJ59E` the 635 that hold a used declaration or that declarations in such
   modules refer to.
2. `scripts/prune.py` deleted from those modules the declarations that are not used (the
   2,927 candidates of `doc/minimal/unused.tsv`), except the 8 listed in
   `doc/minimal/keep.txt`, and removed the modules left without declarations. A module that
   imported a removed one imports what the removed one imported instead.

Nothing else in the Lean files was changed. The declarations of `keep.txt` are needed by proofs
without occurring in their proof terms (a lemma named in a `simp only` list, for example), so the
census does not see them; each line gives the reason.

446 modules under `HPC/`, with 114,063 lines of Lean, and the root module `HPC.lean`. They
hold 4,697 declarations: the 4,689 used ones and those of `keep.txt`.

Comments in the Lean files cite documents, modules and line numbers of the full repository; line
numbers here differ.

## Building and checking

The toolchain is `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (`lean-toolchain`,
`lake-manifest.json`). From the root:

```
lake exe cache get                         # Mathlib's compiled files
lake build                                 # the library HPC
lake env lean Axioms.lean > axioms-ci.txt  # the axiom audit; compare with axioms.txt
```

`Axioms.lean` holds the `#print axioms` lines of the full repository's audit for the theorems
this repository keeps: 2,253 lines, for 2,246 theorems (as in the full
repository, a few theorems are printed in more than one group). `axioms.txt` is its expected
output. The workflow in `.github/workflows/build.yml` builds the library on every push, fails on
any `sorry`, regenerates the audit, compares it with `axioms.txt`, and allows no axiom other than
`propext`, `Classical.choice` and `Quot.sound`.

## Credits

*Draft, to be edited.*

The project was directed by David V. Feldman (University of New Hampshire). The Lean code was
written by Aristotle (Harmonic) from commissions, and in many places statement skeletons, written by
Claude (Anthropic), which also wrote the defects ledger and the severity document.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

`scripts/make_minimal.py` and `scripts/prune.py` were written by Claude (Anthropic).

## License

Apache License 2.0; see `LICENSE`. Quotations from published papers in the comments of the Lean
files remain under their publishers' copyright and are not covered by this license.
