# Homogeneous plane continua in Lean: the modules of the classification

This repository holds the modules of the Lean formalization in the repository
[homogeneous-plane-continua][full] that the proof of the classification of homogeneous plane
continua draws on. The documentation, the records and the other modules are in the full
repository.

[full]: https://github.com/DavidVFeldman/homogeneous-plane-continua

The two final theorems, `HPC.BJ59.ho16_classification₄` and
`HPC.BJ59.ho16_classification_plane₄`, are in `HPC/BJ59/BJ59E.lean`.

## How this repository was made

`scripts/make_minimal.py` derives it from the full repository, using the full repository's
dependency census (`doc/depcensus/` there; its README says which state of the sources it
describes):

* only the library `HPC` is kept, the import closure of `HPC.BJ59.BJ59E` (709 modules);
* of these, 635 modules are kept: the 446 that hold a declaration the final theorems use,
  and every module that a declaration in a kept module refers to;
* the other 74 are removed;
* a module that defines syntax, notation, macros or attributes for kept modules is kept too,
  since that leaves no trace in the census; here every such module is kept already;
* a kept module that imported a removed one imports what the removed one imported instead.

Nothing inside a kept module is changed apart from its import lines. So the kept modules also
hold declarations the final theorems do not use: of their 7,618 declarations, the final
theorems use 4,689.

635 modules under `HPC/`, with 188,502 lines of Lean, and the root module `HPC.lean`.

Comments in the Lean files cite documents, modules and line numbers of the full repository. In
the 35 modules whose imports were rewritten, the line numbers differ from the full
repository's.

## Building and checking

The toolchain is `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (`lean-toolchain`,
`lake-manifest.json`). From the root:

```
lake exe cache get                         # Mathlib's compiled files
lake build                                 # the library HPC
lake env lean Axioms.lean > axioms-ci.txt  # the axiom audit; compare with axioms.txt
```

`Axioms.lean` holds the `#print axioms` lines of the full repository's audit for theorems
declared in kept modules: 3,623 lines, for 3,612 theorems (as in the full repository,
a few theorems are printed in more than one group). `axioms.txt` is its expected output. The
workflow in `.github/workflows/build.yml` builds the library on every push, fails on any
`sorry`, regenerates the audit, compares it with `axioms.txt`, and allows no axiom other than
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

`scripts/make_minimal.py` was written by Claude (Anthropic).

## License

Apache License 2.0; see `LICENSE`. Quotations from published papers in the comments of the Lean
files remain under their publishers' copyright and are not covered by this license.
