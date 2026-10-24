import HPC.Hagopian.Hagopian76C
import HPC.Hagopian.H76Collar
import HPC.Hagopian.H76Lemma3
import HPC.Plane.SorgenfreyDefs

/-!
# Batch 159 skeleton: Hagopian 1976, Lemma 6 and the unnumbered claims, Lemma 7; the plane
# Schoenflies theorem and a two-sided collar of an arc; Lemma 8 with prescribed caps; Lemma 9

Batch 159 (`doc/batches/COMMISSION-batch159.md`; report `doc/batches/REPORT-batch159.md`). The
skeleton is kept as `doc/batches/skeletons/Hagopian76D.lean`. Supporting proofs:

* `H76Schoen.lean` (item C): `plane_schoenflies_aux` (Moore 1919's `m19_schoenflies_boundary_proof`
  for the restricted regions of the plane, `spaceRestricted ptSetoid`, transported along
  `ptHomeo`), and the cross-cut theorem in the plane `plane_split` (Moore 1919's
  `split_interior_of`, transported the same way);
* `H76Invert.lean` (item C): half-collars on the bounded side (`isHalfCollar_bounded`) and on the
  unbounded side (`isHalfCollar_unbounded`, by an inversion);
* `H76Collar.lean` (item C): accessibility at a non-cut point (`accessible_of_noncut`), every arc
  lies on a simple closed curve (`TArc.exists_closing_arc`), and `exists_collar_aux`; the definition
  `IsCollar` (moved there unchanged);
* `H76Lemma8Caps.lean` (item D): `lemma8_caps_aux`.

Items that remain open are commented out (no `sorry`), each with an `OPEN (batch 159)` note; their
obstructions are in `OPEN.md`. Shape changes are recorded at the statement and in the report.

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345; Bing 1960 p. 215
(`doc/sources/bing1960.pdf`); Moore 1919 (`m19_schoenflies_boundary_proof`, `HPC/Moore/M19GBoundary.lean`);
the plane as a model of Moore's axioms (`mooreDecomp_ptSetoid`, `HPC/Jones/Jones55T2A.lean`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 6 and the unnumbered claims; B. Lemma 7 (restated from `Hagopian76C.lean`) -/

/- OPEN (batch 159): `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`, `hagopian76_essential_typeA'`, `hagopian76_lemma7` — not formalized. Step 5 of Lemma 6 (the limit `c` of the far ends `zᵢ` of an increasing sequence of extensions `Fᵢ` exhausting `R(X, E)`, a `δ`-homeomorphism `f` with `f(c) = zᵢ`, `L ∩ f[L] = ∅` and `f[L] ⊆ R(X, E)`) needs (a) the exhausting sequence `{Fᵢ}` itself (Lemma 4 gives that the extensions have no maximal element, not a cofinal sequence with `R(X, E) = ⋃ Fᵢ`), (b) the convergence of the far ends and `c ∉ R(X, E)`, which is a compactness argument over the chain of extensions, and (c) the disjointness `L ∩ f[L] = ∅` and `f[L] ⊆ R(X, E)`, argued in two sentences ("Since M is hereditarily unicoherent and f[L] contains zᵢ and misses w, and since Fᵢ is irreducible, the sets L and f[L] are disjoint. Since M is atriodic, it follows that f[L] is a subset of R(X, E).") whose triods are not written out. `hagopian76_essential_typeA'` needs the containment of an essential continuum in one extension, which uses (b). Lemma 7 uses Lemma 6. See `OPEN.md`, batch 159, items A and B.

-/

-- `hagopian76_closure_extUnion`: proved in batch 160, `Hagopian76E.lean`.
-- `hagopian76_lemma6`: proved in batch 160, `Hagopian76E.lean`.
-- `hagopian76_Rset_composant`: proved in batch 160, `Hagopian76E.lean`.
-- `hagopian76_essential_typeA'`: proved in batch 160, `Hagopian76E.lean`.

-- `hagopian76_lemma7`: proved in batch 162, `Hagopian76G.lean`.

end Section2

/-! ## C. Plane topology: Schoenflies, and a two-sided collar of an arc -/

/- `IsCollar` (the skeleton's definition, unchanged) is in `H76Collar.lean`. -/

/-- **Every arc in the plane has a two-sided collar.** Shape: the skeleton's, unchanged. Route
(`exists_collar_aux`, `H76Collar.lean`), which differs from the skeleton's suggestion: the ends of
`γ` are joined by an arc `β` meeting `γ` only in them (`TArc.exists_closing_arc`: both ends are
accessible from the connected complement of `γ`); an arc `β₂` from end to end through the bounded
side `I` of `γ ∪ β` (`exists_side_arc`) cuts `I` into the bounded sides `R₁` of `γ ∪ β₂` and `R₂` of
`β ∪ β₂` (`plane_split`); the collar is glued from a half-collar in `R₁ ∪ γ ∪ β₂` (Schoenflies) and
one in the unbounded side `E` of `γ ∪ β` together with `γ ∪ β` (Schoenflies after an inversion
about a point of `I`, restricted to a strip along `γ`). Near a point of the open arc, the plane is
covered by the two closed sides, since only `R₂` is missing and `γ` misses its closure. -/
theorem exists_collar {γ : unitInterval → Pt} (hγ : IsEmbedding γ) : ∃ F, IsCollar γ F :=
  exists_collar_aux hγ

/-! ## D. Lemma 8 with prescribed caps; E. Lemma 9 -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.

end Lemma9

end HPC.Hagopian
