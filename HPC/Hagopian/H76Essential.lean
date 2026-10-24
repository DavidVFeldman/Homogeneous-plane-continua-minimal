import HPC.Hagopian.H76Lemma6

/-!
# Batch 160, item A: "every continuum essential to `R(E)` is of type A′ (Lemma 5)" (p. 343)

Let `H` be essential to `R(E)`: a continuum in `R(E) = R(X, E) ∪ R(Z, E)` meeting two layers of some
extension of `E`.

* If `H ⊆ R(X, E)`, then `H` lies in one extension `G` away from `X` (`exists_ext_of_subset`), and
  meets two layers of `G` (the layers of `E`, and of a smaller extension, are layers of `G`; if the
  given extension is away from `Z`, the two points lie in `E`, since the two sides meet only in `E`,
  `ext_inter_subset`). Then `isTypeA'_of_subcontinuum` with Lemma 5 (`essential_typeA'_of_subset`).
* If `H ⊆ R(Z, E)`: the same for the reversed map.
* Otherwise `H` meets `X` and `Z` (absorption), so `H ⊇ E`; `H ∩ R(X, E)` lies in one extension `K`
  away from `X`, and `H ∩ R(Z, E)` in one extension `Q` away from `Z` (`exists_ext_cover`; otherwise
  `H ∪ F₀ ⊇ Cl R(E)` and `H = Cl R(E)`, which is impossible as `R(E)` is not closed). With `b` a
  point of `H ∩ K` farthest out in `K` and `a` a point of `H ∩ Q` farthest out in `Q`, `H` is
  irreducible between `a` and `b` (Lemma 5 in `K` and `Q`), and `H ⊆ (H ∩ Q) ∪ (H ∩ K)` with
  `a ∉ K`, `b ∉ Q`; Kuratowski's criterion with the 1975 ¶2 argument (`isTypeA'_of_decomposable`,
  `no_indecomposable_interior_aux`) makes `H` of type A′ (`essential_typeA'_two_sided`).

The containment of report 158 §1.C (an essential continuum lies in one extension) is
`exists_ext_of_subset`; it uses that `R(X, E)` is not closed (`not_isClosed_extUnion`, from Lemma 6),
not the point `c` of step 5.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Ess

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- Lemma 5, in the form used here. -/
theorem lsc_of_minimalAdmissible (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {G : Set M} {d : G → unitInterval} (hd : IsMinimalAdmissible G d) :
    ∀ x, LSCAt (Setoid.ker d) x := by
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp hd.isCompact
  exact (hagopian76_lemma5 hX hi hd).2

end Ess

end HPC.Hagopian
