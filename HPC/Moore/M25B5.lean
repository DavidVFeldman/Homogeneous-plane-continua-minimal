import HPC.Moore.M25BDefs

/-!
# Batch 146, item C: Moore 1925, Theorems 5–8 (p. 420)

Each theorem is an instance, in the space of elements (metrizable by `quotient_metrizable_plane`),
of the general results of `CutArc.lean`:

* Theorem 5: `IsCutArc.isConnected_diff_ends` (a cut-point arc is an embedded `[0, 1]`).
* Theorem 6: a closed connected nondegenerate subset of an embedded arc is the image of an interval
  (`eq_image_Icc_of_subset_range`), hence a cut-point arc (`isCutArc_image_Icc`).
* Theorem 7 (with `x` for the printed `p`): the sub-arcs of `pq` having `x` as an interior element
  are the images of intervals `[s, t] ∋ u` with `s < u < t` (`ends_of_image_Icc`), and these form a
  neighbourhood base of `x` in `pq`.
* Theorem 8: Nadler 6.7 (`exists_nonCut_diff`). Moore's own proof (pp. 420–421) is followed in
  substance: Nadler's non-cut point theorem (batch 94) is what replaces his appeal to Theorem 5 for
  "`K₂ + p` would be a simple continuous arc".

`not_separatesPlane_ptsOf` is `isConnected_ptsOf` (batch 145): the point set of a connected set of
elements is connected.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

variable {r : Setoid Pt}

section M25B

variable (hG : MooreDecomp r)
include hG

/-- Sets of elements and their point sets: if `H` does not separate `G`, then `H̄` does not separate
`S` (used in Theorems 11 and 13: "neither `a` nor `b` separates `G` and therefore neither `ā` nor `b̄`
separates `S`"). -/
theorem not_separatesPlane_ptsOf {H : Set (Quotient r)} (hH : IsConnected Hᶜ) :
    ¬ SeparatesPlane (ptsOf r H) := by
  unfold SeparatesPlane
  rw [not_not, ← ptsOf_compl]
  exact isConnected_ptsOf hG hH

/-- **Theorem 6** (p. 420). Every closed and connected subset of a simple continuous arc which
contains more than one element is itself a simple continuous arc. (No proof in the text.) -/
theorem m25_theorem6 {A B : Quotient r} {K L : Set (Quotient r)} (hK : IsArcElt A B K)
    (hLK : L ⊆ K) (hL : IsClosed L) (hLc : IsConnected L) (hLn : L.Nontrivial) :
    ∃ a b, IsArcElt a b L := by
  haveI := quotient_metrizable_plane hG
  obtain ⟨f, hf, hrange, -, -⟩ := hK.isCutArc.exists_embedding
  obtain ⟨s, t, hst, rfl⟩ := eq_image_Icc_of_subset_range hf (hrange ▸ hLK) hL
    hLc.isPreconnected hLn
  exact ⟨_, _, (isCutArc_image_Icc hf hst).isArcElt hL
    (hK.2.2.2.1.subset (ptsOf_mono hLK))⟩

end M25B

end HPC.Moore
