import HPC.Plane.Composant91
import HPC.Chains.Consolidation

/-!
# Batch 91: Bing's surgery for Theorem 10 (Duke 1951, p. 659), formally

Bing's proof of Theorem 10 ends with a surgery: a chain `F` covering a subcontinuum `M''` through
`p` (refining `D`, `p` in its first link and in the closure of no other) is extended to a chain
covering `M`, by cutting `M` at a small open set `N` near a point of `M''` in the last link of `F`
and in the end link `d_1` of `D`, separating `M ∖ N` into a clopen piece `H` (containing the
component of `p`, hence covered by `F`) and the rest `K` (covered by `D`).

`theorem10_1951_of_lastLink` proves the surgery in a form that needs less than Bing's text:

* `M''` need **not** be proper and need **not** meet every link of `D`;
* the point `y` need only lie in `M'' ∩ f_k ∩ d_1` and differ from `p` — it may lie in the closure
  of `f_{k-1}` and of `d_2`: the last link of `F` is merged with `N`, and `cl N` is removed from
  the links `d_2, d_3, …` of the `D`-part;
* only condition B (which follows from condition A) is used.

`theorem10_1951_of_lastLink'` is the mirror form (the last link of `D` instead of the first).
So Theorem 10 follows from Bing's unestablished sentence in the following form: **some**
subcontinuum `M''` through `p` has a chain `F` with the properties of Theorem 10 whose last link
meets `M'' ∩ (d_1 ∪ d_m)` at a point other than `p`.
-/

namespace HPC.Plane

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- **Separating a compact set along the component of a point.** If every preconnected subset of
the compact set `S` through `p` lies in the open set `O`, then `S` splits into two disjoint compact
pieces, the one containing `p` inside `O`. (In the compact space `S` the component of `p` is the
intersection of the clopen sets containing it; by compactness one of them lies in `O`.) -/
theorem exists_clopen_split {S : Set X} (hS : IsCompact S) {p : X} (hp : p ∈ S) {O : Set X}
    (hO : IsOpen O) (hC : ∀ A : Set X, IsPreconnected A → A ⊆ S → p ∈ A → A ⊆ O) :
    ∃ H K : Set X, IsCompact H ∧ IsCompact K ∧ H ∪ K = S ∧ Disjoint H K ∧ p ∈ H ∧ H ⊆ O := by
  classical
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  set p' : S := ⟨p, hp⟩
  have hcomp : Subtype.val '' connectedComponent p' ⊆ O :=
    hC _ (isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn)
      (by rintro _ ⟨z, -, rfl⟩; exact z.2) ⟨p', mem_connectedComponent, rfl⟩
  set Z : Set S := (Subtype.val ⁻¹' O)ᶜ with hZ_def
  have hZc : IsCompact Z := ((hO.preimage continuous_subtype_val).isClosed_compl).isCompact
  have hCZ : Z ∩ ⋂ s : { s : Set S // IsClopen s ∧ p' ∈ s }, (s : Set S) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzZ hzC
    exact hzZ (hcomp ⟨z, hzC, rfl⟩)
  obtain ⟨u, hu⟩ := hZc.elim_finite_subfamily_closed
    (fun s : { s : Set S // IsClopen s ∧ p' ∈ s } => (s : Set S)) (fun s => s.2.1.isClosed) hCZ
  set W : Set S := ⋂ i ∈ u, (i : Set S) with hW_def
  have hW : IsClopen W := isClopen_biInter_finset fun i _ => i.2.1
  have hpW : p' ∈ W := mem_iInter₂.mpr fun i _ => i.2.2
  refine ⟨Subtype.val '' W, Subtype.val '' Wᶜ, hW.isClosed.isCompact.image continuous_subtype_val,
    hW.compl.isClosed.isCompact.image continuous_subtype_val, ?_, ?_, ⟨p', hpW, rfl⟩, ?_⟩
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    rw [Subtype.val_injective hab] at hb
    exact hb ha
  · rintro _ ⟨z, hz, rfl⟩
    by_contra hzO
    have : z ∈ Z ∩ W := ⟨hzO, hz⟩
    rw [hu] at this
    exact this

end HPC.Plane
