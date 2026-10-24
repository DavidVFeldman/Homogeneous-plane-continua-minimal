import HPC.Plane.Ingram68Core

/-!
# Batch 132, Part II (2): the property (∗) by the direct route

`ingramStar_holds : IngramStar S`, without circle-likeness (COMMISSION-batch132 §2, "alternative
route"). Let `M ⊊ Y ∪ A` be a subcontinuum and `z ∈ (Y ∪ A) ∖ M`; write `Y ∩ A = H ⊔ K`
(Ingram's Lemma 1).
* `z ∈ Y ∖ A` (or `A ∖ Y`): `isUnicoherent_of_not_mem_diff`. Cutting `Y` at `z` (cut wire,
  irreducibility from Lemma 2) puts `M` inside a hereditarily unicoherent continuum
  `C_H ∪ A ∪ C_K`.
* `z ∈ H` (or `K`) and `A ∖ Y ⊆ M`: `isUnicoherent_of_not_mem_piece`. Terminality of `H` in `A`
  (Lemma 2) lets `A` be replaced by a subcontinuum `A*` missing `z` with `Y ∪ A* = Y ∪ A`, and the
  first case applies.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **The cut-wire theorem.** If no subcontinuum of the closed set `F`
meets both of the closed sets `E₁, E₂ ⊆ F`, then `F` splits into two disjoint closed sets, one
containing `E₁` and the other `E₂`. (Components are quasi-components in a compact Hausdorff
space: `connectedComponent_eq_iInter_isClopen`.) -/
theorem exists_split_of_no_continuum {F E₁ E₂ : Set S} (hF : IsClosed F) (h₁ : E₁ ⊆ F)
    (h₂ : E₂ ⊆ F) (c₁ : IsClosed E₁) (c₂ : IsClosed E₂)
    (h : ∀ C : Set S, Fold.Q78.IsContinuum C → C ⊆ F → (C ∩ E₁).Nonempty →
      (C ∩ E₂).Nonempty → False) :
    ∃ F₁ F₂ : Set S, IsClosed F₁ ∧ IsClosed F₂ ∧ Disjoint F₁ F₂ ∧ F = F₁ ∪ F₂ ∧ E₁ ⊆ F₁ ∧
      E₂ ⊆ F₂ := by
  classical
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  set E₁' : Set F := Subtype.val ⁻¹' E₁ with hE₁'
  set E₂' : Set F := Subtype.val ⁻¹' E₂ with hE₂'
  have hE₂c : IsCompact E₂' := (c₂.preimage continuous_subtype_val).isCompact
  have hE₁c : IsCompact E₁' := (c₁.preimage continuous_subtype_val).isCompact
  have hW : ∀ e ∈ E₁', ∃ W : Set F, IsClopen W ∧ e ∈ W ∧ Disjoint W E₂' := by
    intro e he
    have hC : E₂' ∩ ⋂ s : { s : Set F // IsClopen s ∧ e ∈ s }, (s : Set F) = ∅ := by
      rw [← connectedComponent_eq_iInter_isClopen]
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hz2 hzC
      exact h (Subtype.val '' connectedComponent e)
        ⟨(isClosed_connectedComponent.isCompact).image continuous_subtype_val,
          isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn⟩
        (by rintro _ ⟨w, -, rfl⟩; exact w.2) ⟨e, ⟨e, mem_connectedComponent, rfl⟩, he⟩
        ⟨z, ⟨z, hzC, rfl⟩, hz2⟩
    obtain ⟨u, hu⟩ := hE₂c.elim_finite_subfamily_closed
      (fun s : { s : Set F // IsClopen s ∧ e ∈ s } => (s : Set F)) (fun s => s.2.1.isClosed) hC
    refine ⟨⋂ i ∈ u, (i : Set F), isClopen_biInter_finset fun i _ => i.2.1,
      mem_iInter₂.mpr fun i _ => i.2.2, ?_⟩
    rw [disjoint_iff_inter_eq_empty, inter_comm]
    exact hu
  choose! W hWc hWe hWd using hW
  obtain ⟨t, htE, htfin, hcover⟩ := hE₁c.elim_finite_subcover_image (b := E₁') (c := W)
    (fun e he => (hWc e he).isOpen) (fun e he => mem_biUnion he (hWe e he))
  set U : Set F := ⋃ i ∈ t, W i with hU_def
  have hU : IsClopen U :=
    ⟨htfin.isClosed_biUnion fun i hi => (hWc i (htE hi)).isClosed,
      isOpen_biUnion fun i hi => (hWc i (htE hi)).isOpen⟩
  have hUd : Disjoint U E₂' := by
    rw [hU_def, disjoint_iUnion₂_left]
    exact fun i hi => hWd i (htE hi)
  refine ⟨Subtype.val '' U, Subtype.val '' Uᶜ,
    (hU.isClosed.isCompact.image continuous_subtype_val).isClosed,
    (hU.compl.isClosed.isCompact.image continuous_subtype_val).isClosed,
    (disjoint_image_iff Subtype.val_injective).mpr disjoint_compl_right, ?_, ?_, ?_⟩
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · intro x hx
    exact ⟨⟨x, h₁ hx⟩, hcover hx, rfl⟩
  · intro x hx
    exact ⟨⟨x, h₂ hx⟩, fun h' => disjoint_left.mp hUd h' hx, rfl⟩


end HPC.Plane
