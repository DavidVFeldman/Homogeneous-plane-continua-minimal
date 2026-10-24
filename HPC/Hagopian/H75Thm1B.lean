import HPC.Hagopian.H75Thm1A

/-!
# Batch 155, item I: Theorem 1, paragraphs 9–11 (the invariance of an interior layer)

`E ⊆ M` has an admissible map `k` with layers of void interior; `0 < r < s < t < 1`;
`Z = k⁻¹[r, t]`, `Y = k⁻¹(s)`; `ε` is at most the distance from `Z` to the end layers; `h` is a
homeomorphism of `M` moving no point by `ε` or more, and `h[Y] ∩ Y ≠ ∅`.

* `homeo_image_subset_of_meets` (**the second inclusion of paragraph 9**, unargued by Hagopian:
  `hᵢk⁻¹[[r,t]] ⊂ E`). `h[Z]` misses the end layers (choice of `ε`) and meets `E`. If `h[Z] ⊄ E`,
  then `J = E ∩ h[Z]` is a continuum (hereditary unicoherence) with `k(J) = [d', e'] ⊆ (0, 1)`, and
  `N = k⁻¹[d', e']`, `X₁ = k⁻¹[0, d']`, `X₂ = k⁻¹[e', 1]`, `X₃ = h[Z] ∪ N` satisfy the hypotheses of
  `isTriod_of_core`: a triod, against atriodicity.
* `homeo_image_layer_subset` (**paragraph 10**). Suppose `h[Y] ⊄ Y`; `k(h[Y]) = [d, e]` with `d < e`,
  and every layer `k⁻¹(u)`, `d < u < e`, lies in `h[Y]` (`layer_subset_of_meets'`). Split
  `E ∖ Y ⊆ k⁻¹[0, r] ∪ k⁻¹[t, 1] ∪ k⁻¹[r, s) ∪ k⁻¹(s, t]`. The images of the first two are closed and
  miss `h[Y]`; the images of the last two are connected subsets of `E` (paragraph 9) missing
  `k⁻¹(d, e) ⊆ h[Y]`, so each lies in `k⁻¹[0, d]` or in `k⁻¹[e, 1]`. Hence a point `y` with
  `k(y) ∈ (d, e)` is not in the closure of `h[E ∖ Y]`: a neighbourhood of `y` meets `h[E]` only in
  `h[Y]`, and pulling it back by `h`, `Y` has nonvoid interior in `E`. (Hagopian's sets `R` and `T`
  are the components of `h[E] − h[Y]` containing the images of `k⁻¹[0, s)` and `k⁻¹(s, 1]`; his
  appeal to the minimal admissible decomposition of `h[E]` is replaced by the invariance of relative
  interiors under the homeomorphism `h`, so `hagopian75_lemma3_unique` is not needed here.)
* `hagopian75_layer_invariant_aux` (**paragraph 11**): the same argument for `h⁻¹`, which moves no
  point by `ε` and also satisfies `h⁻¹[Y] ∩ Y ≠ ∅`, gives `Y ⊆ h[Y]`.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section Thm1B

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] [CompactSpace M] in
/-- **Paragraph 9, the second inclusion.** -/
theorem homeo_image_subset_of_meets (hHU : IsHereditarilyUnicoherent (univ : Set M))
    (hAT : IsAtriodic (univ : Set M)) {E : Set M} (hEc : Fold.Q78.IsContinuum E)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) {Z : Set M} (hZ : Fold.Q78.IsContinuum Z)
    (h : M ≃ₜ M) (hmeet : (E ∩ h '' Z).Nonempty)
    (hends : ∀ z ∈ Z, ∀ w : E, (k w = 0 ∨ k w = 1) → h z ≠ w) : h '' Z ⊆ E := by
  by_contra hnot
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc.1
  have hhZ := isContinuum_homeo_image h hZ
  have hJ := isContinuum_inter_of_HU hHU hEc hhZ hmeet
  set J' : Set E := Subtype.val ⁻¹' (E ∩ h '' Z)
  have hJ'c : IsCompact J' := (hJ.1.isClosed.preimage continuous_subtype_val).isCompact
  have hJ'ne : J'.Nonempty := by
    obtain ⟨z, hzE, hz⟩ := hmeet
    exact ⟨⟨z, hzE⟩, hzE, hz⟩
  obtain ⟨y₁, hy₁, hmin⟩ := hJ'c.exists_isMinOn hJ'ne hk.1.continuousOn
  obtain ⟨y₂, hy₂, hmax⟩ := hJ'c.exists_isMaxOn hJ'ne hk.1.continuousOn
  set d' := k y₁
  set e' := k y₂
  have hnotend : ∀ y ∈ J', k y ≠ 0 ∧ k y ≠ 1 := by
    intro y hy
    obtain ⟨-, z, hz, hzy⟩ := hy
    exact ⟨fun h0 => hends z hz y (Or.inl h0) hzy, fun h1 => hends z hz y (Or.inr h1) hzy⟩
  have hd'0 : 0 < d' := lt_of_le_of_ne (unitInterval.nonneg') (hnotend y₁ hy₁).1.symm
  have he'1 : e' < 1 := lt_of_le_of_ne (unitInterval.le_one') (hnotend y₂ hy₂).2
  have hde : d' ≤ e' := hmin hy₂
  set N := Subtype.val '' (k ⁻¹' Icc d' e')
  set X₁ := Subtype.val '' (k ⁻¹' Icc 0 d')
  set X₂ := Subtype.val '' (k ⁻¹' Icc e' 1)
  have hN : Fold.Q78.IsContinuum N :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hde)
  have h₁ : Fold.Q78.IsContinuum X₁ :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 hd'0.le)
  have h₂ : Fold.Q78.IsContinuum X₂ :=
    isContinuum_img hEc.1 hk isClosed_Icc isPreconnected_Icc (nonempty_Icc.2 he'1.le)
  have hJN : E ∩ h '' Z ⊆ N := by
    intro z hz
    exact ⟨⟨z, hz.1⟩, ⟨hmin hz, hmax hz⟩, rfl⟩
  have hy₁N : (y₁ : M) ∈ N := ⟨y₁, ⟨le_rfl, hde⟩, rfl⟩
  have h₃ : Fold.Q78.IsContinuum (h '' Z ∪ N) :=
    isContinuum_union hhZ hN ⟨y₁, hy₁.2, hy₁N⟩
  obtain ⟨p₀, hp₀⟩ := hk.2.1 0
  obtain ⟨p₁, hp₁⟩ := hk.2.1 1
  have hT := isTriod_of_core hN h₁ h₂ h₃
    ⟨y₁, ⟨y₁, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, hy₁N⟩
    ⟨y₂, ⟨y₂, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, ⟨y₂, ⟨hde, le_rfl⟩, rfl⟩⟩
    ⟨y₁, Or.inr hy₁N, hy₁N⟩
    (by
      rintro z ⟨hz1, hz2⟩
      obtain ⟨hzE, hk1⟩ := mem_img_iff.1 hz1
      obtain ⟨_, hk2⟩ := mem_img_iff.1 hz2
      exact mem_img_iff.2 ⟨hzE, hde.trans hk2.1, hk1.2.trans hde⟩)
    (by
      rintro z ⟨hz1, hz3 | hz3⟩
      · exact hJN ⟨img_subset _ hz1, hz3⟩
      · exact hz3)
    (by
      rintro z ⟨hz2, hz3 | hz3⟩
      · exact hJN ⟨img_subset _ hz2, hz3⟩
      · exact hz3)
    (fun hsub => by
      have := hsub ⟨p₀, show k p₀ ∈ Icc 0 d' by rw [hp₀]; exact ⟨le_rfl, hd'0.le⟩, rfl⟩
      obtain ⟨_, hk0⟩ := mem_img_iff.1 this
      have : d' ≤ k p₀ := hk0.1
      rw [hp₀] at this
      exact absurd this (not_le.2 hd'0))
    (fun hsub => by
      have := hsub ⟨p₁, show k p₁ ∈ Icc e' 1 by rw [hp₁]; exact ⟨he'1.le, le_rfl⟩, rfl⟩
      obtain ⟨_, hk1⟩ := mem_img_iff.1 this
      have : k p₁ ≤ e' := hk1.2
      rw [hp₁] at this
      exact absurd this (not_le.2 he'1))
    (fun hsub => hnot fun z hz => img_subset _ (hsub (Or.inl hz)))
  exact hAT _ (subset_univ _) hT

end Thm1B

end HPC.Hagopian
