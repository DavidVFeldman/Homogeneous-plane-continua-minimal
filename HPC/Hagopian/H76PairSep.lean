import HPC.Hagopian.H76Crosscut

/-!
# Batch 168, item B: a crossing continuum separates `D′` along the vertical

In the domain `D′` of `rect_domain_aux` (under the arc `I` from `r = (a, r₂)` to `s = (b, s₂)`):
* `rect_domain_crosscut_arc`: `rect_domain_crosscut` with the low vertical segment replaced by any
  arc `T` from a bottom point `(x₀, 0)` to a point `w` of `I`, with `T − {(x₀, 0), w} ⊆ D′`. Same
  proof: one Jordan curve `J = I_L ∪ {a} × [0, r₂] ∪ [a, x₀] × {0} ∪ T`.
* `seg_subset_rect_domain`: the vertical segment from the bottom up to the lowest point of `I` over
  `x₀` lies in `D′`.
* `rect_domain_crossing_separates`: a connected `B ⊆ D′` whose closure misses `I` and the bottom
  and meets both open side edges separates, in `D′`, a point `(x₀, u₁)` of the vertical below
  `Cl B` from a point `(x₀, u₂)` above it. Proof: a connected `S ⊆ D′ − Cl B` through both points
  gives a polygonal arc from `(x₀, u₁)` to `(x₀, u₂)` in the component of `D′ − Cl B`; with the two
  vertical segments it gives (by loop erasure) an arc `T` from `(x₀, 0)` to `(x₀, w₂)` missing
  `Cl B`, and `rect_domain_crosscut_arc` applies to `B`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- **The low vertical segment lies in `D′`.** -/
theorem seg_subset_rect_domain {a b c : ℝ} (hab : a < b) {r s : ℝ × ℝ} {I D : Set (ℝ × ℝ)}
    (hI : TArc r s I) (hIR : I ⊆ Icc a b ×ˢ Ioc 0 c) (hDo : IsOpen D)
    (hDR : D ⊆ Ioo a b ×ˢ Ioo 0 c)
    (hDf : frontier D = I ∪ Icc a b ×ˢ {0} ∪ ({a} : Set ℝ) ×ˢ Icc 0 r.2 ∪
      ({b} : Set ℝ) ×ˢ Icc 0 s.2) {x₀ w₂ : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hw₂ : 0 < w₂)
    (hsegI : Disjoint (({x₀} : Set ℝ) ×ˢ Ioo 0 w₂) I) :
    ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂ ⊆ D := by
  obtain ⟨c₀, hc₀, -, hc₀I⟩ := exists_height_below hI.isCompact fun z hz => (hIR hz).2.1
  have hlow := rect_domain_low (r := r) (s := s) hab hDR hDf hc₀ fun z hz => (hc₀I z hz).le
  set seg := ({x₀} : Set ℝ) ×ˢ Ioo 0 w₂
  have hsegc : IsPreconnected seg :=
    ((convex_singleton x₀).prod (convex_Ioo 0 w₂)).isPreconnected
  have hsub : seg ⊆ D ∪ (closure D)ᶜ := by
    rintro z ⟨hx, hy⟩
    by_cases hzD : z ∈ D
    · exact Or.inl hzD
    · right
      intro hzcl
      have hzf : z ∈ frontier D := ⟨hzcl, by rwa [hDo.interior_eq]⟩
      rw [hDf] at hzf
      have hx' : z.1 = x₀ := hx
      rcases hzf with ((hzI | ⟨-, hy0⟩) | ⟨hxa, -⟩) | ⟨hxb, -⟩
      · exact disjoint_left.1 hsegI ⟨hx, hy⟩ hzI
      · have : z.2 = 0 := hy0
        linarith [hy.1]
      · have : z.1 = a := hxa
        linarith [hx₀.1]
      · have : z.1 = b := hxb
        linarith [hx₀.2]
  have hDcl : Disjoint D (closure D)ᶜ := disjoint_compl_right.mono_left subset_closure
  rcases hsegc.subset_or_subset hDo isClosed_closure.isOpen_compl hDcl hsub with h | h
  · exact h
  · exfalso
    have hm0 : 0 < min c₀ w₂ := lt_min hc₀ hw₂
    have hm1 := min_le_left c₀ w₂
    have hm2 := min_le_right c₀ w₂
    have hu0 : 0 < min c₀ w₂ / 2 := by linarith
    have hu1 : min c₀ w₂ / 2 < c₀ := by linarith
    have hu2 : min c₀ w₂ / 2 < w₂ := by linarith
    have hm : ((x₀, min c₀ w₂ / 2) : ℝ × ℝ) ∈ D := hlow ⟨hx₀, hu0, hu1⟩
    exact h ⟨mem_singleton x₀, hu0, hu2⟩ (subset_closure hm)

end HPC.Hagopian
