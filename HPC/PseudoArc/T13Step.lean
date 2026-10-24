import HPC.PseudoArc.T13Chains
import HPC.Fold.Theorem4Pair

/-!
# Batch 81: one step of Bing's sequence `E_1, E_2, …`, and the description from `R` to `S`

* `Chain.exists_blockChain`: Theorem 4 (two-link basepoints, `Fold.theorem4_pair`) applied to a
  subchain from `R` to `S` that meets both end links of the coarse chain gives a block
  consolidation of the whole fine chain that is a chain from `R` to `S`, each block inside three
  consecutive coarse links.
* `Description.exists_step`: for every level `L` there is a chain `F` from `R` to `S`, a
  consolidation of some deeper level, the closure of each of whose links lies in a link of level
  `L`, with mesh at most `1/(L+1)`. (Lebesgue number for (Q2)'s "closure inside a link".)
* `Description.exists_description_from'`: iterating the step gives a description of `M` from `R`
  to `S`.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n m : ℕ}

theorem IsFrom.reverse {D : Chain X n} {R S : X} (h : D.IsFrom R S) : D.reverse.IsFrom S R := by
  obtain ⟨hn, hR, hS, hRo, hSo⟩ := h
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · rw [reverse_link]
    convert hS using 2
  · rw [reverse_link]
    convert hR using 2
    ext; simp only [Fin.val_rev]; omega
  · intro i hi
    rw [reverse_link] at hi
    have := hSo _ hi
    simp only [Fin.ext_iff, Fin.val_rev] at this
    ext; simp only; have := i.isLt; omega
  · intro i hi
    rw [reverse_link] at hi
    have := hRo _ hi
    simp only [Fin.ext_iff, Fin.val_rev] at this
    ext; simp only; have := i.isLt; omega

theorem IsConsolidationOf.reverse {F : Chain X m} {D : Chain X n} (h : F.IsConsolidationOf D) :
    F.reverse.IsConsolidationOf D :=
  ⟨h.1.reverse_right, fun t => h.2 (Fin.rev t)⟩

theorem IsConsolidationOf.union_eq {F : Chain X m} {D : Chain X n} (h : F.IsConsolidationOf D) :
    F.union = D.union := by
  refine Subset.antisymm ?_ (union_subset_of_refines h.1)
  intro z hz
  obtain ⟨u, hu⟩ := mem_iUnion.mp hz
  obtain ⟨S, hS⟩ := h.2 u
  rw [hS] at hu
  obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp hu
  exact mem_iUnion.mpr ⟨i, hi⟩

/-- Points of links that meet are within `2ε`. -/
theorem dist_le_two {D : Chain X n} {ε : ℝ} (hbdd : ∀ t, Bornology.IsBounded (D.link t))
    (hdiam : ∀ t, diam (D.link t) ≤ ε) {s t : Fin n} (hst : (D.link s ∩ D.link t).Nonempty)
    {x y : X} (hx : x ∈ D.link s) (hy : y ∈ D.link t) : dist x y ≤ 2 * ε := by
  obtain ⟨z, hzs, hzt⟩ := hst
  have h1 := dist_le_diam_of_mem (hbdd s) hx hzs
  have h2 := dist_le_diam_of_mem (hbdd t) hzt hy
  linarith [dist_triangle x z y, hdiam s, hdiam t]

/-- Two points of three consecutive links are within `3ε`. -/
theorem dist_le_of_mem_unionRange {D : Chain X n} {ε : ℝ}
    (hbdd : ∀ t, Bornology.IsBounded (D.link t)) (hdiam : ∀ t, diam (D.link t) ≤ ε) {j : ℕ}
    {x y : X} (hx : x ∈ D.unionRange j 3) (hy : y ∈ D.unionRange j 3) : dist x y ≤ 3 * ε := by
  obtain ⟨s, hs1, hs2, hsn, hxs⟩ := mem_unionRange.mp hx
  obtain ⟨t, ht1, ht2, htn, hyt⟩ := mem_unionRange.mp hy
  have hε : 0 ≤ ε := le_trans diam_nonneg (hdiam ⟨s, hsn⟩)
  by_cases hclose : s ≤ t + 1 ∧ t ≤ s + 1
  · have := dist_le_two hbdd hdiam ((D.adjacent_iff ⟨s, hsn⟩ ⟨t, htn⟩).mpr hclose) hxs hyt
    linarith
  · -- `s` and `t` are two apart; use the middle link
    have hw : (s + t) / 2 < n := by omega
    obtain ⟨z, hzs, hzw⟩ := (D.adjacent_iff ⟨s, hsn⟩ ⟨(s + t) / 2, hw⟩).mpr (by simp only; omega)
    have h1 := dist_le_diam_of_mem (hbdd _) hxs hzs
    have h2 := dist_le_two hbdd hdiam ((D.adjacent_iff ⟨(s + t) / 2, hw⟩ ⟨t, htn⟩).mpr
      (by simp only; omega)) hzw hyt
    linarith [dist_triangle x z y, hdiam ⟨s, hsn⟩]

/-- **Theorem 4 applied to a subchain from `R` to `S`.** -/
theorem exists_blockChain {k : ℕ} (hk : 5 ≤ k) {E : Chain X n} {D : Chain X k}
    (hcr : E.IsCrookedIn' D) {a b : Fin n} (hab : a ≤ b) {R S : X}
    (hsub : (E.sub a b hab).IsFrom R S) {t₁ t₂ : Fin n} (ht₁ : a ≤ t₁ ∧ t₁ ≤ b)
    (ht₂ : a ≤ t₂ ∧ t₂ ≤ b) (hm₁ : (E.link t₁ ∩ D.link ⟨0, by omega⟩).Nonempty)
    (hm₂ : (E.link t₂ ∩ D.link ⟨k - 1, by omega⟩).Nonempty) :
    ∃ (q : ℕ) (β : Fin n → Fin q) (hβ : IsBlockMap β), (E.ofBlocks β hβ).IsFrom R S ∧
      ∀ u, ∃ j : ℕ, (E.ofBlocks β hβ).link u ⊆ D.unionRange j 3 := by
  classical
  -- the subchain is long
  have hwide : a.val + 2 ≤ b.val := by
    obtain ⟨u₁, hu₁⟩ := hcr.1 t₁
    obtain ⟨u₂, hu₂⟩ := hcr.1 t₂
    have c1 := (D.adjacent_iff u₁ ⟨0, by omega⟩).mp (hm₁.mono (inter_subset_inter_left _ hu₁))
    have c2 := (D.adjacent_iff u₂ ⟨k - 1, by omega⟩).mp (hm₂.mono (inter_subset_inter_left _ hu₂))
    simp only at c1 c2
    have hfar : ¬ (t₁.val ≤ t₂.val + 1 ∧ t₂.val ≤ t₁.val + 1) := by
      intro hc
      have := (D.adjacent_iff u₁ u₂).mp
        (((E.adjacent_iff t₁ t₂).mpr hc).mono (inter_subset_inter hu₁ hu₂))
      have := u₂.isLt
      omega
    rw [Fin.le_def] at ht₁ ht₂
    omega
  obtain ⟨hn', hRa, hSb, hRo, hSo⟩ := hsub
  have hRa' : R ∈ E.link a := by simpa [sub] using hRa
  have hSb' : S ∈ E.link b := by
    have : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
      ext; simp only; rw [Fin.le_def] at hab; omega
    simp only [sub] at hSb
    rwa [this] at hSb
  have hRlinks : ∀ t : Fin n, R ∈ E.link t → t.val + 1 = a.val ∨ t.val = a.val := by
    intro t ht
    have c := E.val_close_of_mem ht hRa'
    by_contra hcon
    have hta : t.val = a.val + 1 := by omega
    have := hRo ⟨1, by omega⟩ (by
      simp only [sub]
      have : (⟨a.val + 1, by omega⟩ : Fin n) = t := by ext; simp only; omega
      rw [this]; exact ht)
    simp [Fin.ext_iff] at this
  have hSlinks : ∀ t : Fin n, S ∈ E.link t → t.val = b.val ∨ t.val = b.val + 1 := by
    intro t ht
    have c := E.val_close_of_mem ht hSb'
    by_contra hcon
    have htb : t.val + 1 = b.val := by omega
    have := hSo ⟨b.val - a.val - 1, by omega⟩ (by
      simp only [sub]
      have : (⟨a.val + (b.val - a.val - 1), by omega⟩ : Fin n) = t := by ext; simp only; omega
      rw [this]; exact ht)
    simp only [Fin.ext_iff] at this
    omega
  have hbn := b.isLt
  have hrn : a.val - 1 < n := by omega
  have hr'n : a.val - 1 + 1 < n := by omega
  have hs'n : min (b.val + 1) (n - 1) - 1 < n := by omega
  have hsn : min (b.val + 1) (n - 1) < n := by omega
  obtain ⟨q, β, hβ, h0, h0', hq', hq⟩ := Fold.theorem4_pair (k := k) (by omega) hcr
    ⟨a.val - 1, hrn⟩ ⟨a.val - 1 + 1, hr'n⟩
    ⟨min (b.val + 1) (n - 1) - 1, hs'n⟩ ⟨min (b.val + 1) (n - 1), hsn⟩
    rfl (by simp only; omega) (Fin.le_def.mpr (by simp only; omega))
    ⟨t₁, Fin.le_def.mpr (by rw [Fin.le_def] at ht₁; simp only; omega),
      Fin.le_def.mpr (by rw [Fin.le_def] at ht₁; simp only; omega), hm₁⟩
    ⟨t₂, Fin.le_def.mpr (by rw [Fin.le_def] at ht₂; simp only; omega),
      Fin.le_def.mpr (by rw [Fin.le_def] at ht₂; simp only; omega), hm₂⟩
  refine ⟨q, β, hβ, ?_, hq.2⟩
  · have hq0 : 0 < q := Fin.pos (β a)
    rw [Fold.Q78.isFrom_ofBlocks_iff E β hβ hq0]
    refine ⟨⟨a, hRa'⟩, fun t ht => ?_, ⟨b, hSb'⟩, fun t ht => ?_⟩
    · rcases hRlinks t ht with h | h
      · have : t = ⟨a.val - 1, hrn⟩ := by ext; simp only; omega
        rw [this]; exact h0
      · by_cases ha0 : a.val = 0
        · have : t = ⟨a.val - 1, hrn⟩ := by ext; simp only; omega
          rw [this]; exact h0
        · have : t = ⟨a.val - 1 + 1, hr'n⟩ := by ext; simp only; omega
          rw [this]; exact h0'
    · have htn := t.isLt
      rcases hSlinks t ht with h | h
      · by_cases hb1 : b.val + 1 < n
        · have : t = ⟨min (b.val + 1) (n - 1) - 1, hs'n⟩ := by ext; simp only; omega
          rw [this]; exact hq'
        · have : t = ⟨min (b.val + 1) (n - 1), hsn⟩ := by ext; simp only; omega
          rw [this]; exact hq.1
      · have : t = ⟨min (b.val + 1) (n - 1), hsn⟩ := by ext; simp only; omega
        rw [this]; exact hq.1

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q)

end Description

end HPC
