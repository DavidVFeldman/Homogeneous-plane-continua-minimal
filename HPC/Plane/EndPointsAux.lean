import HPC.Plane.Snake51
import HPC.PseudoArc.Theorem14

/-!
# Batch 85: tools for the end-point theorems of Bing 1951, §5

* **Weak chains.** A finite family of open sets in which links two or more apart are disjoint,
  but adjacent links need not meet. `exists_chain_of_weak`: the links of a weak chain that meet
  a preconnected set `C` covered by it form a run of consecutive indices, and that run is a chain
  (`HPC.Chain`) covering `C`. Surgery on chains is done with weak chains and then trimmed.
* **Limits of finely chained sets inside a compact set** (`isPreconnected_limSup_of_compact`):
  the batch-81 lemma `HPC.T13.isPreconnected_limSup` without the compact-ambient-space
  hypothesis, the sets being assumed to lie in one compact set.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

/-! ## Weak chains -/

/-- A splitting of a weak chain: if the links before `c₁` are disjoint from the links from `c₂`
on, a preconnected set covered by the two groups and meeting the first lies in the first. -/
theorem weak_split {n : ℕ} {L : ℕ → Set X} (hLo : ∀ i, IsOpen (L i)) {C : Set X}
    (hC : IsPreconnected C) {c₁ c₂ : ℕ}
    (hdisj : ∀ i j, i < c₁ → c₂ ≤ j → j < n → Disjoint (L i) (L j))
    (hcov : C ⊆ (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) ∪ (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j))
    {a b : ℕ} (ha : a < n ∧ a < c₁) (hb : b < n ∧ c₂ ≤ b) (hCa : (L a ∩ C).Nonempty)
    (hCb : (L b ∩ C).Nonempty) : False := by
  have hU : IsOpen (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hLo i
  have hV : IsOpen (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hLo i
  have hUV : Disjoint (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) := by
    rw [Set.disjoint_iUnion_left]; intro i; rw [Set.disjoint_iUnion_left]; intro hi
    rw [Set.disjoint_iUnion_right]; intro j; rw [Set.disjoint_iUnion_right]; intro hj
    exact hdisj i j hi.2 hj.2 hj.1
  obtain ⟨z, hzL, hzC⟩ := hCa
  have hsub := hC.subset_left_of_subset_union hU hV hUV hcov
    ⟨z, hzC, mem_iUnion₂.mpr ⟨a, ha, hzL⟩⟩
  obtain ⟨w, hwL, hwC⟩ := hCb
  exact Set.disjoint_left.mp hUV (hsub hwC) (mem_iUnion₂.mpr ⟨b, hb, hwL⟩)

/-- **Trimming a weak chain.** Let `L 0, …, L (n-1)` be open sets with `L i ∩ L j = ∅` whenever
`j ≥ i + 2`, covering a preconnected set `C`, and let `L i₀` meet `C`. The links meeting `C` are
exactly those with index in a run `[a, a + k)` containing `i₀`, and they form a chain covering
`C`. -/
theorem exists_chain_of_weak {n : ℕ} (L : ℕ → Set X) (hLo : ∀ i, IsOpen (L i))
    (hweak : ∀ i j, i + 2 ≤ j → j < n → Disjoint (L i) (L j)) {C : Set X} (hC : IsPreconnected C)
    (hcov : C ⊆ ⋃ i, ⋃ (_ : i < n), L i) {i₀ : ℕ} (hi₀ : i₀ < n) (hCi₀ : (L i₀ ∩ C).Nonempty) :
    ∃ (a k : ℕ) (E : Chain X k), a ≤ i₀ ∧ i₀ < a + k ∧ a + k ≤ n ∧
      (∀ t : Fin k, E.link t = L (a + t)) ∧ C ⊆ E.union ∧
      (∀ t : Fin k, (E.link t ∩ C).Nonempty) ∧
      (∀ i, i < n → (L i ∩ C).Nonempty → a ≤ i ∧ i < a + k) := by
  classical
  set S : Finset ℕ := (Finset.range n).filter (fun i => (L i ∩ C).Nonempty) with hS
  have hi₀S : i₀ ∈ S := by simp [hS, hi₀, hCi₀]
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  set a := S.min' hSne with ha
  set b := S.max' hSne with hb
  have haS : a ∈ S := S.min'_mem hSne
  have hbS : b ∈ S := S.max'_mem hSne
  have hmemS : ∀ {i}, i ∈ S ↔ i < n ∧ (L i ∩ C).Nonempty := by
    intro i; simp [hS]
  have hai₀ : a ≤ i₀ := S.min'_le _ hi₀S
  have hi₀b : i₀ ≤ b := S.le_max' _ hi₀S
  have hbn : b < n := (hmemS.mp hbS).1
  -- a covering statement split at thresholds
  have cov_split : ∀ c₁ c₂, c₁ ≤ c₂ → (∀ i, c₁ ≤ i → i < c₂ → i < n → L i ∩ C = ∅) →
      C ⊆ (⋃ i, ⋃ (_ : i < n ∧ i < c₁), L i) ∪ (⋃ j, ⋃ (_ : j < n ∧ c₂ ≤ j), L j) := by
    intro c₁ c₂ _ hgap z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
    by_cases h1 : i < c₁
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, ⟨hi, h1⟩, hzi⟩)
    by_cases h2 : c₂ ≤ i
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, h2⟩, hzi⟩)
    exfalso
    have := hgap i (by omega) (by omega) hi
    exact (this ▸ (⟨hzi, hz⟩ : z ∈ L i ∩ C) : z ∈ (∅ : Set X))
  -- every index between `a` and `b` meets `C`
  have hfill : ∀ i, a ≤ i → i ≤ b → (L i ∩ C).Nonempty := by
    intro i hai hib
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hai' : a < i := lt_of_le_of_ne hai (fun h => by
      have := (hmemS.mp haS).2; rw [h, hne] at this; exact Set.not_nonempty_empty this)
    have hib' : i < b := lt_of_le_of_ne hib (fun h => by
      have := (hmemS.mp hbS).2; rw [← h, hne] at this; exact Set.not_nonempty_empty this)
    exact weak_split hLo hC (c₁ := i) (c₂ := i + 1)
      (fun i' j hi' hj hjn => hweak i' j (by omega) hjn)
      (cov_split i (i + 1) (by omega) (fun i' h1 h2 _ => by
        rw [show i' = i by omega]; exact hne))
      ⟨by omega, hai'⟩ ⟨hbn, by omega⟩ (hmemS.mp haS).2 (hmemS.mp hbS).2
  refine ⟨a, b - a + 1, ⟨fun t => L (a + t), fun t => hLo _, ?_⟩, hai₀, by omega, by omega,
    fun t => rfl, ?_, ?_, ?_⟩
  · intro t u
    have ht := t.isLt
    have hu := u.isLt
    constructor
    · intro hne
      by_contra hfar
      rcases le_total (t : ℕ) u with h | h
      · exact (Set.nonempty_iff_ne_empty.mp hne)
          (Set.disjoint_iff_inter_eq_empty.mp (hweak (a + t) (a + u) (by omega) (by omega)))
      · have hne' : (L (a + u) ∩ L (a + t)).Nonempty := by
          rw [Set.inter_comm]; exact hne
        exact (Set.nonempty_iff_ne_empty.mp hne')
          (Set.disjoint_iff_inter_eq_empty.mp (hweak (a + u) (a + t) (by omega) (by omega)))
    · intro hclose
      -- adjacent links of the run meet
      have key : ∀ i, a ≤ i → i + 1 ≤ b → (L i ∩ L (i + 1)).Nonempty := by
        intro i hai hib
        by_contra hne
        rw [not_nonempty_iff_eq_empty] at hne
        refine weak_split hLo hC (c₁ := i + 1) (c₂ := i + 1) ?_
          (cov_split (i + 1) (i + 1) le_rfl (fun i' h1 h2 _ => by omega))
          ⟨by omega, by omega⟩ ⟨hbn, by omega⟩ (hmemS.mp haS).2 (hmemS.mp hbS).2
        intro i' j hi' hj hjn
        by_cases hij : i' + 2 ≤ j
        · exact hweak i' j hij hjn
        · rw [show i' = i by omega, show j = i + 1 by omega]
          exact Set.disjoint_iff_inter_eq_empty.mpr hne
      show (L (a + t) ∩ L (a + u)).Nonempty
      rcases lt_trichotomy (t : ℕ) u with h | h | h
      · have := key (a + t) (by omega) (by omega)
        rwa [show a + (u : ℕ) = a + t + 1 by omega]
      · rw [show u = t from Fin.ext h.symm]
        obtain ⟨z, hz, -⟩ := hfill (a + t) (by omega) (by omega)
        exact ⟨z, hz, hz⟩
      · have := key (a + u) (by omega) (by omega)
        rw [Set.inter_comm]
        rwa [show a + (t : ℕ) = a + u + 1 by omega]
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
    have hiS : i ∈ S := hmemS.mpr ⟨hi, ⟨z, hzi, hz⟩⟩
    have h1 : a ≤ i := S.min'_le _ hiS
    have h2 : i ≤ b := S.le_max' _ hiS
    exact mem_iUnion.mpr ⟨⟨i - a, by omega⟩, by
      show z ∈ L (a + (i - a)); rwa [show a + (i - a) = i by omega]⟩
  · intro t
    exact hfill (a + t) (by omega) (by have := t.isLt; omega)
  · intro i hi hne
    have hiS : i ∈ S := hmemS.mpr ⟨hi, hne⟩
    exact ⟨S.min'_le _ hiS, by have := S.le_max' _ hiS; omega⟩

/-! ## Links indexed by natural numbers -/

/-- The links of a chain indexed by `ℕ`, empty past the end. -/
def linkN {n : ℕ} (D : Chain X n) (i : ℕ) : Set X := if h : i < n then D.link ⟨i, h⟩ else ∅

theorem linkN_of_lt {n : ℕ} (D : Chain X n) {i : ℕ} (h : i < n) : linkN D i = D.link ⟨i, h⟩ :=
  dif_pos h

theorem linkN_fin {n : ℕ} (D : Chain X n) (i : Fin n) : linkN D i = D.link i :=
  dif_pos i.isLt

theorem isOpen_linkN {n : ℕ} (D : Chain X n) (i : ℕ) : IsOpen (linkN D i) := by
  unfold linkN; split_ifs
  · exact D.isOpen _
  · exact isOpen_empty

theorem mem_linkN {n : ℕ} (D : Chain X n) {i : ℕ} {x : X} :
    x ∈ linkN D i ↔ ∃ h : i < n, x ∈ D.link ⟨i, h⟩ := by
  unfold linkN; split_ifs with h
  · exact ⟨fun hx => ⟨h, hx⟩, fun ⟨_, hx⟩ => hx⟩
  · exact ⟨fun hx => hx.elim, fun ⟨h', _⟩ => (h h').elim⟩

theorem disjoint_linkN {n : ℕ} (D : Chain X n) {i j : ℕ} (hij : i + 2 ≤ j) :
    Disjoint (linkN D i) (linkN D j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  obtain ⟨hi', hxi⟩ := (mem_linkN D).mp hi
  obtain ⟨hj', hxj⟩ := (mem_linkN D).mp hj
  have := (D.adjacent_iff ⟨i, hi'⟩ ⟨j, hj'⟩).mp ⟨x, hxi, hxj⟩
  simp only at this
  omega

theorem mem_union_iff_linkN {n : ℕ} (D : Chain X n) {x : X} :
    x ∈ D.union ↔ ∃ i, i < n ∧ x ∈ linkN D i := by
  simp only [Chain.union, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, i.isLt, by rwa [linkN_fin]⟩
  · rintro ⟨i, hi, hx⟩; exact ⟨⟨i, hi⟩, by rwa [← linkN_of_lt D hi]⟩

/-! ## Limits of finely chained sets inside a compact set -/

/-! ## Irreducibility and fine chains (Theorem 14's `δ`) -/

end HPC.Plane
