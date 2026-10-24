import HPC.Chains.Consolidation

/-!
# Schedules: block consolidations as Lipschitz functions into ℕ

A block consolidation of `E` refining `D` with every block inside `w` consecutive links of
`D` is the same as a 1-Lipschitz function `β : Fin m → ℕ` attaining `0`, whose fibers have
minimal-index range less than `w` (up to a shift of one in the converse). This removes `D`
and all set theory from Bing's Theorems 3 and 4, which become statements about the
1-Lipschitz sequence `minIdx`.

Also: the range-covering lemma — reading a crooked chain outward from any link in both
directions, one arm's range of minimal indices covers the other's up to a bounded slack.

English proofs: COMMISSION-batch5.md §2.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-! ### A discrete intermediate value theorem on `Fin m`

A function on `Fin m` moving by at most one between adjacent indices attains every value
between two of its values. -/

/-- Increasing form: the two indices are given in order. -/
private theorem exists_eq_of_lip_mono {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    (v : ℕ) : ∀ (d : ℕ) (a b : Fin m), b.val = a.val + d → β a ≤ v → v ≤ β b →
      ∃ t, β t = v := by
  intro d
  induction d with
  | zero =>
      intro a b hb h1 h2
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, by omega⟩
  | succ d ih =>
      intro a b hb h1 h2
      have hlt : a.val + 1 < m := by have := b.isLt; omega
      have hstep := hlip a ⟨a.val + 1, hlt⟩ rfl
      by_cases hv : β ⟨a.val + 1, hlt⟩ ≤ v
      · exact ih ⟨a.val + 1, hlt⟩ b (by simp; omega) hv h2
      · exact ⟨a, by omega⟩

/-- Decreasing form: the two indices are given in reverse order. -/
private theorem exists_eq_of_lip_anti {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    (v : ℕ) : ∀ (d : ℕ) (a b : Fin m), a.val = b.val + d → β a ≤ v → v ≤ β b →
      ∃ t, β t = v := by
  intro d
  induction d with
  | zero =>
      intro a b hb h1 h2
      have hba : b = a := Fin.ext (by omega)
      subst hba
      exact ⟨b, by omega⟩
  | succ d ih =>
      intro a b hb h1 h2
      have hlt : a.val - 1 < m := by have := a.isLt; omega
      have hstep := hlip ⟨a.val - 1, hlt⟩ a (by simp; omega)
      by_cases hv : β ⟨a.val - 1, hlt⟩ ≤ v
      · exact ih ⟨a.val - 1, hlt⟩ b (by simp; omega) hv h2
      · exact ⟨a, by omega⟩

/-- Unoriented form. -/
private theorem exists_eq_of_lip {m : ℕ} {β : Fin m → ℕ}
    (hlip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1)
    {a b : Fin m} {v : ℕ} (h1 : β a ≤ v) (h2 : v ≤ β b) : ∃ t, β t = v := by
  rcases le_total a.val b.val with hab | hab
  · exact exists_eq_of_lip_mono hlip v (b.val - a.val) a b (by omega) h1 h2
  · exact exists_eq_of_lip_anti hlip v (a.val - b.val) a b (by omega) h1 h2

namespace Chain

variable {n m : ℕ} {E : Chain X m} {D : Chain X n}

/-- The union of the links of `D` with index in `[j, j + w)`. -/
def unionRange (D : Chain X n) (j w : ℕ) : Set X :=
  ⋃ j' ∈ Finset.Ico j (j + w), ⋃ (hj' : j' < n), D.link ⟨j', hj'⟩

theorem mem_unionRange {j w : ℕ} {x : X} :
    x ∈ D.unionRange j w ↔
      ∃ j' : ℕ, j ≤ j' ∧ j' < j + w ∧ ∃ hj' : j' < n, x ∈ D.link ⟨j', hj'⟩ := by
  simp only [unionRange, Set.mem_iUnion, Finset.mem_Ico, exists_prop]
  constructor
  · rintro ⟨j', ⟨hj1, hj2⟩, hj3, hx⟩
    exact ⟨j', hj1, hj2, hj3, hx⟩
  · rintro ⟨j', hj1, hj2, hj3, hx⟩
    exact ⟨j', ⟨hj1, hj2⟩, hj3, hx⟩

theorem link_subset_unionRange (D : Chain X n) {j w : ℕ} (k : Fin n) (h1 : j ≤ k.val)
    (h2 : k.val < j + w) : D.link k ⊆ D.unionRange j w := by
  intro x hx
  rw [mem_unionRange]
  exact ⟨k.val, h1, h2, k.isLt, by simpa using hx⟩

/-- A schedule: a 1-Lipschitz function on the link indices attaining `0`. -/
structure IsSchedule (β : Fin m → ℕ) : Prop where
  lip : ∀ t t' : Fin m, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1
  zero : ∃ t, β t = 0

/-- A schedule is a block map onto an initial segment of `ℕ`: it is surjective onto
`[0, sup β]` by the discrete intermediate value theorem. -/
theorem IsSchedule.exists_blockMap {β : Fin m → ℕ} (hβ : IsSchedule β) :
    ∃ (p : ℕ) (β' : Fin m → Fin p), IsBlockMap β' ∧ ∀ t, (β' t).val = β t := by
  classical
  obtain ⟨t0, ht0⟩ := hβ.zero
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨t0, Finset.mem_univ _⟩
  obtain ⟨tM, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin m)) β hne
  refine ⟨β tM + 1, fun t => ⟨β t, by have := hmax t (Finset.mem_univ t); omega⟩, ⟨?_, ?_⟩,
    fun t => rfl⟩
  · intro u
    have h1 : β t0 ≤ u.val := by omega
    have h2 : u.val ≤ β tM := by have := u.isLt; omega
    obtain ⟨t, ht⟩ := exists_eq_of_lip hβ.lip h1 h2
    exact ⟨t, Fin.ext ht⟩
  · intro t t' htt'
    exact hβ.lip t t' htt'

end Chain

end HPC
