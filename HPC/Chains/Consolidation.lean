import HPC.Chains.Basic
import HPC.Chains.Auxiliary

/-!
# Consolidation infrastructure

Block consolidations as an explicit block map, chain reversal, crookedness of and in
subchains, the minimal and maximal index maps of a refinement, the monotone grouping lemma,
the easy case of Bing 1948 Theorem 4, and a counterexample showing that the strong reading
of "contained in only the first link" is false.

English proofs: COMMISSION-batch4.md §3.
-/

namespace HPC

open Set

/-- The increasing case of `exists_adjacent_cross`. -/
theorem exists_adjacent_cross_mono {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {a b : ℕ}
    {p : ℤ} (hab : a ≤ b) (h1 : g a ≤ p) (h2 : p + 1 ≤ g b) :
    ∃ t, a ≤ t ∧ t + 1 ≤ b ∧ g t = p ∧ g (t + 1) = p + 1 := by
  classical
  have hstep' : ∀ t, g (t + 1) - g t ≤ 1 ∧ -(1 : ℤ) ≤ g (t + 1) - g t := fun t =>
    ⟨(abs_le.mp (hstep t)).2, (abs_le.mp (hstep t)).1⟩
  have hex : ∃ t, a ≤ t ∧ p + 1 ≤ g t := ⟨b, hab, h2⟩
  set y := Nat.find hex with hy
  obtain ⟨hay, hgy⟩ : a ≤ y ∧ p + 1 ≤ g y := Nat.find_spec hex
  have hyb : y ≤ b := Nat.find_le ⟨hab, h2⟩
  have hay' : a < y := by
    rcases hay.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hgy) (by omega)
  have hmin := Nat.find_min hex (m := y - 1) (by omega)
  rw [not_and_or] at hmin
  have hs := hstep' (y - 1)
  have hy1 : y - 1 + 1 = y := by omega
  rw [hy1] at hs
  refine ⟨y - 1, by omega, by omega, ?_, ?_⟩
  · rcases hmin with hm | hm <;> omega
  · rw [hy1]; rcases hmin with hm | hm <;> omega

/-- A discrete crossing lemma: a function on `ℕ` moving by at most one at each step and
passing from a value `≤ p` to a value `≥ p + 1` has two *adjacent* indices, between the two
given ones, carrying the values `p` and `p + 1` (in one order or the other). -/
theorem exists_adjacent_cross {g : ℕ → ℤ} (hstep : ∀ t, |g (t + 1) - g t| ≤ 1) {a b : ℕ}
    {p : ℤ} (h1 : g a ≤ p) (h2 : p + 1 ≤ g b) :
    ∃ t, min a b ≤ t ∧ t + 1 ≤ max a b ∧
      ((g t = p ∧ g (t + 1) = p + 1) ∨ (g t = p + 1 ∧ g (t + 1) = p)) := by
  rcases le_total a b with hab | hab
  · obtain ⟨t, h3, h4, h5, h6⟩ := exists_adjacent_cross_mono hstep hab h1 h2
    exact ⟨t, by omega, by omega, Or.inl ⟨h5, h6⟩⟩
  · have hstep2 : ∀ t, |(-g) (t + 1) - (-g) t| ≤ 1 := by
      intro t
      have h := hstep t
      rw [abs_sub_comm] at h
      simpa [show -g (t + 1) + g t = g t - g (t + 1) by ring] using h
    obtain ⟨t, h3, h4, h5, h6⟩ :=
      exists_adjacent_cross_mono (g := -g) (p := -(p + 1)) hstep2 hab (by simpa using h2)
        (by simpa using h1)
    have e5 : -g t = -(p + 1) := h5
    have e6 : -g (t + 1) = -(p + 1) + 1 := h6
    exact ⟨t, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n m p : ℕ}

/-! ## Block consolidations -/

/-- A block map: a surjection `β : Fin n → Fin p` moving by at most one between adjacent
indices. -/
structure IsBlockMap (β : Fin n → Fin p) : Prop where
  surj : Function.Surjective β
  lip : ∀ t t' : Fin n, t'.val = t.val + 1 → ((β t' : ℤ) - (β t : ℤ)).natAbs ≤ 1

/-- The links of the block consolidation satisfy the adjacency condition of a chain. -/
theorem blockLink_adjacent (D : Chain X n) {β : Fin n → Fin p} (hβ : IsBlockMap β)
    (u u' : Fin p) :
    (((⋃ t ∈ {t | β t = u}, D.link t) ∩ ⋃ t ∈ {t | β t = u'}, D.link t).Nonempty) ↔
      ((u : ℤ) - (u' : ℤ)).natAbs ≤ 1 := by
  have hmem : ∀ (v : Fin p) (t : Fin n) (z : X), β t = v → z ∈ D.link t →
      z ∈ ⋃ t ∈ {t | β t = v}, D.link t := by
    intro v t z hv hz
    exact Set.mem_biUnion (show t ∈ {t | β t = v} from hv) hz
  have hmem' : ∀ (v : Fin p) (z : X), z ∈ (⋃ t ∈ {t | β t = v}, D.link t) →
      ∃ t, β t = v ∧ z ∈ D.link t := by
    intro v z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hz
    exact hz
  -- the essential case: two consecutive blocks meet
  have key : ∀ u u' : Fin p, u'.val = u.val + 1 →
      (((⋃ t ∈ {t | β t = u}, D.link t) ∩ ⋃ t ∈ {t | β t = u'}, D.link t).Nonempty) := by
    intro u u' huu'
    obtain ⟨t₀, ht₀⟩ := hβ.surj u
    obtain ⟨t₁, ht₁⟩ := hβ.surj u'
    have hn : 0 < n := t₀.pos
    set c : ℕ → Fin n := fun x => ⟨min x (n - 1), by omega⟩ with hc
    set G : ℕ → ℤ := fun x => ((β (c x) : Fin p) : ℤ) with hG
    have hcval : ∀ t : Fin n, c t.val = t := by
      intro t
      have := t.isLt
      exact Fin.ext (by simp only [hc]; omega)
    have hGstep : ∀ x, |G (x + 1) - G x| ≤ 1 := by
      intro x
      by_cases hx : x + 1 ≤ n - 1
      · have hsucc : (c (x + 1)).val = (c x).val + 1 := by simp only [hc]; omega
        have hlip := hβ.lip (c x) (c (x + 1)) hsucc
        rw [abs_le]
        simp only [hG]
        omega
      · have heq : c (x + 1) = c x := Fin.ext (by simp only [hc]; omega)
        simp [hG, heq]
    have hGt₀ : G t₀.val = (u : ℕ) := by simp only [hG, hcval t₀, ht₀]
    have hGt₁ : G t₁.val = (u' : ℕ) := by simp only [hG, hcval t₁, ht₁]
    obtain ⟨t, htmin, htmax, hcase⟩ :=
      exists_adjacent_cross hGstep (a := t₀.val) (b := t₁.val) (p := ((u : ℕ) : ℤ))
        (by rw [hGt₀]) (by rw [hGt₁]; omega)
    have ht₀l := t₀.isLt
    have ht₁l := t₁.isLt
    have hcv : (c t).val = t := by simp only [hc]; omega
    have hcv1 : (c (t + 1)).val = t + 1 := by simp only [hc]; omega
    obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff (c t) (c (t + 1))).mpr (by omega)
    have hval : ∀ x : ℕ, ∀ v : Fin p, G x = ((v : ℕ) : ℤ) → β (c x) = v := by
      intro x v hx
      simp only [hG] at hx
      exact Fin.ext (by exact_mod_cast hx)
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨z, hmem u (c t) z (hval t u e1) hz1, hmem u' (c (t + 1)) z ?_ hz2⟩
      exact hval (t + 1) u' (by rw [e2]; omega)
    · refine ⟨z, hmem u (c (t + 1)) z (hval (t + 1) u e2) hz2, hmem u' (c t) z ?_ hz1⟩
      exact hval t u' (by rw [e1]; omega)
  constructor
  · rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, ht, hzt⟩ := hmem' u z hz1
    obtain ⟨t', ht', hzt'⟩ := hmem' u' z hz2
    have hadj := (D.adjacent_iff t t').mp ⟨z, hzt, hzt'⟩
    rcases eq_or_ne t.val t'.val with heq | hne
    · have : t = t' := Fin.ext heq
      subst this
      simp [← ht, ← ht']
    · rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hβ.lip t t' (by omega)
        rw [ht, ht'] at this
        omega
      · have := hβ.lip t' t (by omega)
        rw [ht, ht'] at this
        omega
  · intro hle
    rcases lt_trichotomy u.val u'.val with hlt | heq | hgt
    · exact key u u' (by omega)
    · have : u = u' := Fin.ext heq
      subst this
      obtain ⟨t, ht⟩ := hβ.surj u
      obtain ⟨z, hz⟩ := D.link_nonempty t
      exact ⟨z, hmem u t z ht hz, hmem u t z ht hz⟩
    · obtain ⟨z, hz1, hz2⟩ := key u' u (by omega)
      exact ⟨z, hz2, hz1⟩

/-- The chain whose `u`-th link is the union of the links of `D` in block `u`. -/
def ofBlocks (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) : Chain X p where
  link u := ⋃ t ∈ {t | β t = u}, D.link t
  isOpen _ := isOpen_biUnion fun t _ => D.isOpen t
  adjacent u u' := blockLink_adjacent D hβ u u'

theorem ofBlocks_link (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) (u : Fin p) :
    (D.ofBlocks β hβ).link u = ⋃ t ∈ {t | β t = u}, D.link t := rfl

/-- `ofBlocks` is a consolidation in the sense of batch-1 D6. -/
theorem ofBlocks_isConsolidationOf (D : Chain X n) (β : Fin n → Fin p) (hβ : IsBlockMap β) :
    (D.ofBlocks β hβ).IsConsolidationOf D :=
  ⟨fun t => ⟨β t, Set.subset_biUnion_of_mem (u := fun t => D.link t) (show β t = β t from rfl)⟩,
    fun u => ⟨{t | β t = u}, rfl⟩⟩

/-!
Note: the converse — that every consolidation in the sense of batch-1 D6 arises from a block
map — is false, because D6 does not require the blocks to partition the index set. From this
batch on, Theorems 3–5 are stated for block consolidations (`ofBlocks`). D6 remains in use
only where it already is (Theorem 12), where only its consequences were needed.
-/

/-! ## Reversal -/

/-- The reverse of a chain. -/
def reverse (D : Chain X n) : Chain X n where
  link i := D.link (Fin.rev i)
  isOpen i := D.isOpen _
  adjacent i j := by
    rw [D.adjacent_iff]
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.val_rev, Fin.val_rev]
    omega

@[simp] theorem reverse_link (D : Chain X n) (i : Fin n) :
    D.reverse.link i = D.link (Fin.rev i) := rfl

theorem reverse_reverse (D : Chain X n) : D.reverse.reverse = D := by
  cases D with
  | mk link isOpen adjacent =>
    have : (fun i => link (Fin.rev (Fin.rev i))) = link := by
      funext i; rw [Fin.rev_rev]
    simp only [reverse, this]

theorem Refines.reverse_left {E : Chain X m} {D : Chain X n} (h : E.Refines D) :
    E.reverse.Refines D := fun i => h (Fin.rev i)

theorem Refines.reverse_right {E : Chain X m} {D : Chain X n} (h : E.Refines D) :
    E.Refines D.reverse := by
  intro i
  obtain ⟨j, hj⟩ := h i
  exact ⟨Fin.rev j, by rw [reverse_link, Fin.rev_rev]; exact hj⟩

/-- Crookedness (1948 sense) is unaffected by reversing the fine chain. -/
theorem IsCrookedIn'.reverse_left {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D) :
    E.reverse.IsCrookedIn' D := by
  obtain ⟨hR, hC⟩ := h
  refine ⟨hR.reverse_left, ?_⟩
  intro a b hab i j hi hj
  rw [reverse_link] at hi hj
  obtain ⟨r, s, hbtw, hr, hs⟩ := hC a b hab (Fin.rev i) (Fin.rev j) hi hj
  refine ⟨Fin.rev r, Fin.rev s, ?_, by rw [reverse_link, Fin.rev_rev]; exact hr,
    by rw [reverse_link, Fin.rev_rev]; exact hs⟩
  have hlt : ∀ x y : Fin m, x < y → Fin.rev y < Fin.rev x := by
    intro x y hxy
    have hx := x.isLt
    have hy := y.isLt
    have hxy' : x.val < y.val := hxy
    show (Fin.rev y).val < (Fin.rev x).val
    simp only [Fin.val_rev]
    omega
  rcases hbtw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine Or.inr ⟨?_, hlt _ _ h2, ?_⟩
    · have g := hlt _ _ h1
      rwa [Fin.rev_rev] at g
    · have g := hlt _ _ h3
      rwa [Fin.rev_rev] at g
  · refine Or.inl ⟨?_, hlt _ _ h2, ?_⟩
    · have g := hlt _ _ h1
      rwa [Fin.rev_rev] at g
    · have g := hlt _ _ h3
      rwa [Fin.rev_rev] at g

/-- Crookedness (1948 sense) is unaffected by reversing the coarse chain. -/
theorem IsCrookedIn'.reverse_right {E : Chain X m} {D : Chain X n} (h : E.IsCrookedIn' D) :
    E.IsCrookedIn' D.reverse := by
  obtain ⟨hR, hC⟩ := h
  refine ⟨hR.reverse_right, ?_⟩
  intro a b hab i j hi hj
  have hal := a.isLt
  have hbl := b.isLt
  rw [reverse_link] at hi hj
  have hva := Fin.val_rev a
  have hvb := Fin.val_rev b
  have hrev : (Fin.rev b).val + 2 < (Fin.rev a).val := by omega
  obtain ⟨r, s, hbtw, hr, hs⟩ := hC (Fin.rev b) (Fin.rev a) hrev j i hj hi
  refine ⟨s, r, hbtw.symm, ?_, ?_⟩
  · rw [reverse_link]
    have heq : Fin.rev (⟨b.val - 1, by omega⟩ : Fin n) = ⟨(Fin.rev b).val + 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [heq]
    exact hs
  · rw [reverse_link]
    have heq : Fin.rev (⟨a.val + 1, by omega⟩ : Fin n) = ⟨(Fin.rev a).val - 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [heq]
    exact hr

/-! ## Subchains -/

/-! ## Minimal and maximal index of a refinement -/

variable {E : Chain X m} {D : Chain X n}

/-- A link lies in at most two links of a coarser chain, and those are adjacent. The
hypothesis that `E` refines `D` is not needed: the two containments are enough. -/
theorem subset_adjacent_of_subset (_h : E.Refines D) (t : Fin m) {j j' : Fin n}
    (hj : E.link t ⊆ D.link j) (hj' : E.link t ⊆ D.link j') :
    ((j : ℤ) - (j' : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz⟩ := E.link_nonempty t
  exact (D.adjacent j j').mp ⟨z, hj hz, hj' hz⟩

/-- The indices of links of `D` containing `E.link t` form a nonempty set of naturals. -/
theorem minIdx_set_nonempty (h : E.Refines D) (t : Fin m) :
    {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩}.Nonempty := by
  obtain ⟨j, hj⟩ := h t
  exact ⟨j.val, j.isLt, hj⟩

/-- The least index of a link of `D` containing `E.link t`. -/
noncomputable def Refines.minIdx (h : E.Refines D) (t : Fin m) : Fin n :=
  ⟨sInf {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩},
    Exists.elim (Nat.sInf_mem (minIdx_set_nonempty h t)) fun hj _ => hj⟩

theorem minIdx_subset (h : E.Refines D) (t : Fin m) : E.link t ⊆ D.link (h.minIdx t) := by
  obtain ⟨hj, hsub⟩ := Nat.sInf_mem (minIdx_set_nonempty h t)
  exact hsub

theorem minIdx_le (h : E.Refines D) (t : Fin m) {j : Fin n} (hj : E.link t ⊆ D.link j) :
    h.minIdx t ≤ j := by
  have hmem : (j : ℕ) ∈ {j : ℕ | ∃ hj : j < n, E.link t ⊆ D.link ⟨j, hj⟩} := ⟨j.isLt, hj⟩
  exact Nat.sInf_le hmem

/-- The greatest index of a link of `D` containing `E.link t`. -/
noncomputable def Refines.maxIdx (h : E.Refines D) (t : Fin m) : Fin n :=
  Fin.rev (h.reverse_right.minIdx t)

theorem maxIdx_subset (h : E.Refines D) (t : Fin m) : E.link t ⊆ D.link (h.maxIdx t) :=
  minIdx_subset h.reverse_right t

theorem le_maxIdx (h : E.Refines D) (t : Fin m) {j : Fin n} (hj : E.link t ⊆ D.link j) :
    j ≤ h.maxIdx t := by
  have h2 : E.link t ⊆ D.reverse.link (Fin.rev j) := by
    rw [reverse_link, Fin.rev_rev]; exact hj
  have h3 := minIdx_le h.reverse_right t h2
  have g := Fin.rev_le_rev.mpr h3
  rwa [Fin.rev_rev] at g

/-- `minIdx` moves by at most one between adjacent links. -/
theorem minIdx_lip (h : E.Refines D) (t t' : Fin m) (htt' : t'.val = t.val + 1) :
    ((h.minIdx t' : ℤ) - (h.minIdx t : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
  exact (D.adjacent _ _).mp ⟨z, minIdx_subset h t' hz1, minIdx_subset h t hz2⟩

theorem maxIdx_lip (h : E.Refines D) (t t' : Fin m) (htt' : t'.val = t.val + 1) :
    ((h.maxIdx t' : ℤ) - (h.maxIdx t : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t' t).mpr (by omega)
  exact (D.adjacent _ _).mp ⟨z, maxIdx_subset h t' hz1, maxIdx_subset h t hz2⟩

/-- A link meeting `D.link j` has minimal index within one of `j`. -/
theorem minIdx_near_of_inter (h : E.Refines D) (t : Fin m) (j : Fin n)
    (hne : (E.link t ∩ D.link j).Nonempty) :
    ((h.minIdx t : ℤ) - (j : ℤ)).natAbs ≤ 1 := by
  obtain ⟨z, hz1, hz2⟩ := hne
  exact (D.adjacent _ _).mp ⟨z, minIdx_subset h t hz1, hz2⟩

/-! ## The monotone grouping -/

end Chain

/-! ## The strong reading of "contained in only the first link" is false -/

section Counterexample

end Counterexample

end HPC
