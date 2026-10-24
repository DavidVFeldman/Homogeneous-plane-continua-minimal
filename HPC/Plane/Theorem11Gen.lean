import HPC.Plane.Theorem11Nec

/-!
# Batch 96, §2–3: chain constructions for the sufficiency half of Theorem 11

* `EpsCoverable` (moved here from the skeleton so that the general lemmas can use it).
* Chain constructions: `chainSingle` (one link), `chainRestrict` (intersect every link with an
  open set), `chainAppend` (concatenate two chains that meet only at the junction).
* `consec_meet`: in a chain all of whose links meet a preconnected set `C` it covers, consecutive
  links meet *inside* `C` (the fact needed for item 7 of the commission).
* `trim_first`: a chain covering a preconnected `C` with `p` in the first link only (and in no
  other link's closure) can be cut down to the links meeting `C`, keeping these properties.
* `epsCoverable_amalgam_gen`: Bing's amalgamation, for `Z ⊆ H ∪ K` with `H ∩ K = {p}`.
* `exists_minimal_notCoverable'`: the minimal non-coverable subcontinuum.
-/

namespace HPC.Plane

open Set Topology Metric

section Constructions

variable {X : Type*} [MetricSpace X]

/-- `M` is covered by some `ε`-chain. -/
def EpsCoverable (M : Set X) (ε : ℝ) : Prop :=
  ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

/-- **Consecutive links meet inside the covered set.** If every link of a chain meets a
preconnected set `C` it covers, then consecutive links meet inside `C`. -/
theorem consec_meet {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCD : C ⊆ D.union) (hall : ∀ i, (C ∩ D.link i).Nonempty) (i : ℕ) (hi : i + 1 < n) :
    (C ∩ (D.link ⟨i, by omega⟩ ∩ D.link ⟨i + 1, hi⟩)).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  set U : Set X := ⋃ t : Fin n, ⋃ (_ : t.val ≤ i), D.link t with hU
  set V : Set X := ⋃ t : Fin n, ⋃ (_ : i + 1 ≤ t.val), D.link t with hV
  have hUo : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t
  have hVo : IsOpen V := isOpen_iUnion fun t => isOpen_iUnion fun _ => D.isOpen t
  have hcov : C ⊆ U ∪ V := by
    intro z hz
    obtain ⟨t, ht⟩ := exists_link_of_mem_union (hCD hz)
    by_cases hti : t.val ≤ i
    · exact Or.inl (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨hti, ht⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨by omega, ht⟩⟩)
  obtain ⟨u, huC, hu⟩ := hall ⟨i, by omega⟩
  obtain ⟨v, hvC, hv⟩ := hall ⟨i + 1, hi⟩
  obtain ⟨z, hzC, hzU, hzV⟩ := hC U V hUo hVo hcov
    ⟨u, huC, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨le_refl i, hu⟩⟩⟩
    ⟨v, hvC, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨le_refl (i + 1), hv⟩⟩⟩
  simp only [hU, hV, mem_iUnion] at hzU hzV
  obtain ⟨t1, h1, hz1⟩ := hzU
  obtain ⟨t2, h2, hz2⟩ := hzV
  have := (D.adjacent_iff t1 t2).mp ⟨z, hz1, hz2⟩
  have e1 : t1 = ⟨i, by omega⟩ := Fin.ext (by simp only; omega)
  have e2 : t2 = ⟨i + 1, hi⟩ := Fin.ext (by simp only; omega)
  rw [e1] at hz1
  rw [e2] at hz2
  have : z ∈ C ∩ (D.link ⟨i, by omega⟩ ∩ D.link ⟨i + 1, hi⟩) := ⟨hzC, hz1, hz2⟩
  rw [h] at this
  exact this

/-- The links meeting a nonempty preconnected set covered by a chain form an interval `[a, b]`. -/
theorem exists_trim {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCne : C.Nonempty) (hCD : C ⊆ D.union) :
    ∃ a b : Fin n, a ≤ b ∧ ∀ t : Fin n, (C ∩ D.link t).Nonempty ↔ (a.val ≤ t.val ∧ t.val ≤ b.val) := by
  classical
  set I := Finset.univ.filter (fun i : Fin n => (C ∩ D.link i).Nonempty) with hI
  obtain ⟨x, hx⟩ := hCne
  obtain ⟨i0, hi0⟩ := exists_link_of_mem_union (hCD hx)
  have hmem : ∀ t, t ∈ I ↔ (C ∩ D.link t).Nonempty := fun t => by
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
  have hIne : I.Nonempty := ⟨i0, (hmem i0).mpr ⟨x, hx, hi0⟩⟩
  refine ⟨I.min' hIne, I.max' hIne, Finset.min'_le_max' I hIne, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · exact ⟨Fin.le_def.mp (Finset.min'_le I t ((hmem t).mpr ht)),
      Fin.le_def.mp (Finset.le_max' I t ((hmem t).mpr ht))⟩
  · have ha := (hmem _).mp (Finset.min'_mem I hIne)
    have hb := (hmem _).mp (Finset.max'_mem I hIne)
    exact meets_between D hC hCD ha hb t (by have := ht.1; omega) (by have := ht.2; omega)

end Constructions

end HPC.Plane
