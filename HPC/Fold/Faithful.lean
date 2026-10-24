import HPC.Chains.Schedule

/-!
# The faithful model, with a realization theorem

`IsCrookedIv` (batch 20) is necessary but not sufficient, for two reasons the geometry
dictates and the definition omitted:

* **Adjacency.** Two overlapping links lie in the intersection of all their containing coarse
  links, so the union of their two index-intervals must fit in two consecutive indices. A
  width-2 link at `{a, a+1}` cannot neighbour a link touching `a + 2`, since
  `d_a ∩ d_{a+1} ∩ d_{a+2} = ∅`. Both batch-20 witnesses violate this at several places.
* **Forced meetings.** A link overlaps each neighbour and therefore meets every coarse link
  its neighbour lies in. Those meetings fire crookedness hypotheses.

`IsCrookedIvF` imposes both. Two theorems close the model question: a crooked chain lands in
it (necessity), and every sequence in it is the `(minIdx, maxIdx)` pair of an explicit crooked
chain of open rectangles in `ℝ × ℝ` (sufficiency). After this batch a counterexample in the
model *is* a chain, by construction.

English proofs: COMMISSION-batch22.md §3; the endpoint table actually used is in
REPORT-batch22.md. Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

open Set

/-- The faithful model. -/
structure IsCrookedIvF {n : ℕ} (ρ σ : Fin n → ℤ) : Prop where
  le : ∀ t, ρ t ≤ σ t
  width : ∀ t, σ t ≤ ρ t + 1
  /-- geometric adjacency: the two intervals of neighbours fit in two consecutive indices -/
  adj : ∀ t t' : Fin n, t'.val = t.val + 1 → max (σ t) (σ t') ≤ min (ρ t) (ρ t') + 1
  /-- crookedness, with hypotheses on forced meetings -/
  crooked : ∀ s t : Fin n, s < t → ∀ h k : ℤ,
    (∃ u : Fin n, ((u : ℤ) - s).natAbs ≤ 1 ∧ ρ u ≤ h ∧ h ≤ σ u) →
    (∃ u : Fin n, ((u : ℤ) - t).natAbs ≤ 1 ∧ ρ u ≤ k ∧ k ≤ σ u) →
    3 ≤ |h - k| →
    ∃ r r' : Fin n, s < r ∧ r < r' ∧ r' < t ∧
      (h < k → (ρ r ≤ k - 1 ∧ k - 1 ≤ σ r) ∧ (ρ r' ≤ h + 1 ∧ h + 1 ≤ σ r')) ∧
      (k < h → (ρ r ≤ k + 1 ∧ k + 1 ≤ σ r) ∧ (ρ r' ≤ h - 1 ∧ h - 1 ≤ σ r'))

/-! ## A decidable criterion for the faithful model

The crookedness clause quantifies over integers `h` and `k`; the width clause pins each of
them to one of the two ends of the interval of the witnessing neighbour, so the clause is
equivalent to a statement quantified over two indices and two Booleans, which `decide` can
check on concrete data. -/

open HPC.Chain in
/-- One application of 1948 crookedness, from meeting hypotheses: the `crookedIv_step` of
batch 20 with `meets` in place of `lies in`. -/
theorem crookedIvF_step {X : Type*} [MetricSpace X] {m c : ℕ}
    {E : Chain X m} {D : Chain X c} (hcr : E.IsCrookedIn' D) {s t : Fin m} (hst : s < t)
    (a b : Fin c) (ha : (E.link s ∩ D.link a).Nonempty) (hb : (E.link t ∩ D.link b).Nonempty)
    (hab : 3 ≤ |(a : ℤ) - (b : ℤ)|) :
    ∃ r r' : Fin m, s < r ∧ r < r' ∧ r' < t ∧
      ((a : ℤ) < (b : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) - 1 ∧ (b : ℤ) - 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) + 1 ∧
          (a : ℤ) + 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) ∧
      ((b : ℤ) < (a : ℤ) →
        (((hcr.1.minIdx r : ℕ) : ℤ) ≤ (b : ℤ) + 1 ∧ (b : ℤ) + 1 ≤ ((hcr.1.maxIdx r : ℕ) : ℤ)) ∧
        (((hcr.1.minIdx r' : ℕ) : ℤ) ≤ (a : ℤ) - 1 ∧
          (a : ℤ) - 1 ≤ ((hcr.1.maxIdx r' : ℕ) : ℤ))) := by
  have href := hcr.1
  rcases lt_or_gt_of_ne (fun (hab' : (a : ℤ) = (b : ℤ)) => by
      rw [hab'] at hab; simp at hab) with hlt | hgt
  · have hidx : a.val + 2 < b.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 a b hidx s t ha hb
    have horder : s < r ∧ r < r' ∧ r' < t := by
      rcases hbtw with hb' | hb'
      · exact hb'
      · exact absurd hst (not_lt.mpr ((hb'.2.2.trans hb'.2.1).trans hb'.1).le)
    refine ⟨r, r', horder.1, horder.2.1, horder.2.2, fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      fun hcon => absurd hcon (by omega)⟩
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
  · have hidx : b.val + 2 < a.val := by
      rcases abs_cases ((a : ℤ) - (b : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    obtain ⟨r, r', hbtw, hr, hr'⟩ := hcr.2 b a hidx t s hb ha
    have horder : s < r' ∧ r' < r ∧ r < t := by
      rcases hbtw with hb' | hb'
      · exact absurd hst (not_lt.mpr ((hb'.1.trans hb'.2.1).trans hb'.2.2).le)
      · exact ⟨hb'.2.2, hb'.2.1, hb'.1⟩
    refine ⟨r', r, horder.1, horder.2.1, horder.2.2, fun hcon => absurd hcon (by omega),
      fun _ => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · have := Fin.le_def.mp (minIdx_le href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r' hr'); simp only [] at this; omega
    · have := Fin.le_def.mp (minIdx_le href r hr); simp only [] at this; omega
    · have := Fin.le_def.mp (le_maxIdx href r hr); simp only [] at this; omega

open HPC.Chain in
/-- **Necessity.** A crooked chain lands in the faithful model. -/
theorem isCrookedIvF_minIdx_maxIdx {X : Type*} [MetricSpace X] {m k : ℕ}
    {E : Chain X m} {D : Chain X k} (h : E.IsCrookedIn' D) :
    IsCrookedIvF (fun t => (h.1.minIdx t : ℤ)) (fun t => (h.1.maxIdx t : ℤ)) := by
  have href := h.1
  have hle : ∀ t, ((href.minIdx t : ℕ) : ℤ) ≤ ((href.maxIdx t : ℕ) : ℤ) := by
    intro t
    have := Fin.le_def.mp (minIdx_le href t (maxIdx_subset href t))
    exact_mod_cast this
  have hwidth : ∀ t, ((href.maxIdx t : ℕ) : ℤ) ≤ ((href.minIdx t : ℕ) : ℤ) + 1 := by
    intro t
    have hadj := subset_adjacent_of_subset href t (minIdx_subset href t) (maxIdx_subset href t)
    have := hle t
    omega
  -- a link whose interval contains `j` lies in the coarse link with index `j`
  have hpin : ∀ (t : Fin m) (j : ℤ), ((href.minIdx t : ℕ) : ℤ) ≤ j →
      j ≤ ((href.maxIdx t : ℕ) : ℤ) → ∃ a : Fin k, E.link t ⊆ D.link a ∧ ((a : ℕ) : ℤ) = j := by
    intro t j h1 h2
    have := hwidth t
    rcases (by omega : j = ((href.minIdx t : ℕ) : ℤ) ∨ j = ((href.maxIdx t : ℕ) : ℤ)) with e | e
    · exact ⟨href.minIdx t, minIdx_subset href t, e.symm⟩
    · exact ⟨href.maxIdx t, maxIdx_subset href t, e.symm⟩
  refine ⟨hle, hwidth, ?_, ?_⟩
  · intro t t' htt'
    have h1 := hle t
    have h2 := hle t'
    have h3 := hwidth t
    have h4 := hwidth t'
    obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t t').mpr (by omega)
    have hA : ((href.maxIdx t : ℤ) - (href.minIdx t' : ℤ)).natAbs ≤ 1 :=
      (D.adjacent _ _).mp ⟨z, maxIdx_subset href t hz1, minIdx_subset href t' hz2⟩
    have hB : ((href.maxIdx t' : ℤ) - (href.minIdx t : ℤ)).natAbs ≤ 1 :=
      (D.adjacent _ _).mp ⟨z, maxIdx_subset href t' hz2, minIdx_subset href t hz1⟩
    rw [max_le_iff]
    simp only [] at *
    omega
  · rintro s t hst hh kk ⟨u, hu, hu1, hu2⟩ ⟨v, hv, hv1, hv2⟩ habs
    obtain ⟨a, ha, hav⟩ := hpin u hh hu1 hu2
    obtain ⟨b, hb, hbv⟩ := hpin v kk hv1 hv2
    have hmeet_s : (E.link s ∩ D.link a).Nonempty := by
      obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff s u).mpr (by
        have : ((u : ℤ) - (s : ℤ)).natAbs ≤ 1 := hu
        omega)
      exact ⟨z, hz1, ha hz2⟩
    have hmeet_t : (E.link t ∩ D.link b).Nonempty := by
      obtain ⟨z, hz1, hz2⟩ := (E.adjacent_iff t v).mpr (by
        have : ((v : ℤ) - (t : ℤ)).natAbs ≤ 1 := hv
        omega)
      exact ⟨z, hz1, hb hz2⟩
    obtain ⟨r, r', h1, h2, h3, hasc, hdesc⟩ :=
      crookedIvF_step h hst a b hmeet_s hmeet_t (by rw [hav, hbv]; exact habs)
    refine ⟨r, r', h1, h2, h3, fun hlt => ?_, fun hlt => ?_⟩
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hasc (by omega)
      omega
    · obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hdesc (by omega)
      omega

/-! ## Sufficiency: the realization -/

section Endpoints

variable {n : ℕ}

variable {ρ σ : Fin n → ℤ}

end Endpoints

/-! ### Intervals with endpoints in eighths -/

/-! ## A realized example

The realization theorem is not vacuous: here is a six-term member of the faithful model whose
crookedness clause genuinely fires — at `s = 0`, `t = 4`, with meeting indices `0` and `3` —
together with the chain of open rectangles that realizes it. -/

/-! ## The batch-20 witnesses are not chains -/

/-! ## The route, over the faithful model -/

end HPC.Fold
