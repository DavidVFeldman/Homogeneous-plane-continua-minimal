import HPC.Plane.SorgenfreyDefs

/-!
# Batch 102, part 1: Nadler 11.25–11.33

The statements of the skeleton for 11.25–11.33 (moved here from `HPC/Plane/Sorgenfrey.lean`),
with their proofs. Throughout, `X = Y ⊕ Z`, `U = X ∖ Z`, `V = X ∖ Y`, and `Ū`, `V̄` are closures.

Shape changes (recorded in `REPORT-batch102.md`):
* **11.28 as transcribed is false** when `H = Ū` (then `U ∖ H = ∅`, which is not connected);
  Nadler's proof assumes `U − H ≠ ∅` ("assuming for the purpose of proof"). The skeleton's
  statement is kept, commented out, with the counterexample `isConnected_diff_of_superset_false`
  (the arc `[0, 1] = [0, ½] ⊕ [½, 1]`); `isConnected_diff_of_superset'` adds `U ∖ H ≠ ∅`.
* **11.31**: the hypothesis `B ⊆ Ū` is not used and is dropped.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## 11.25, 11.26 and the remark after 11.24 -/

/-- **11.25.** Every triod is a weak triod. -/
theorem isWeakTriod_of_isTriod {X : Set S} (h : IsTriod X) : IsWeakTriod X := by
  obtain ⟨hX, N, hN, hNX, A, B, C, hA, hB, hC, hcov, h1, h2, h3, h4, h5, h6⟩ := h
  have hnotN : ∀ x ∈ A ∪ B ∪ C, x ∉ N := fun x hx => by
    have : x ∈ X \ N := by rw [hcov]; exact hx
    exact this.2
  have hXA : Fold.Q78.IsContinuum (N ∪ A) :=
    isContinuum_union_piece (R := B ∪ C) hX hN hNX (by rw [hcov, union_assoc])
      (disjoint_union_right.mpr ⟨h1, h3⟩) (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h2, h4⟩)
  have hXB : Fold.Q78.IsContinuum (N ∪ B) :=
    isContinuum_union_piece (R := A ∪ C) hX hN hNX
      (by rw [hcov]; ext x; simp only [mem_union]; tauto)
      (disjoint_union_right.mpr ⟨h2.symm, h5⟩)
      (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h1.symm, h6⟩)
  have hXC : Fold.Q78.IsContinuum (N ∪ C) :=
    isContinuum_union_piece (R := A ∪ B) hX hN hNX
      (by rw [hcov]; ext x; simp only [mem_union]; tauto)
      (disjoint_union_right.mpr ⟨h4.symm, h6.symm⟩)
      (by rw [closure_union]; exact disjoint_union_right.mpr ⟨h3.symm, h5.symm⟩)
  have hXeq : X = N ∪ (A ∪ B ∪ C) := by rw [← hcov, union_diff_cancel hNX]
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  obtain ⟨n, hn⟩ := hN.2.nonempty
  refine isWeakTriod_of hXA hXB hXC (by rw [hXeq]; ext x; simp only [mem_union]; tauto) ?_ ?_ ?_
    ⟨n, Or.inl hn, Or.inl hn, Or.inl hn⟩
  · refine ⟨a, Or.inr ha, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN a (Or.inl (Or.inl ha)) h
      · exact Set.disjoint_left.mp h2 ha (subset_closure h)
    · rintro (h | h)
      · exact hnotN a (Or.inl (Or.inl ha)) h
      · exact Set.disjoint_left.mp h4 ha (subset_closure h)
  · refine ⟨b, Or.inr hb, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN b (Or.inl (Or.inr hb)) h
      · exact Set.disjoint_left.mp h1 (subset_closure h) hb
    · rintro (h | h)
      · exact hnotN b (Or.inl (Or.inr hb)) h
      · exact Set.disjoint_left.mp h6 hb (subset_closure h)
  · refine ⟨c, Or.inr hc, ?_, ?_⟩
    · rintro (h | h)
      · exact hnotN c (Or.inr hc) h
      · exact Set.disjoint_left.mp h3 (subset_closure h) hc
    · rintro (h | h)
      · exact hnotN c (Or.inr hc) h
      · exact Set.disjoint_left.mp h5 (subset_closure h) hc

/-! ## 11.27 and 11.28 -/

-- Commented-out statement `isConnected_diff_of_superset` removed in batch 103; see `LEDGER.md`.

/-! ## 11.30 -/

/-! ## 11.31–11.33 -/

end HPC.Plane
