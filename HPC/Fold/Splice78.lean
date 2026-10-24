import HPC.Fold.Zig77Main
import HPC.Fold.Minimal
import HPC.Fold.OffCenter
import HPC.Fold.Faithful

/-!
# Batch 78: the splice behind Bing's Theorem 4

`fold_low_end` is the greedy jump zigzag of batch 77 run on a sequence to which one *fake* link
at level `0` has been appended after its last link. The fake link is admissible for the
crookedness clause exactly when the last link of the arm meets the first link of the coarse
chain; its time `U` in the fold is a time whose block has every level at most `2`.
-/

namespace HPC.Fold.B78

open Z77

/-! ## Chain-level pieces -/

section ChainLevel

open HPC.Chain

variable {X : Type*} [MetricSpace X]

/-- The re-indexed sequence at an index inside the range. -/
theorem reindex_eq {n : ℕ} (ρ : Fin n → ℤ) (i : Fin n) (x : ℤ) (h1 : 0 ≤ (i : ℤ) + x)
    (h2 : (i : ℤ) + x < n) : Z77.reindex ρ i x = ρ ⟨((i : ℤ) + x).toNat, by omega⟩ := by
  unfold Z77.reindex
  rw [dif_pos ⟨h1, h2⟩]

/-- A link whose least or greatest coarse index lies in `[w, w + 2]` lies in the three coarse
links from `w`. -/
theorem link_sub_of_level {n N : ℕ} {E : Chain X n} {D : Chain X N} (h : E.Refines D)
    (t : Fin n) (w : ℕ)
    (hw : ((w : ℤ) ≤ ((h.minIdx t : ℕ) : ℤ) ∧ ((h.minIdx t : ℕ) : ℤ) ≤ w + 2) ∨
      ((w : ℤ) ≤ ((h.maxIdx t : ℕ) : ℤ) ∧ ((h.maxIdx t : ℕ) : ℤ) ≤ w + 2)) :
    E.link t ⊆ D.unionRange w 3 := by
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (minIdx_subset h t).trans (link_subset_unionRange D _ (by omega) (by omega))
  · exact (maxIdx_subset h t).trans (link_subset_unionRange D _ (by omega) (by omega))

/-- Three consecutive links of the reversed coarse chain are three consecutive links of the
coarse chain. -/
theorem unionRange_reverse {N : ℕ} (D : Chain X N) (j : ℕ) :
    D.reverse.unionRange j 3 ⊆ D.unionRange (N - 3 - j) 3 := by
  intro x hx
  rw [mem_unionRange] at hx ⊢
  obtain ⟨j', h1, h2, h3, h4⟩ := hx
  rw [reverse_link] at h4
  refine ⟨N - 1 - j', by omega, by omega, by omega, ?_⟩
  have : (⟨N - 1 - j', by omega⟩ : Fin N) = Fin.rev ⟨j', h3⟩ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  rw [this]; exact h4

end ChainLevel

end HPC.Fold.B78
