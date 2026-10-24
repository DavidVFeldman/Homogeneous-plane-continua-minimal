import HPC.Fold.Minimal

/-!
# Bing's pattern as a function of the index

Batch 82. `bingF d u` is the `u`-th term of `bingPath 0 d` (`0`-indexed), defined by structural
recursion on `d` so that its three pieces can be addressed by index arithmetic:

* `u < z (d-1)`: the pattern `bingF (d-1)` (Bing's `F[1, z(n-1)]`);
* the next `z (d-2) - 1` indices: the reflected pattern `(d-1) - bingF (d-2)` (Bing's `F''`);
* the last `z (d-1) - 1` indices: the shifted pattern `1 + bingF (d-1)` (Bing's `F'''`).

Beyond its length the function is constant, equal to `d`.
-/

namespace HPC.Fold

/-- Bing's pattern `bingPath 0 d` as a function of the index. -/
def bingF : ℕ → ℕ → ℤ
  | 0, _ => 0
  | 1, u => min (u : ℤ) 1
  | 2, u => min (u : ℤ) 2
  | d + 3, u =>
      if u < z (d + 2) then bingF (d + 2) u
      else if u < z (d + 2) + z (d + 1) - 1 then ((d : ℤ) + 2) - bingF (d + 1) (u - (z (d + 2) - 1))
      else 1 + bingF (d + 2) (u - (z (d + 2) + z (d + 1) - 2))

theorem z_succ3 (d : ℕ) : z (d + 3) = 2 * z (d + 2) + z (d + 1) - 2 := rfl

theorem z_two_le (d : ℕ) (hd : 1 ≤ d) : 2 ≤ z d := by
  have := z_ge_of_le hd
  simpa [z] using this

theorem z_three_le (d : ℕ) (hd : 2 ≤ d) : 3 ≤ z d := by
  have := z_ge_of_le hd
  simpa [z] using this

theorem bingF_zero : ∀ d : ℕ, bingF d 0 = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | d + 3 => by
      rw [bingF, if_pos (by have := z_pos (d + 2); omega)]
      exact bingF_zero (d + 2)

/-- From its last index on, the pattern is constant, equal to `d`. -/
theorem bingF_top : ∀ d u : ℕ, z d - 1 ≤ u → bingF d u = d
  | 0, _, _ => rfl
  | 1, u, hu => by
      have : z 1 = 2 := rfl
      simp only [bingF]; push_cast; omega
  | 2, u, hu => by
      have : z 2 = 3 := rfl
      simp only [bingF]; push_cast; omega
  | d + 3, u, hu => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rw [z_succ3] at hu
      rw [bingF, if_neg (by omega), if_neg (by omega),
        bingF_top (d + 2) _ (by omega)]
      push_cast; ring

/-- The three pieces of the pattern, as a case split. -/
theorem bingF_A (d u : ℕ) (hu : u < z (d + 2)) : bingF (d + 3) u = bingF (d + 2) u := by
  rw [bingF, if_pos hu]

theorem bingF_B (d u : ℕ) (hu1 : z (d + 2) - 1 ≤ u) (hu2 : u < z (d + 2) + z (d + 1) - 1) :
    bingF (d + 3) u = ((d : ℤ) + 2) - bingF (d + 1) (u - (z (d + 2) - 1)) := by
  rcases Nat.lt_or_ge u (z (d + 2)) with h | h
  · have hu : u = z (d + 2) - 1 := by omega
    rw [bingF, if_pos h, hu, Nat.sub_self, bingF_zero, bingF_top (d + 2) _ le_rfl]
    push_cast; ring
  · rw [bingF, if_neg (by omega), if_pos hu2]

theorem bingF_C (d u : ℕ) (hu : z (d + 2) + z (d + 1) - 2 ≤ u) :
    bingF (d + 3) u = 1 + bingF (d + 2) (u - (z (d + 2) + z (d + 1) - 2)) := by
  have hB := z_two_le (d + 1) (by omega)
  rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h | h
  · have hu' : u = z (d + 2) + z (d + 1) - 2 := by omega
    have hA := z_pos (d + 2)
    rw [bingF_B d u (by omega) h, bingF_top (d + 1) _ (by omega), hu', Nat.sub_self, bingF_zero]
    push_cast; ring
  · rw [bingF, if_neg (by omega), if_neg (by omega)]

theorem bingF_range : ∀ d u : ℕ, 0 ≤ bingF d u ∧ bingF d u ≤ d
  | 0, _ => by simp [bingF]
  | 1, u => by simp only [bingF]; omega
  | 2, u => by simp only [bingF]; omega
  | d + 3, u => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1]; have := bingF_range (d + 2) u; push_cast; omega
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2]
        have := bingF_range (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)]
        have := bingF_range (d + 2) (u - (z (d + 2) + z (d + 1) - 2)); push_cast at *; omega

theorem bingF_nonneg (d u : ℕ) : 0 ≤ bingF d u := (bingF_range d u).1
theorem bingF_le (d u : ℕ) : bingF d u ≤ d := (bingF_range d u).2

/-- Consecutive terms differ by at most one. -/
theorem bingF_lip : ∀ d u : ℕ, |bingF d (u + 1) - bingF d u| ≤ 1
  | 0, _ => by simp [bingF]
  | 1, u => by simp only [bingF]; rw [abs_le]; push_cast; omega
  | 2, u => by simp only [bingF]; rw [abs_le]; push_cast; omega
  | d + 3, u => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge (u + 1) (z (d + 2)) with h1 | h1
      · rw [bingF_A d u (by omega), bingF_A d (u + 1) h1]; exact bingF_lip (d + 2) u
      rcases Nat.lt_or_ge (u + 1) (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) (by omega), bingF_B d (u + 1) (by omega) h2]
        have := bingF_lip (d + 1) (u - (z (d + 2) - 1))
        rw [show u + 1 - (z (d + 2) - 1) = u - (z (d + 2) - 1) + 1 by omega]
        rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
      · rw [bingF_C d u (by omega), bingF_C d (u + 1) (by omega)]
        have := bingF_lip (d + 2) (u - (z (d + 2) + z (d + 1) - 2))
        rw [show u + 1 - (z (d + 2) + z (d + 1) - 2) = u - (z (d + 2) + z (d + 1) - 2) + 1 by
          omega]
        rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]

/-- Level `0` is taken only at the first index. -/
theorem bingF_eq_zero : ∀ d u : ℕ, u < z d → bingF d u = 0 → u = 0
  | 0, u, hu, _ => by have : z 0 = 1 := rfl; omega
  | 1, u, _, h => by simp only [bingF] at h; omega
  | 2, u, _, h => by simp only [bingF] at h; omega
  | d + 3, u, hu, h => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1] at h; exact bingF_eq_zero (d + 2) u h1 h
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2] at h
        have := bingF_le (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)] at h
        have := bingF_nonneg (d + 2) (u - (z (d + 2) + z (d + 1) - 2)); omega

/-- The top level `d` is taken only from the last index on. -/
theorem bingF_eq_top : ∀ d u : ℕ, bingF d u = d → z d - 1 ≤ u
  | 0, u, _ => by have : z 0 = 1 := rfl; omega
  | 1, u, h => by have : z 1 = 2 := rfl; simp only [bingF] at h; omega
  | 2, u, h => by have : z 2 = 3 := rfl; simp only [bingF] at h; omega
  | d + 3, u, h => by
      have hA := z_three_le (d + 2) (by omega)
      have hB := z_two_le (d + 1) (by omega)
      rw [z_succ3]
      rcases Nat.lt_or_ge u (z (d + 2)) with h1 | h1
      · rw [bingF_A d u h1] at h; have := bingF_le (d + 2) u; push_cast at *; omega
      rcases Nat.lt_or_ge u (z (d + 2) + z (d + 1) - 1) with h2 | h2
      · rw [bingF_B d u (by omega) h2] at h
        have := bingF_nonneg (d + 1) (u - (z (d + 2) - 1)); push_cast at *; omega
      · rw [bingF_C d u (by omega)] at h
        have := bingF_eq_top (d + 2) (u - (z (d + 2) + z (d + 1) - 2)) (by push_cast at *; omega)
        omega

end HPC.Fold

namespace HPC.Fold

end HPC.Fold
