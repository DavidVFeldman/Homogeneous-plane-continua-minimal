import Mathlib

/-!
# Jump walks and the phase condition

A walk in `FoldsOnto` is an arbitrary `c : ℕ → ℤ`; nothing asks consecutive centres to differ by
one. This file uses that freedom. For turning levels `a₀, a₁, …, a_K` (each leg of height at least
three) the *jump walk* `jwalk a₀ [a₁, …, a_K]` starts at `a₀` and runs each leg `a → b` as
`a, a ± 3, a ± 4, …, b`: it skips the two levels next to the turn it leaves.

With that walk, whether an arm folds is decided by a purely order-theoretic condition, `Fit`: on
each leg the arm stays within one of the leg's range, and it passes to the next leg when it first
comes within one of the leg's far end. `fold_of_fit` builds the fold from `Fit`.
-/

namespace HPC.Fold.Z77

/-- The envelope of the leg from `a` to `b`: within one of the levels between them. -/
def Env (a b x : ℤ) : Prop := min a b - 1 ≤ x ∧ x ≤ max a b + 1

/-- The level at which an arm passes from the leg `a → b` to the next leg: one short of `b`. -/
def arr (a b : ℤ) : ℤ := if a < b then b - 1 else b + 1

/-- **The phase condition.** `Fit f m τ a ts`: from time `τ`, the arm `f` (read on `[0, m)`) runs
the legs from `a` through the turning levels `ts`. On each leg it either stays in the leg's
envelope for good, or stays in it until a time at which it is at `arr`, where it passes to the next
leg. Every leg has height at least three. -/
def Fit (f : ℕ → ℤ) (m : ℕ) : ℕ → ℤ → List ℤ → Prop
  | _, _, [] => False
  | τ, a, b :: rest =>
      3 ≤ |b - a| ∧
      ((∀ j, τ ≤ j → j < m → Env a b (f j)) ∨
       (∃ τ', τ ≤ τ' ∧ τ' < m ∧ f τ' = arr a b ∧
          (∀ j, τ ≤ j → j ≤ τ' → Env a b (f j)) ∧ Fit f m τ' b rest))

/-- The number of indices of the leg `a → b` before its far end. -/
def legLen (a b : ℤ) : ℕ := (|b - a| - 2).toNat

/-- The length of the jump walk. -/
def jlen : ℤ → List ℤ → ℕ
  | _, [] => 1
  | a, b :: rest => legLen a b + jlen b rest

/-- **The jump walk.** -/
def jwalk : ℤ → List ℤ → ℕ → ℤ
  | a, [], _ => a
  | a, b :: rest, u =>
      if u = 0 then a
      else if u < legLen a b then (if a < b then a + 2 + u else a - 2 - u)
      else jwalk b rest (u - legLen a b)

/-- The position on the leg `a → b` used for an arm at level `x`. -/
def legPos (a b x : ℤ) : ℕ :=
  if a < b then (max 0 (min (x - a - 1) (b - a - 2))).toNat
  else (max 0 (min (a - 1 - x) (a - b - 2))).toNat

theorem jlen_pos (a : ℤ) (ts : List ℤ) : 1 ≤ jlen a ts := by
  induction ts generalizing a with
  | nil => simp [jlen]
  | cons b rest ih => simp only [jlen]; have := ih b; omega

theorem jwalk_zero (a : ℤ) (ts : List ℤ) : jwalk a ts 0 = a := by
  cases ts with
  | nil => simp [jwalk]
  | cons b rest => simp [jwalk]

/-- `|b - a|` with the sign of `b - a` resolved. -/
theorem abs_sub_cases (a b : ℤ) : (a < b ∧ |b - a| = b - a) ∨ (¬ a < b ∧ |b - a| = a - b) := by
  rcases lt_or_ge a b with h | h
  · exact Or.inl ⟨h, abs_of_pos (by omega)⟩
  · exact Or.inr ⟨by omega, by rw [abs_of_nonpos (by omega)]; ring⟩

theorem legPos_le (a b x : ℤ) (h : 3 ≤ |b - a|) : legPos a b x ≤ legLen a b := by
  unfold legPos legLen
  rcases abs_sub_cases a b with ⟨hab, he⟩ | ⟨hab, he⟩ <;> rw [he] at h ⊢ <;> simp only [hab,
    if_true, if_false] <;> omega

theorem legPos_lip (a b x y : ℤ) (h : |y - x| ≤ 1) :
    |((legPos a b y : ℕ) : ℤ) - ((legPos a b x : ℕ) : ℤ)| ≤ 1 := by
  rw [abs_le] at h ⊢
  unfold legPos
  split_ifs with hab <;> constructor <;> omega

/-- The jump walk at the leg position of a level in the envelope is within one of that level. -/
theorem jwalk_legPos (a b x : ℤ) (rest : List ℤ) (h3 : 3 ≤ |b - a|) (hx : Env a b x) :
    |x - jwalk a (b :: rest) (legPos a b x)| ≤ 1 := by
  unfold Env at hx
  rw [abs_le]
  rcases abs_sub_cases a b with ⟨hab, he⟩ | ⟨hab, he⟩
  · rw [he] at h3
    rw [min_eq_left (by omega), max_eq_right (by omega)] at hx
    have hp : (legPos a b x : ℤ) = max 0 (min (x - a - 1) (b - a - 2)) := by
      unfold legPos; rw [if_pos hab]; rw [Int.toNat_of_nonneg (le_max_left _ _)]
    have hl : (legLen a b : ℤ) = b - a - 2 := by
      unfold legLen; rw [he, Int.toNat_of_nonneg (by omega)]
    simp only [jwalk]
    split_ifs with h0 hlt
    · rw [h0] at hp; push_cast at hp; omega
    · omega
    · have heq : legPos a b x = legLen a b := by omega
      rw [heq, Nat.sub_self, jwalk_zero b rest]
      omega
  · rw [he] at h3
    rw [min_eq_right (by omega), max_eq_left (by omega)] at hx
    have hp : (legPos a b x : ℤ) = max 0 (min (a - 1 - x) (a - b - 2)) := by
      unfold legPos; rw [if_neg hab]; rw [Int.toNat_of_nonneg (le_max_left _ _)]
    have hl : (legLen a b : ℤ) = a - b - 2 := by
      unfold legLen; rw [he, Int.toNat_of_nonneg (by omega)]
    simp only [jwalk]
    split_ifs with h0 hlt
    · rw [h0] at hp; push_cast at hp; omega
    · omega
    · have heq : legPos a b x = legLen a b := by omega
      rw [heq, Nat.sub_self, jwalk_zero b rest]
      omega

end HPC.Fold.Z77
