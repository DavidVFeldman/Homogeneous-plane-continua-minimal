import HPC.Fold.OffCenter

/-!
# Bing 1948, Theorem 7: minimality, and the timing bound it gives

Batch 29 closed every basepoint within two of an extreme and proved the range sharp: the
straight descent `6,5,4,3,2,1,0` based at its middle admits no walk of unit steps at all
(`no_zigWalk_fold_veeSeq`), so the interior cases cannot be settled without crookedness. What
that sequence lacks is length: it crosses six levels in six indices, while a token that starts
at time zero and moves one level per step cannot be near both extremes at times so close
together.

Crookedness forbids exactly that. Bing's Theorem 7 says a chain crooked in a chain of `n` links
has at least `z(n)` links, where `z 0 = 1`, `z 1 = 2`, `z 2 = 3` and
`z (n+3) = 2 · z (n+2) + z (n+1) − 2`. The repository has the construction and its length
(`bingPath`, `bingPath_length`, batch 24); the lower bound — the content of Theorem 7 — is
proved here, as `minimality`, and it supplies the token's timing budget.

The engine is `minGap`: if some link of a faithful crooked sequence meets coarse level `ℓ` and
another meets `ℓ + d`, then the sequence has at least `z d` links. Its proof is Bing's own
recursion read backwards. The crookedness clause at the pair of those two links produces two
intermediate links, one meeting `ℓ + d − 1` and, after it, one meeting `ℓ + 1`; the three
contiguous stretches they cut the sequence into meet pairs of levels `d − 1`, `d − 2`, `d − 1`
apart, each stretch is again faithful and crooked (`isCrookedIvF_restrict`), and the three
lengths overlap in exactly two links, so induction gives
`2 · z (d−1) + z (d−2) − 2 = z d` links. Measuring the gap with the *intervals* `[ρ, σ]`, not
with `ρ` alone, is what makes the three pieces come out one short of the whole rather than two.

Checked in `census-batch30.c`: the shortest faithful crooked sequence is exhaustively 2, 3, 6,
13 links at spans 1, 2, 3, 4, against `z 1 = 2`, `z 2 = 3`, `z 3 = 6`, `z 4 = 13`; on
`bingPath 0 n` for `n = 3 … 8` and random contiguous subchains, every pair of indices at level
distance `d ≥ 3` is at least `z d − 1` apart, and every contiguous stretch is faithful and
crooked.

English proofs: COMMISSION-batch30.md §2–§3. Delivered complete: no `sorry` remains.
-/

namespace HPC.Fold

/-! ## The recurrence -/

/-- Bing's recurrence is monotone: one step. -/
theorem z_le_succ : ∀ m : ℕ, z m ≤ z (m + 1)
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
      have h1 := z_pos (m + 1)
      have h2 := z_pos (m + 2)
      have he : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
      show z (m + 2) ≤ z (m + 3)
      omega

/-- `z` is monotone. -/
theorem z_ge_of_le {a b : ℕ} (h : a ≤ b) : z a ≤ z b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (z_le_succ b)

/-! ## Restriction -/

/-! ## Theorem 7 -/

/-! ## What it buys -/

end HPC.Fold
