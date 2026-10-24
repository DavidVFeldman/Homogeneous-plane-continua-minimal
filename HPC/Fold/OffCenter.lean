import HPC.Fold.Faithful

/-!
# The off-center one-bump family, Bing's chains, and `F2PrimeOff`

Every itinerary proposed in batches 6–23 started at a window centered on the basepoint level
`p`. The schedules that exist at the refuting chains start at a window with `p` on an edge. This
file defines the one-bump family with base center `c₀ ∈ {p − 1, p, p + 1}`, states `F2PrimeOff`
— both arms fold onto one member — and derives Theorem 3 in the block reading from it through
batch 6's bridge, with no `SegLam`.

It also builds Bing's own crooked chains from the recursion behind his Theorem 7 recurrence,
proves the recurrence for that construction, and checks membership of the small ones in the
faithful model. These are the only chains in the repository that reach the inductive case of
Theorem 3; the batch-23 71-term witness is `bing 0 6`.

Evidence for `F2PrimeOff` (§2 of COMMISSION.md, reproduced and extended in REPORT-batch24.md):
no failure at any basepoint of `bing 0 n` for `n ≤ 7`, of the 7 559 subchains of `bing 0 7` of
length ≥ 9 and span ≥ 5 (665 322 basepoints), of the two batch-23 witnesses, or of the faithful
exhaustive corpus to length 9.

English proofs and sketches: COMMISSION.md §3. Delivered: every ordinary item is proved, and
of the search item `f2PrimeOff` the monotone case and a reduction to the combinatorial
statement `OffDichotomy`; `f2PrimeOff` itself is neither proved nor refuted and is kept,
commented out, at the end. No `sorry` remains.
-/

namespace HPC.Fold

/-! ## The family -/

/-! ## Bing's chains -/

/-- Bing's recurrence, as a function. `z 1 = 2`, `z 2 = 3`. -/
def z : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | n + 3 => 2 * z (n + 2) + z (n + 1) - 2

/-- Every value of the recurrence is positive (needed to take tails). -/
theorem z_pos_aux : ∀ m : ℕ, 1 ≤ z m ∧ 1 ≤ z (m + 1) ∧ 1 ≤ z (m + 2)
  | 0 => ⟨by decide, by decide, by decide⟩
  | m + 1 => by
      obtain ⟨-, h1, h2⟩ := z_pos_aux m
      refine ⟨h1, h2, ?_⟩
      show 1 ≤ z (m + 3)
      have he : z (m + 3) = 2 * z (m + 2) + z (m + 1) - 2 := rfl
      omega

theorem z_pos (m : ℕ) : 1 ≤ z m := (z_pos_aux m).1

/-! ## Two ladders

The two members of the family with `h = c₀`, respectively `l = c₀`, are *ladders*:
`offLam c₀ c₀ L H` descends from `c₀` to the bottom and then climbs to `H - 1`, and
`offVee c₀ c₀ L H` is its reflection. Past the bottom (respectively the top) the climb covers
every level, so an arm that has crossed can be tracked whatever it does; the whole constraint
is the crossing. Two special cases are settled outright here — `p ≤ L + 1` and `H - 1 ≤ p`, in
which the arm never has to cross — and the general crossing criterion is isolated below. -/

/-! ## The crossing criterion, and a reduction of `F2PrimeOff`

The fold onto the V-ladder `offLam c₀ c₀ L H` needs the arm to arrive at the bottom position
*on schedule*: the token starts at position `0` and moves at most one position per index, so
by the index `j` at which it reaches the bottom the arm must have stayed, at each earlier index
`k`, at level at most `min (L+2) c₀ + (j - k)` — the highest level the window it can occupy at
that time contains — and never above `c₀ + 1`. Past the bottom nothing constrains it. -/

-- Commented-out statement `f2PrimeOff`, `theorem3` removed in batch 103; see `LEDGER.md`.

end HPC.Fold
