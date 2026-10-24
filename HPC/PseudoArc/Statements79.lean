import HPC.PseudoArc.Theorem10

/-!
# Bing 1948, Theorems 5, 6 and 13: statements

Batch 79, target 3. Statements only: each theorem is a `def … : Prop`, so that this file adds no
`sorry`; the next batch proves `∀ Δ, Theorem5Statement Δ` and so on. The auxiliary notions the
statements need are defined here: the re-indexed description `Description.shift`, a pattern
between two indices (`IsPatternFromTo`), a consolidation of a set of links (`IsConsolidationOn`),
the composant of a point, and Bing's subchain `D_i(R, S)` (`IsSubchainFrom`).

Conventions. The repository's descriptions are indexed from `0`: Bing's `D_1, D_2, …` are
`Δ.D 0, Δ.D 1, …`, and Bing's link `d(i)_r` is `(Δ.D (i-1)).link (r-1)`. The mesh bound `1/i` is
the description's `ε i` (any bound tending to `0`). "The closure of each link is a compact subset
of a link" is `Δ.closure_subset` together with `[CompactSpace X]`, which is assumed where
compactness is used.

## `PatternFollowing` versus Theorem 6

`Description.PatternFollowing Δ` asks, for *every* level `i` and every pattern `x` in `Δ.D i`,
for a level `j > i` and a chain from `P` to `Q` consolidating `Δ.D j` and following `x` in
`Δ.D i`. Theorem 6 (`Theorem6Statement Δ`) is the same for level `0` only, and asks for some
level `j`, not necessarily `j > 0`. Re-indexing (`Δ.shift i`, whose level `j` is `Δ.D (i + j)`)
turns one into the other, with two differences recorded as proved statements below:

* `theorem6_shift_of_patternFollowing`: `PatternFollowing Δ` gives Theorem 6 for every shift of
  `Δ` (indeed with `0 < j`).
* `patternFollowing_of_theorem6Pos`: Theorem 6 for every shift, *with `0 < j`* (Bing's proof of
  Theorem 6 produces a deep level, so this is what it gives), gives `PatternFollowing Δ`.

So the only gap between Bing's Theorem 6 as stated and the hypothesis of Theorem 12 is the
requirement `j > i`, and Bing's statement is applied to every tail `D_i, D_{i+1}, …` of the
sequence, which is again a description.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Description

variable {P Q : X}

/-- The tail of a description from level `i`: its level `j` is level `i + j` of `Δ`. -/
def shift (Δ : Description X P Q) (i : ℕ) : Description X P Q where
  n j := Δ.n (i + j)
  D j := Δ.D (i + j)
  isFrom j := Δ.isFrom (i + j)
  crooked j := Δ.crooked (i + j)
  closure_subset j := Δ.closure_subset (i + j)
  ε j := Δ.ε (i + j)
  ε_pos j := Δ.ε_pos (i + j)
  ε_tendsto := Δ.ε_tendsto.comp (Filter.tendsto_atTop_atTop_of_monotone
    (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
  bdd j := Δ.bdd (i + j)
  diam_le j := Δ.diam_le (i + j)

@[simp] theorem shift_n (Δ : Description X P Q) (i j : ℕ) : (Δ.shift i).n j = Δ.n (i + j) := rfl

@[simp] theorem shift_D (Δ : Description X P Q) (i j : ℕ) : (Δ.shift i).D j = Δ.D (i + j) := rfl

/-! ## Theorem 6 -/

/-- Theorem 6 with a level `j > 0`, which is what Bing's proof produces. -/
def Theorem6PosStatement (Δ : Description X P Q) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Fin (Δ.n 0)), IsPattern x →
    ∃ j, 0 < j ∧ ∃ E : Chain X N, E.IsFrom P Q ∧ E.IsConsolidationOf (Δ.D j) ∧
      E.FollowsPattern x (Δ.D 0)

/-- Theorem 6 with `j > 0` for every tail of the description gives `PatternFollowing`. -/
theorem patternFollowing_of_theorem6Pos (Δ : Description X P Q)
    (h : ∀ i, Theorem6PosStatement (Δ.shift i)) : Δ.PatternFollowing := by
  intro i N x hx
  obtain ⟨d, hd, E, hE1, hE2, hE3⟩ := h i N x hx
  exact ⟨i + d, by omega, E, hE1, hE2, hE3⟩

/-! ## Theorem 5 -/

end Description

/-! ## Theorem 13 and its two auxiliary notions -/

/-- The **composant** of `p` in `M`: the union of all proper subcontinua of `M` containing `p`. -/
def composant (M : Set X) (p : X) : Set X :=
  ⋃₀ {K | Fold.Q78.IsContinuum K ∧ K ⊆ M ∧ K ≠ M ∧ p ∈ K}

namespace Chain

/-- Bing's subchain `D(R, S)` (p. 740): the subchain of `D` from link `a` to link `b` (in
either order of the two points) is a chain from `R` to `S` — `R` lies in its first link and in
no other, `S` in its last and in no other. -/
def IsSubchainFrom {n : ℕ} (D : Chain X n) (a b : Fin n) (R S : X) : Prop :=
  ∃ hab : a ≤ b, (D.sub a b hab).IsFrom R S ∨ (D.sub a b hab).IsFrom S R

end Chain

namespace Description

variable {P Q : X}

end Description

end HPC
