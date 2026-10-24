import HPC.Plane.StdChain

/-!
# Batch 150, item B: Moore 1922, Theorems 1–3

R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund. Math. 3 (1922),
232–237. The four definitions of the batch-150 skeleton (verbatim) and Theorems 1–3.

* **Theorem 1** (`moore22_theorem1`): Moore's proof takes a "limiting set" of connected sets
  `tₙ ∋ Aₙ, Pₙ`. Here the limiting set is replaced by an explicit chain: connected sets of
  summable diameters joining points `Pₖ → P`, points `Xₖ → X`, and `X₀` to `P₀`; the union, with
  `X` and `P` added, is connected and lies in `M̄`. (The printed proof has `tₙ` "within `K*`";
  it should be within `K̄`, see the ledger.)
* **Theorem 2** (`moore22_theorem2`): Moore's proof (the set `M_s + P`, `P ∈ M̄_s`), run with the
  finitely many pieces whose closure contains `P` rather than with a sequence.
* **Theorem 3** (`moore22_theorem3`): Moore's proof with `ε/3` in place of `ε` (as printed, the
  sets `M_K` have diameter `≤ 2ε`, see the ledger).
-/

namespace HPC.Jones

open Set Topology Metric

section Moore22

open HPC.Plane

/-- *Connected im kleinen at `P`* (p. 233): for every `ε` there is `δ` such that each point `X` of
`M` within `δ` of `P` lies with `P` in a connected subset of `M` of diameter less than `ε`. -/
def CikAt (M : Set Pt) (P : Pt) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ X ∈ M, dist X P < δ → ∃ C ⊆ M, IsPreconnected C ∧ X ∈ C ∧ P ∈ C ∧
    Bornology.IsBounded C ∧ diam C < ε

/-- A set lying in a closed ball of radius `r` has diameter `≤ 2r`. -/
theorem diam_le_of_subset_closedBall' {S : Set Pt} {c : Pt} {r : ℝ} (hr : 0 ≤ r)
    (h : S ⊆ closedBall c r) : diam S ≤ 2 * r :=
  (diam_mono h isBounded_closedBall).trans (diam_closedBall hr)

end Moore22

end HPC.Jones
