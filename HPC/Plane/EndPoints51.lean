import HPC.Plane.Snake51
import HPC.PseudoArc.Theorem14
import HPC.Plane.EndPointsT15

/-!
# Bing 1951, §4 Theorem 10 and §5 (end points of snake-like continua)

Batch 85. The skeleton's seven statements; `theorem10_1951` and `endPoint_of_condA` now live in
`LastLink99.lean`, where they are proved (batches 99–100). Shape changes from the skeleton: the
hypothesis `hM : IsContinuum M` was unused and has been removed from `condB_of_condA`,
`condB_of_endPoint` and `exists_not_endPoint_of_not_HI`; `theorem14_1951` keeps `IsSnakeLike M`
but uses only its continuum part. See `REPORT-batch85.md`.

`IsSnakeLike`, `IsEpsChain` are from `Snake51.lean`; `IsIrreducibleBetween` from
`PseudoArc/Theorem14.lean`; `Fold.Q78.IsContinuum`, `IsIndecomposable` from `Fold/Questions78.lean`.
Bing's "chain from `p` to `q`" is `Chain.IsFrom p q`. Conditions A, B, C are stated for a point
`p` of a set `M`.
-/

namespace HPC.Plane

open Set Filter Topology

variable {X : Type*} [MetricSpace X]

/-- **Condition B**: of two subcontinua of `M` containing `p`, one contains the other. -/
def CondB (M : Set X) (p : X) : Prop :=
  p ∈ M ∧ ∀ H K : Set X, H ⊆ M → K ⊆ M → Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K →
    p ∈ H → p ∈ K → H ⊆ K ∨ K ⊆ H

/-- Hereditarily indecomposable: every subcontinuum is indecomposable. -/
def IsHereditarilyIndecomposable (M : Set X) : Prop :=
  ∀ K : Set X, K ⊆ M → Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K

end HPC.Plane
