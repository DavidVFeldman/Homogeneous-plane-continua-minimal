import HPC.PseudoArc.Theorem13
import HPC.Fold.BingCrook
import HPC.Fold.Pair79Chain
import HPC.Fold.Minimal
import HPC.Fold.OffCenter
import HPC.Fold.Faithful
import HPC.Fold.Zig77Main
import HPC.Fold.Splice78
import Mathlib.Tactic
import HPC.Plane.Descr
import HPC.Plane.Transfer
import HPC.Plane.RealStep
import HPC.Plane.Joints
import HPC.Chains.Basic
import HPC.PseudoArc.Uniqueness

/-!
# Bing 1951, *Snake-like continua*: Theorem 4, and a description in the plane

Batch 84 (COMMISSION-batch84.md). The skeleton's four definitions are kept verbatim. The skeleton's
`exists_rect_chain_following` is **false as stated** (counterexample: `HPC/Plane/Counter.lean`,
`rectStepSkeleton_false`); it is commented out below with the reason, and replaced by a reshaped
statement about *tame* chains (images of a row of standard rectangles under a homeomorphism of the
plane, `IsTame`, `HPC/Plane/StdChain.lean`) along *slow* patterns. `theorem4`,
`exists_description_plane` and `pseudoArc_exists` keep their conclusions.

The plane is `ℝ × ℝ` with its product (sup) metric (`Pt`, defined in `HPC/Plane/StdChain.lean`).
-/

namespace HPC.Plane

open Set

-- Commented-out statement `exists_rect_chain_following` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- An `ε`-chain: bounded links of diameter less than `ε` (Bing 1951, §1). -/
def IsEpsChain {X : Type*} [MetricSpace X] {n : ℕ} (D : Chain X n) (ε : ℝ) : Prop :=
  ∀ i, Bornology.IsBounded (D.link i) ∧ Metric.diam (D.link i) < ε

/-- **Snake-like** (Bing 1951, §1): a (compact) continuum that is covered by an `ε`-chain for every
`ε > 0`. -/
def IsSnakeLike {X : Type*} [MetricSpace X] (M : Set X) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union

/-- **A description exists in the plane** (COMMISSION-batch84.md §3.4): tame chains following
stuttered Bing patterns, crooked by tightness (`HPC/Plane/Descr.lean`). -/
theorem exists_description_plane :
    ∃ (P Q : Pt), P ≠ Q ∧ Nonempty (Description Pt P Q) :=
  exists_description_plane'

/-- All links of a description in the plane lie in a compact set: the closure of the (bounded)
union of the links of level `0`. -/
theorem Description.links_subset_compact {P Q : Pt} (Δ : Description Pt P Q) :
    IsCompact (closure (Δ.D 0).union) ∧ ∀ i t, (Δ.D i).link t ⊆ closure (Δ.D 0).union := by
  refine ⟨Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_, fun i t => ?_⟩
  · exact (Bornology.isBounded_iUnion.mpr fun j => Δ.bdd 0 j).closure
  · obtain ⟨s, hs⟩ := Δ.refines_of_le (Nat.zero_le i) t
    exact hs.trans ((subset_iUnion _ s).trans subset_closure)

end HPC.Plane
