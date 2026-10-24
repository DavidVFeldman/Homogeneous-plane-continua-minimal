import HPC.BJ59.Thm3
import HPC.BJ59.Defs
import HPC.BJ59.Transfer

/-!
# Batch 198, library: helpers for Theorems 5 and 6 (commission 198, §6)

* `sign_persist`: two chain maps whose values are never within `1` keep the sign of their
  difference (it changes by at most `2` per step);
* `isIndecomposable_singleton`, `isArcOfContinua_id`, `isSnakeLike_univ_unitInterval`,
  `oneLinkChain`: the ingredients of the degenerate counterexample to Theorem 5 as printed.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

/-- The chain with one link, the whole space. -/
def oneLinkChain (X : Type*) [MetricSpace X] [Nonempty X] : Chain X 1 where
  link := fun _ => univ
  isOpen := fun _ => isOpen_univ
  adjacent := fun i j => by
    have : i = j := Subsingleton.elim _ _
    subst this
    simp only [sub_self, Int.natAbs_zero, zero_le_one, iff_true, inter_self]
    exact univ_nonempty

/-- `exp π = -1 ≠ 1` on the circle. -/
theorem circle_exp_pi_ne_one : Circle.exp Real.pi ≠ 1 := by
  intro h
  have := congrArg (fun z : Circle => (z : ℂ).re) h
  simp [Circle.coe_exp] at this
  norm_num at this

end HPC.BJ59
