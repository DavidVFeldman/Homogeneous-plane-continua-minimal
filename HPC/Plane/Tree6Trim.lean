import HPC.Plane.Tree6Cut

/-!
# Batch 118, auxiliary: threading a closed chain of simple arcs through a circular chain

For connected open sets `D 0, …, D (m-1)` (`m ≥ 3`), consecutive ones (cyclically) meeting and no
three of them sharing a point, there are points `P i ∈ D (i-1) ∩ D i` and simple arcs
`A i ⊆ D i` from `P i` to `P (i+1)` (`P m = P 0`) forming a closed chain: consecutive arcs meet
only at their common end (`threaded_nat`).

Choose points `Q i ∈ D (i-1) ∩ D i` and simple arcs `G i ⊆ D i` from `Q i` to `Q (i+1)`; then
trim forward (`trim_chain`): cut the current arc at its first point on `G (i+1)`, and restart
along `G (i+1)` from there; finally close up (`trim_close`): cut the last arc at its first point
on the first one, and start the first one there.
-/

namespace HPC.Plane

open Set Metric

namespace SArcSet

variable {S : Set Pt} {a b : Pt}

end SArcSet

/-! ### A small triangle (the case of a common point of three sets, `m = 3`) -/

theorem mem_segment_prod {x y w : Pt} : w ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    w.1 = x.1 + t * (y.1 - x.1) ∧ w.2 = x.2 + t * (y.2 - x.2) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, by simp, by simp⟩
  · rintro ⟨t, h0, h1, e1, e2⟩
    exact ⟨t, ⟨h0, h1⟩, Prod.ext (by simp [e1]) (by simp [e2])⟩

end HPC.Plane
