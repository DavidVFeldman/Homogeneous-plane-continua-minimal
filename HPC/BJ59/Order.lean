import HPC.Plane.Theorem11Gen

/-!
# Batch 198, library: the order of links along an arc of continua (Bing–Jones, Theorem 2)

The combinatorial core of Bing–Jones's Theorem 2 (p. 174), for arbitrary sets: `order_core`.
The printed proof leaves one step (commission 198, §6): that `G(b, c)` meets the link `d_t` lying
between the links meeting `G(0, b)` and those meeting `G(c, 1)`. Here `d_t` meets neither, so (the
chain covering the whole space) it meets `G(b, c)`.
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- Two disjoint compact sets are a positive distance apart. -/
theorem exists_sep_of_disjoint {P Q : Set X} (hP : IsCompact P) (hQ : IsCompact Q)
    (hPQ : Disjoint P Q) : ∃ ε > 0, ∀ x ∈ P, ∀ y ∈ Q, ε ≤ dist x y := by
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
  rcases Q.eq_empty_or_nonempty with rfl | hQne
  · exact ⟨1, one_pos, fun x _ y hy => absurd hy (notMem_empty y)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hP.exists_isMinOn hPne (continuous_infDist_pt Q).continuousOn
  refine ⟨infDist x₀ Q, ?_, fun x hx y hy => (hmin hx).trans (infDist_le_dist_of_mem hy)⟩
  exact (hQ.isClosed.notMem_iff_infDist_pos hQne).1 (Set.disjoint_left.1 hPQ hx₀)

end HPC.BJ59
