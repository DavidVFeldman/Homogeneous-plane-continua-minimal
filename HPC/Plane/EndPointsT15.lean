import HPC.Plane.EndPointsAux

/-!
# Batch 85: the construction behind Bing 1951, Theorem 15

A nondegenerate snake-like continuum `M` carries a sequence of chains `C_i` covering `M` (every
link meeting `M`, mesh `→ 0`, the closure of every link of `C_{i+1}` inside a link of `C_i`)
together with index pairs `s_i + 2 ≤ t_i` such that the closures of the links `s_{i+1}`, `t_{i+1}`
lie in the links `s_i`, `t_i`, and the links of `C_{i+1}` between `s_{i+1}` and `t_{i+1}` have
closures in links of `C_i` between `s_i` and `t_i` (Bing's subchains `D_i`). The step is
`exists_next_level`; the index argument is a discrete intermediate value theorem.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

/-- A bounded set containing `z` has closure inside the closed ball about `z` of radius its
diameter. -/
theorem closure_subset_closedBall_diam {S : Set X} (hS : Bornology.IsBounded S) {z : X}
    (hz : z ∈ S) : closure S ⊆ closedBall z (diam S) :=
  closure_minimal (fun _ hw => mem_closedBall.mpr (dist_le_diam_of_mem hS hw hz)) isClosed_closedBall

/-- Chains of arbitrarily small mesh covering a connected set can be taken with every link
meeting it. -/
theorem exists_cover_meeting {M : Set X} (hMconn : IsPreconnected M) (hMne : M.Nonempty)
    (hsnake : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (D : Chain X n), IsEpsChain D ε ∧ M ⊆ D.union ∧ ∀ i, (D.link i ∩ M).Nonempty := by
  obtain ⟨n, D, hDε, hMD⟩ := hsnake ε hε
  obtain ⟨z, hz⟩ := hMne
  obtain ⟨i₀, hi₀, hzi₀⟩ := (mem_union_iff_linkN D).mp (hMD hz)
  obtain ⟨a, k, E, -, -, hakn, hlink, hcov, hmeet, -⟩ := exists_chain_of_weak (n := n) (linkN D)
    (isOpen_linkN D) (fun i j hij _ => disjoint_linkN D hij) hMconn
    (fun x hx => by
      obtain ⟨i, hi, hx⟩ := (mem_union_iff_linkN D).mp (hMD hx)
      exact mem_iUnion₂.mpr ⟨i, hi, hx⟩) hi₀ ⟨z, hzi₀, hz⟩
  refine ⟨k, E, fun t => ?_, hcov, hmeet⟩
  rw [hlink t, linkN_of_lt D (by omega)]
  exact hDε _

end HPC.Plane
