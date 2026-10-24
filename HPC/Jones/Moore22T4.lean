import HPC.Jones.Moore22
import HPC.Moore.M25Plane
import HPC.Plane.Tree7Star
import HPC.Jones.Jones49Why

/-!
# Batch 150, item B: Moore 1922, Theorem 4 — the general (non-planar-separation) steps

Steps of Theorem 4 that do not use plane separation by continua:

* `isPreconnected_compl_of_mooreSimplyConnected`: the complement of a bounded open set which is
  simply connected in Moore's sense is connected (a bounded clopen piece `E₂` of the complement
  would give the bounded set `H = thickening (δ/2) E₂`, whose frontier lies in `R` but which is not
  contained in `R`);
* `isConnected_frontier_of_mooreSimplyConnected`: hence (unicoherence of the plane) the boundary of
  a bounded, connected, open, Moore-simply-connected set is connected;
* `locallyConnectedSpace_of_cikAt`: a set connected im kleinen at each of its points is locally
  connected (as a space);
* `exists_crossing_continua`: the reconstruction of the cited PNAS argument — from a point `P` of a
  continuum `M` at which `M` is not connected im kleinen, two concentric squares about `P` and
  infinitely many mutually disjoint subcontinua of `M` each meeting both squares and lying between
  them.
-/

namespace HPC.Jones

open Set Topology Metric HPC.Plane

/-- **Connected im kleinen at every point implies locally connected.** For a set `M` of the
plane, viewed as a space. -/
theorem locallyConnectedSpace_of_cikAt {M : Set Pt} (h : ∀ P ∈ M, CikAt M P) :
    LocallyConnectedSpace M := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hxF
  rw [Metric.isOpen_iff]
  intro y hy
  have hyF : y ∈ F := connectedComponentIn_subset _ _ hy
  obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.1 hF y hyF
  obtain ⟨δ, hδ, hδC⟩ := h y y.2 ε hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨C, hCM, hCc, hzC, hyC, hCb, hCd⟩ := hδC z z.2 (mem_ball.1 hz)
  set C' : Set M := Subtype.val ⁻¹' C
  have hCimg : Subtype.val '' C' = C := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]; exact inter_eq_left.2 hCM
  have hC'c : IsPreconnected C' := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hCimg]; exact hCc
  have hC'F : C' ⊆ F := by
    intro w hw
    apply hεF
    rw [mem_ball, Subtype.dist_eq]
    exact (dist_le_diam_of_mem hCb hw hyC).trans_lt hCd
  have hC'sub := hC'c.subset_connectedComponentIn (x := y) hyC hC'F
  rw [connectedComponentIn_eq hy]
  exact hC'sub hzC

end HPC.Jones
