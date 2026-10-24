import HPC.Hagopian.H76Descent

/-!
# Batch 174, items B and C: Hagopian's collection `I` is finite; `e` and `x₂ = e`

Commission 174 §1, §2.B–C; Hagopian 1976, p. 347: "Let `I` be the collection of all intervals
`[x, y]` such that `d⁻¹[[x, y]]` is irreducible with respect to containing a component of
`F ∩ π⁻¹[D]` whose closure meets `π⁻¹[(p₁, r)]` and `π⁻¹[(p₅, s)]`. It follows from Property 3 that
`I` is finite."

* `crossSet G π F D'`: the set `G ∩ π⁻¹[D]`, `D = F[D′]`.
* `IsCrossingComponent`: a component of `G ∩ π⁻¹[D]` whose closure meets both closed side segments.
* `IsIrreducibleInterval d C x y`: `[x, y]` is the least interval with `C ⊆ d⁻¹[[x, y]]`.
* `crossingIntervals`: Hagopian's `I`.

The route is commission 174 §1, steps 1–5: the closure of a crossing component contains the whole
layers over the interior of its interval (`layerSet_Ioo_subset`); two crossing components whose
intervals have overlapping interiors coincide (a component of `G ∩ π⁻¹[D]` is closed in it);
distinct members of `I` have disjoint interiors; each has length `≥ λ` (`crossing_length_pos_all`,
which covers the end element, §1.6); so `I` is finite.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section IFinite

variable {M : Set Pt}

theorem isClosed_layerSet_Icc {G : Set M} {d : G → unitInterval} (hG : IsMinimalAdmissible G d)
    (x y : unitInterval) : IsClosed (layerSet d (Icc x y)) :=
  (isCompact_img hG.isCompact hG.2.1.1 isClosed_Icc).isClosed

variable [CompactSpace M]

variable [ConnectedSpace M]

end IFinite

end HPC.Hagopian
