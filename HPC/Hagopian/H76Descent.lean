import HPC.Hagopian.H76Translate
import HPC.Hagopian.H76PairSep
import HPC.Hagopian.H76Lemma5End
import HPC.Hagopian.H76D1
import HPC.Hagopian.H75KurMap
import HPC.Hagopian.Hagopian76E
import HPC.Jones.Basic

/-!
# Batch 173, item A: Property 3 by descent (supporting file)

Commission 173 §1. The objects of the descent are *layer crossings*: connected subsets `Z` of one
layer `d⁻¹(u)` of the extension `G`, lying over the closure of Hagopian's domain `D = F[D′]` and
meeting the two closed side segments over `3/22` and `19/22` (`LayerCrossing`). The set of such
`u` is closed (`isClosed_layerCrossing`, from `crossing_set_closed`); it is defined by continua, not
by maps, as the commission asks.

* `IsCrossRegion`: the properties of `D = F[D′]` used (open, inside the open strip of height `c₁`
  over `(3/22, 19/22)`, frontier meeting `π[M]` only over the axis and the two side segments: the
  top arc `I₂` misses `π[M]`, T7).
* `layerCrossing_disjoint`: a layer containing a layer crossing misses `E` (commission D1.1, in the
  form: a layer of `E` projects to one point of the axis).
* `crossing_from_layer_translate_aux` (**D1**): a layer `d⁻¹(u)` containing `ψ[E]`, for a continuous
  `ψ : M → M` moving points less than `2ε₁` and with one middle point `ψ(x)`, `k(x) ∈ [4/11, 7/11]`,
  over `D`, misses `E` and contains a layer crossing. Boundary bumping in `ψ[k⁻¹[[0, k(x)]]]` and
  `ψ[k⁻¹[[k(x), 1]]]` from `ψ(x)`; the frontier point is not over `I₂` (misses `π[M]`), not over
  the axis (the layer misses `E`), and not over the far side (coarse monotonicity, `IsEps1.sep`).
* `crossing_descends_aux` (**D2**): a layer crossing in an interior layer `d⁻¹(v)` gives one in
  some `d⁻¹(u)`, `0 < u < v`: `hagopian76_property3_translate` gives `h` with `h[G] ⊆ d⁻¹(v)`; the
  point `h(x)`, `k(x) = 1/2`, lies over `D`; the shift `g` (`hagopian76_property3_shift`) small
  enough to keep `gh(x)` over `D`; then D1 with `ψ = g ∘ h`.
* `property3_layer_aux`: no interior layer contains a layer crossing (least element of the closed
  set of crossing parameters below `v`, against D2).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## Elevenths -/

variable {M : Set Pt}

/-! ## Layers of an extension meeting `E` -/

section Layers

variable [CompactSpace M] [ConnectedSpace M]

end Layers

/-! ## Hagopian's domain and layer crossings -/

theorem isClosed_layer {G : Set M} {d : G → unitInterval} (hG : IsCompact G) (hd : Continuous d)
    (u : unitInterval) : IsClosed (layer d u) :=
  (isCompact_img hG hd isClosed_singleton).isClosed

section Crossing

variable [CompactSpace M] [ConnectedSpace M]

end Crossing

end HPC.Hagopian

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Length

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

end Length

end HPC.Hagopian
