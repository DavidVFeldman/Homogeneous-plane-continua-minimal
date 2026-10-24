import HPC.Plane.PseudoArc51
import HPC.Chains.Basic

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §4: monotone decompositions

Skeleton for batch 89 (save as `HPC/Plane/Monotone51.lean`; add `import HPC.Plane.Monotone51` to
the root `HPC.lean`). The skeleton's proofs were all `sorry` work items. Shapes may be adjusted
with the change recorded; `theorem3_HIC` and `theorem4_HIC` keep their conclusions.

A monotone decomposition of `M` is given by a continuous surjection with connected fibres
(COMMISSION-batch89.md §3.1). `IsSnakeLike`, `IsHereditarilyIndecomposable`, `IsPseudoArc` are
from `Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.

**Batch 89 delivery.** All five statements are proved as stated (no shape changes). Theorem 3 uses
the combinatorial lemma `Mono.exists_chain_of_intervals` (`HPC/Plane/Monotone51Comb.lean`): Bing's
windows `D(n_{3k+1}, n_{3k+5})`, with his `n_i` replaced by strictly increasing block boundaries
(see that file and `REPORT-batch89.md`). The chain obtained in the space `M'` is lifted to `Y` by
`PA51.liftChain` (batch 88). The monotone image of a hereditarily indecomposable continuum is
hereditarily indecomposable because preimages of connected subsets of `M'` are connected
(`isConnected_inter_preimage`, a direct argument with the closed sets `f '' (M ∩ u)`).
-/

namespace HPC.Plane

open Set

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `f` is a **monotone map** of `M` onto `M'`: continuous on `M`, with image `M'`, and with every
fibre `M ∩ f ⁻¹' {y}` (for `y ∈ M'`) connected. Bing's "upper semi-continuous collection of
continua filling `M`" is the collection of fibres. -/
def IsMonotoneMap (f : X → Y) (M : Set X) (M' : Set Y) : Prop :=
  ContinuousOn f M ∧ f '' M = M' ∧ ∀ y ∈ M', IsConnected (M ∩ f ⁻¹' {y})

namespace Mono

omit [MetricSpace X] [MetricSpace Y] in
/-- The full preimage (inside `M`) of a subset of `M'` maps onto it. -/
theorem image_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hfM : f '' M = M')
    {S : Set Y} (hS : S ⊆ M') : f '' (M ∩ f ⁻¹' S) = S := by
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hS hy : y ∈ f '' M)
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- **The preimage of a connected set under a monotone map of a compact set is connected.**
For closed `u`, `v` covering the preimage `K` and both meeting it, the compact (hence closed)
images `f '' (M ∩ u)` and `f '' (M ∩ v)` cover `K'` and both meet it, so they share a point `y` of
`K'`; the connected fibre over `y` lies in `K ⊆ u ∪ v` and meets both, hence meets `u ∩ v`. -/
theorem isConnected_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hMc : IsCompact M)
    (hf : IsMonotoneMap f M M') {K' : Set Y} (hK' : IsConnected K') (hKM : K' ⊆ M') :
    IsConnected (M ∩ f ⁻¹' K') := by
  obtain ⟨hfc, hfM, hfib⟩ := hf
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hK'.nonempty
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hKM hy : y ∈ f '' M)
    exact ⟨x, hx, hy⟩
  rw [isPreconnected_closed_iff]
  intro u v hu hv hcov hKu hKv
  have hA : IsClosed (f '' (M ∩ u)) :=
    ((hMc.inter_right hu).image_of_continuousOn (hfc.mono inter_subset_left)).isClosed
  have hB : IsClosed (f '' (M ∩ v)) :=
    ((hMc.inter_right hv).image_of_continuousOn (hfc.mono inter_subset_left)).isClosed
  have hcov' : K' ⊆ f '' (M ∩ u) ∪ f '' (M ∩ v) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hfM ▸ hKM hy : y ∈ f '' M)
    rcases hcov ⟨hx, hy⟩ with h | h
    · exact Or.inl ⟨x, ⟨hx, h⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩
  have hK'u : (K' ∩ f '' (M ∩ u)).Nonempty := by
    obtain ⟨x, ⟨hxM, hxK⟩, hxu⟩ := hKu
    exact ⟨f x, hxK, x, ⟨hxM, hxu⟩, rfl⟩
  have hK'v : (K' ∩ f '' (M ∩ v)).Nonempty := by
    obtain ⟨x, ⟨hxM, hxK⟩, hxv⟩ := hKv
    exact ⟨f x, hxK, x, ⟨hxM, hxv⟩, rfl⟩
  obtain ⟨y, hyK, ⟨x₁, ⟨hx₁M, hx₁u⟩, hx₁⟩, ⟨x₂, ⟨hx₂M, hx₂v⟩, hx₂⟩⟩ :=
    isPreconnected_closed_iff.mp hK'.isPreconnected _ _ hA hB hcov' hK'u hK'v
  have hF := (hfib y (hKM hyK)).isPreconnected
  have hFK : M ∩ f ⁻¹' {y} ⊆ M ∩ f ⁻¹' K' := fun x hx =>
    ⟨hx.1, by rw [mem_preimage, show f x = y from hx.2]; exact hyK⟩
  obtain ⟨x, hxF, hxu, hxv⟩ := isPreconnected_closed_iff.mp hF u v hu hv (hFK.trans hcov)
    ⟨x₁, ⟨hx₁M, hx₁⟩, hx₁u⟩ ⟨x₂, ⟨hx₂M, hx₂⟩, hx₂v⟩
  exact ⟨x, hFK hxF, hxu, hxv⟩

/-- The full preimage (inside `M`) of a continuum in `M'` is a continuum. -/
theorem isContinuum_inter_preimage {f : X → Y} {M : Set X} {M' : Set Y} (hMc : IsCompact M)
    (hf : IsMonotoneMap f M M') {K' : Set Y} (hK' : Fold.Q78.IsContinuum K') (hKM : K' ⊆ M') :
    Fold.Q78.IsContinuum (M ∩ f ⁻¹' K') :=
  ⟨hMc.of_isClosed_subset (hf.1.preimage_isClosed_of_isClosed hMc.isClosed hK'.1.isClosed)
      inter_subset_left,
    isConnected_inter_preimage hMc hf hK'.2 hKM⟩

end Mono

/-- The monotone image of a hereditarily indecomposable continuum is hereditarily
indecomposable. -/
theorem isHereditarilyIndecomposable_image {f : X → Y} {M : Set X} {M' : Set Y}
    (hM : Fold.Q78.IsContinuum M) (hHI : IsHereditarilyIndecomposable M)
    (hf : IsMonotoneMap f M M') : IsHereditarilyIndecomposable M' := by
  intro K' hK'M hK'
  refine ⟨hK', fun A' B' hA' hB' hA'K hB'K hAB => ?_⟩
  have hK := Mono.isContinuum_inter_preimage hM.1 hf hK' hK'M
  have hA := Mono.isContinuum_inter_preimage hM.1 hf hA' (hA'K.trans hK'M)
  have hB := Mono.isContinuum_inter_preimage hM.1 hf hB' (hB'K.trans hK'M)
  have hunion : M ∩ f ⁻¹' A' ∪ M ∩ f ⁻¹' B' = M ∩ f ⁻¹' K' := by
    rw [← inter_union_distrib_left, ← preimage_union, hAB]
  rcases (hHI _ inter_subset_left hK).2 _ _ hA hB
      (inter_subset_inter_right _ (preimage_mono hA'K))
      (inter_subset_inter_right _ (preimage_mono hB'K)) hunion with h | h
  · left
    have := congrArg (f '' ·) h
    simpa only [Mono.image_inter_preimage hf.2.1 (hA'K.trans hK'M),
      Mono.image_inter_preimage hf.2.1 hK'M] using this
  · right
    have := congrArg (f '' ·) h
    simpa only [Mono.image_inter_preimage hf.2.1 (hB'K.trans hK'M),
      Mono.image_inter_preimage hf.2.1 hK'M] using this

end HPC.Plane
