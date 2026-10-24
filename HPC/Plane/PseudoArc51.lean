import HPC.Plane.EndPoints51
import HPC.PseudoArc.Theorem14
import HPC.Fold.BingCrook
import HPC.Fold.Pair79Chain
import HPC.Fold.Theorem4Pair
import HPC.Plane.PA51Lift
import HPC.Plane.Snake51

/-!
# Bing, *Concerning hereditarily indecomposable continua* (Pacific J. Math. 1 (1951), 43–51),
# Theorem 1 and its consequences

Batch 88 (COMMISSION-batch88.md). The skeleton's definition and nine statements. Seven are proved
as stated. Two are **false as stated** and are kept below in comments, each with a Lean refutation
and a reshaped, proved replacement:

* `theorem12_of` (Theorem 12 with `IsCompact Δ.M` in place of a compact ambient space): refuted by
  `theorem12_of_false`. A description in a non-complete space can describe a compact set that is
  not connected (`PA51.exists_description_compact_disconnected`: the plane description with every
  point of its continuum except `P`, `Q` removed from the plane). Reshaped: the links of each
  description lie in a compact set, as in `Transfer.lean`.
* `isPseudoArc_of_description` (same hypothesis `IsCompact Δ.M`): refuted by
  `isPseudoArc_of_description_false`, same counterexample. Reshaped: links in a compact set
  (`isPseudoArc_of_description`), or a compact ambient space (`isPseudoArc_of_description'`).

`theorem1_HIC`, `theorem1_HIC'`, `isPseudoArc_iff_endPoints` keep their statements, and so do
`exists_description_of_chainable_HI`, `homogeneous_of_isPseudoArc`, `isPseudoArc_of_subcontinuum`
and `oppositeEndPoints_of_composants`. Added: `homeomorphic_subcontinuum`, `theorem1_snake`,
`isPseudoArc_plane`, `pseudoArc_unique`, `exists_not_mem_composant`.

The proof of Theorem 1 (`exists_description_of_chainable_HI`) is in `PA51Crook.lean` (crookedness
eventually, Bing's first paragraph, with a corrected choice of witnesses), `PA51Pre.lean` (the
sequence of mutually crooked chains, and the description from `p` to `q`, in the compact space
`M`), and `PA51Lift.lean` (from the space `M` back to `X`).

`IsSnakeLike` (= Bing's "can be chained"), `IsEpsChain`, `IsEndPoint`, `OppositeEndPoints`,
`IsHereditarilyIndecomposable` are from `Snake51.lean` / `EndPoints51.lean`; `composant` from
`PseudoArc/Statements79.lean`; `Description` from `PseudoArc/Description.lean`.
-/

namespace HPC.Plane

open Set

variable {X : Type*} [MetricSpace X]

/-- **A pseudo-arc**: a nondegenerate chainable hereditarily indecomposable (compact) continuum
(Bing 1951, p. 45: "all of these continua are topologically equivalent and are pseudo-arcs"). -/
def IsPseudoArc (M : Set X) : Prop :=
  IsSnakeLike M ∧ IsHereditarilyIndecomposable M ∧ M.Nontrivial

-- Commented-out statement `theorem12_of` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- **Bing 1951 (Pacific J. Math.), Theorem 1, the "in fact" clause.** -/
theorem theorem1_HIC {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') {p q : X} {p' q' : X'}
    (hp : p ∈ M) (hq : q ∈ M) (hpq : q ∉ composant M p)
    (hp' : p' ∈ M') (hq' : q' ∈ M') (hpq' : q' ∉ composant M' p') :
    ∃ T : M ≃ₜ M', T ⟨p, hp⟩ = ⟨p', hp'⟩ ∧ T ⟨q, hq⟩ = ⟨q', hq'⟩ := by
  obtain ⟨hs, hh, hnd⟩ := hM
  obtain ⟨hs', hh', hnd'⟩ := hM'
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hs.1.1
  haveI : CompactSpace M' := isCompact_iff_compactSpace.mp hs'.1.1
  obtain ⟨Δ₁, hΔ₁⟩ := PA51.exists_description_sub hs hh hnd hp hq hpq
  obtain ⟨Δ₂, hΔ₂⟩ := PA51.exists_description_sub hs' hh' hnd' hp' hq' hpq'
  have hne₁ : (⟨p, hp⟩ : M) ≠ ⟨q, hq⟩ := fun h =>
    PA51.ne_of_not_mem_composant hnd hp hpq (congrArg Subtype.val h)
  have hne₂ : (⟨p', hp'⟩ : M') ≠ ⟨q', hq'⟩ := fun h =>
    PA51.ne_of_not_mem_composant hnd' hp' hpq' (congrArg Subtype.val h)
  obtain ⟨T, hTP, hTQ⟩ := theorem12 Δ₁ Δ₂ hne₁ hne₂
  let e₁ : M ≃ₜ Δ₁.M := (Homeomorph.Set.univ M).symm.trans (Homeomorph.setCongr hΔ₁.symm)
  let e₂ : M' ≃ₜ Δ₂.M := (Homeomorph.Set.univ M').symm.trans (Homeomorph.setCongr hΔ₂.symm)
  refine ⟨(e₁.trans T).trans e₂.symm, ?_, ?_⟩
  · show e₂.symm (T (e₁ ⟨p, hp⟩)) = _
    have e : e₁ ⟨p, hp⟩ = ⟨⟨p, hp⟩, Δ₁.P_mem_M⟩ := rfl
    rw [e, hTP]
    rfl
  · show e₂.symm (T (e₁ ⟨q, hq⟩)) = _
    have e : e₁ ⟨q, hq⟩ = ⟨⟨q, hq⟩, Δ₁.Q_mem_M⟩ := rfl
    rw [e, hTQ]
    rfl

/-- Every point of a pseudo-arc has a point of the pseudo-arc outside its composant
(`composant_ne_of_indecomposable`, Bing 1948 batch 81, applied in the compact space `M`). -/
theorem exists_not_mem_composant {M : Set X} (hM : IsPseudoArc M) {p : X} (hp : p ∈ M) :
    ∃ q ∈ M, q ∉ composant M p := by
  obtain ⟨hs, hh, hnd⟩ := hM
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hs.1.1
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.mp hs.1.2
  have hcont : Fold.Q78.IsContinuum (univ : Set M) := ⟨isCompact_univ, isConnected_univ⟩
  have hnd' : (univ : Set M).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnd
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩
  have hne := composant_ne_of_indecomposable (PA51.hI_sub hh univ hcont) hnd' (mem_univ ⟨p, hp⟩)
  obtain ⟨y, -, hy⟩ : ∃ y ∈ (univ : Set M), y ∉ composant univ ⟨p, hp⟩ := by
    by_contra hcon
    push_neg at hcon
    exact hne (Subset.antisymm (sUnion_subset fun K hK => hK.2.1) hcon)
  refine ⟨y.1, y.2, fun hyc => hy ?_⟩
  obtain ⟨K, ⟨hK, hKM, hKne, hpK⟩, hyK⟩ := mem_sUnion.mp hyc
  refine mem_sUnion.mpr ⟨Subtype.val ⁻¹' K, ⟨⟨?_, ?_⟩, subset_univ _, ?_, hpK⟩, hyK⟩
  · exact hs.1.1.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK.1
  · refine ⟨⟨⟨p, hp⟩, hpK⟩, ?_⟩
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.mpr hKM]
    exact hK.2.isPreconnected
  · intro h
    apply hKne
    refine Subset.antisymm hKM fun x hx => ?_
    have : (⟨x, hx⟩ : M) ∈ Subtype.val ⁻¹' K := h ▸ mem_univ _
    exact this

/-- **Theorem 1**: any two pseudo-arcs are homeomorphic. (Also *Snake-like continua*, Theorem 1.) -/
theorem theorem1_HIC' {X' : Type*} [MetricSpace X'] {M : Set X} {M' : Set X'}
    (hM : IsPseudoArc M) (hM' : IsPseudoArc M') : Nonempty (M ≃ₜ M') := by
  obtain ⟨p, hp, -⟩ := hM.2.2
  obtain ⟨p', hp', -⟩ := hM'.2.2
  obtain ⟨q, hq, hpq⟩ := exists_not_mem_composant hM hp
  obtain ⟨q', hq', hpq'⟩ := exists_not_mem_composant hM' hp'
  obtain ⟨T, -⟩ := theorem1_HIC hM hM' hp hq hpq hp' hq' hpq'
  exact ⟨T⟩

/-- A pseudo-arc is homogeneous (Bing, p. 45). -/
theorem homogeneous_of_isPseudoArc {M : Set X} (hM : IsPseudoArc M) (p q : X) (hp : p ∈ M)
    (hq : q ∈ M) : ∃ T : M ≃ₜ M, T ⟨p, hp⟩ = ⟨q, hq⟩ := by
  obtain ⟨r, hr, hpr⟩ := exists_not_mem_composant hM hp
  obtain ⟨s, hs, hqs⟩ := exists_not_mem_composant hM hq
  obtain ⟨T, hT, -⟩ := theorem1_HIC hM hM hp hr hpr hq hs hqs
  exact ⟨T, hT⟩

-- Commented-out statement `isPseudoArc_of_description` (skeleton form) removed in batch 103; see `LEDGER.md`.

/-- **The continuum of a description is a pseudo-arc** (reshaped: the links lie in a compact
set; this covers the plane continuum of `Plane.pseudoArc_exists`). -/
theorem isPseudoArc_of_description {P Q : X} (Δ : Description X P Q) (hPQ : P ≠ Q)
    (K : Set X) (hK : ∀ i t, (Δ.D i).link t ⊆ K) (hKc : IsCompact K) : IsPseudoArc Δ.M := by
  refine ⟨⟨Δ.isContinuum_M_of K hK hKc, fun ε hε => ?_⟩, fun L hL hLc => Description.theorem10 Δ L
    hL hLc, ⟨P, Δ.P_mem_M, Q, Δ.Q_mem_M, hPQ⟩⟩
  obtain ⟨i, hi⟩ := (Δ.ε_tendsto.eventually (gt_mem_nhds hε)).exists
  exact ⟨Δ.n i, Δ.D i, fun t => ⟨Δ.bdd i t, (Δ.diam_le i t).trans_lt hi⟩, Δ.M_subset_union i⟩

/-- **A pseudo-arc in the plane**: the continuum of `Plane.exists_description_plane`. -/
theorem isPseudoArc_plane : ∃ M₀ : Set Pt, IsPseudoArc M₀ := by
  obtain ⟨P, Q, hPQ, ⟨Δ⟩⟩ := exists_description_plane
  obtain ⟨hKc, hK⟩ := Description.links_subset_compact Δ
  exact ⟨Δ.M, isPseudoArc_of_description Δ hPQ _ hK hKc⟩

end HPC.Plane
