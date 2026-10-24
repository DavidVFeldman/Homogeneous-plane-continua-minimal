import HPC.BJ59.Decomp
import HPC.BJ59.Thm56
import HPC.BJ59.Thm5

/-!
# Batch 198: Part G, I — the circle of pseudo-arcs (Bing–Jones 1959), top down

The skeleton of commission 198, §§4–6 (the definitions and named inputs of §§2–3 are in
`HPC/BJ59/Defs.lean`, verbatim). Library lemmas are in the other files of `HPC/BJ59/`.

Source: R. H. Bing and F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959),
171–192 (`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`).
Route: commission 198.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/-! ## §4. From Theorem 10: homogeneity and uniqueness of circles of pseudo-arcs -/

/-- **Each circle of pseudo-arcs is homogeneous** (Bing–Jones pp. 173, 189, "It follows from
Theorem 10"; the step is supplied by commission §4). -/
theorem isHomogeneous_of_isCircleOfPA (h10 : BJThm10) {X : Type} [MetricSpace X]
    (hX : IsCircleOfPA X) : IsHomogeneous X := by
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hX
  exact isHomogeneous_of_isCircPAMap h10 hf

/-- **Any two circles of pseudo-arcs are homeomorphic** (Bing–Jones pp. 173, 189). -/
theorem homeomorph_of_isCircleOfPA (h10 : BJThm10) {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (hX : IsCircleOfPA X) (hY : IsCircleOfPA Y) : Nonempty (X ≃ₜ Y) := by
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hX
  obtain ⟨g, hg⟩ := isCircleOfPA_iff.1 hY
  exact homeomorph_of_isCircPAMap h10 hf hg

/-! ## §5. The decomposable case and the classification -/

/-- The circle is homogeneous. -/
theorem isHomogeneous_circle : IsHomogeneous Circle := by
  exact isHomogeneous_circle'

/-- **The decomposable case**: a decomposable homogeneous plane continuum is a simple closed curve
or a circle of pseudo-arcs. -/
theorem circle_or_circleOfPA_of_decomposable (hCL : HOCircleLike) {M : Set Pt} [CompactSpace M]
    [ConnectedSpace M] (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ IsCircleOfPA M := by
  rcases circle_or_circPAMap_of_decomposable hX hd (hCL M ‹_› ‹_› hX hd) with h | h
  · exact Or.inl h
  · exact Or.inr (isCircleOfPA_iff.2 h)

/-- **The classification, both directions** (H–O p. 180, with Bing–Jones for the third class). -/
theorem ho16_classification (h10 : BJThm10) (hCL : HOCircleLike) (M : Set Pt) [CompactSpace M]
    [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  constructor
  · intro hX
    by_cases hd : IsDecomposableSpace M
    · rcases circle_or_circleOfPA_of_decomposable hCL hX hd with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ((ho16_indec_homogeneous_iff M hnt).1 ⟨hX, hd⟩))
  · rintro (he | h | h)
    · obtain ⟨e⟩ := he
      exact IsHomogeneous.of_homeomorph e.symm isHomogeneous_circle
    · exact (ho16_pseudoArc_indec_homogeneous M h).1
    · exact isHomogeneous_of_isCircleOfPA h10 h

/-- **The classification of homogeneous plane continua**: there are three plane continua, the
circle, the pseudo-arc and a circle of pseudo-arcs, each homogeneous, no two homeomorphic, and
every non-degenerate plane continuum is homogeneous iff it is homeomorphic to one of them. -/
theorem ho16_classification_plane (h10 : BJThm10) (hCL : HOCircleLike) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  obtain ⟨C₁, ⟨e₁⟩⟩ := exists_plane_circle
  obtain ⟨C₂, hC₂⟩ := isPseudoArc_plane
  obtain ⟨C₃, hC₃⟩ := hEx
  have hom₁ : IsHomogeneous C₁ := IsHomogeneous.of_homeomorph e₁.symm isHomogeneous_circle
  have hom₂ : IsHomogeneous C₂ := fun x y => by
    obtain ⟨T, hT⟩ := homogeneous_of_isPseudoArc hC₂ x y x.2 y.2
    exact ⟨T, hT⟩
  have hom₃ : IsHomogeneous C₃ := isHomogeneous_of_isCircleOfPA h10 hC₃
  obtain ⟨f, hf⟩ := isCircleOfPA_iff.1 hC₃
  have hd₁ : IsDecomposableSpace C₁ := IsDecomposableSpace.of_homeomorph e₁.symm
    isDecomposableSpace_circle
  have hd₂ : ¬ IsDecomposableSpace C₂ := not_isDecomposableSpace_of_isIndecomposable_univ
    (isIndecomposable_univ_of_isIndecomposable (hC₂.2.1 C₂ subset_rfl hC₂.1.1))
  have hd₃ : IsDecomposableSpace C₃ := isDecomposableSpace_of_isCircPAMap hf
  have h13 : IsEmpty (C₁ ≃ₜ C₃) := by
    refine ⟨fun Φ => ?_⟩
    set ψ : C₃ ≃ₜ Circle := Φ.symm.trans e₁
    set F : Set C₃ := f ⁻¹' {1}
    have hK : IsPseudoArc (ψ '' F) := isPseudoArc_of_homeomorph (hf.fib 1) (ψ.image F)
    refine not_isPseudoArc_of_ne_univ_circle (fun hu => ?_) hK
    obtain ⟨x, hx⟩ := hf.surj (Circle.exp Real.pi)
    obtain ⟨y, hy, hyx⟩ : ψ x ∈ ψ '' F := hu ▸ mem_univ _
    have : y = x := ψ.injective hyx
    subst this
    have h1 : f y = 1 := hy
    rw [hx] at h1
    exact circle_exp_pi_ne_one h1
  refine ⟨C₁, C₂, C₃, ⟨⟨e₁⟩, hC₂, hC₃⟩, ⟨hom₁, hom₂, hom₃⟩,
    ⟨⟨fun Φ => hd₂ (IsDecomposableSpace.of_homeomorph Φ hd₁)⟩, h13,
      ⟨fun Φ => hd₂ (IsDecomposableSpace.of_homeomorph Φ.symm hd₃)⟩⟩, ?_⟩
  intro M hMc hMk hMnt
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  haveI : ConnectedSpace M := isConnected_iff_connectedSpace.1 hMk
  have hnt : (univ : Set M).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hMnt
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩
  constructor
  · intro hX
    rcases (ho16_classification h10 hCL M hnt).1 hX with he | h | h
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨e.trans e₁.symm⟩
    · obtain ⟨e⟩ := theorem1_HIC' h hC₂
      exact Or.inr (Or.inl ⟨(Homeomorph.Set.univ M).symm.trans e⟩)
    · exact Or.inr (Or.inr (homeomorph_of_isCircleOfPA h10 h hC₃))
  · rintro (he | he | he) <;> obtain ⟨e⟩ := he
    · exact IsHomogeneous.of_homeomorph e.symm hom₁
    · exact IsHomogeneous.of_homeomorph e.symm hom₂
    · exact IsHomogeneous.of_homeomorph e.symm hom₃

/-! ## §6. Bing–Jones §§3–4: snake-like arcs of continua; chain maps -/

section Section3

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Bing–Jones, Theorem 4** (p. 175): a non-empty open set missing the end elements separates
them. -/
theorem bj_theorem4 {f : X → unitInterval} (hf : IsArcOfContinua f)
    (hS : IsSnakeLike (univ : Set X)) {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hU01 : Disjoint U (f ⁻¹' {0, 1})) :
    ∃ A B : Set X, IsClosed A ∧ IsClosed B ∧ Disjoint A B ∧ A ∪ B = Uᶜ ∧ f ⁻¹' {0} ⊆ A ∧
      f ⁻¹' {1} ⊆ B := by
  obtain ⟨p, hp⟩ := hUne
  have hε := posFn_pos hU hp
  obtain ⟨m, D, hD, hcov, h0, h1⟩ :=
    theorem3_arc hf.1 hf.2.1 (fun t => (hf.2.2 t).2.isPreconnected) hS hε
  obtain ⟨l, hl⟩ := mem_iUnion.1 (hcov (mem_univ p))
  have hlU : D.link l ⊆ U := by
    intro y hy
    by_contra hyU
    have hdist : dist p y < posFn U p :=
      lt_of_le_of_lt (dist_le_diam_of_mem (hD l).1 hl hy) (hD l).2
    have hpos : posFn U p = infDist p Uᶜ := by unfold posFn; rw [if_pos ⟨y, hyU⟩]
    rw [hpos] at hdist
    exact absurd (infDist_le_dist_of_mem (show y ∈ Uᶜ from hyU)) (not_le.2 hdist)
  exact theorem4_of_chain hU hU01 (hf.2.2 0).2.isPreconnected (hf.2.2 1).2.isPreconnected D hcov
    h0 h1 l hlU

end Section3

end HPC.BJ59
