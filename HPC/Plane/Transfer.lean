import HPC.PseudoArc.Theorem13

/-!
# Restricting a description to a compact set containing its links

Batch 84. Theorems 12 and 13 are stated for descriptions in a *compact* metric space. A description
in the plane whose links all lie in a compact set `K` restricts to a description in the subspace
`K`, describing the same continuum. This transfers `isContinuum_M` and `theorem13` to the plane.
-/

namespace HPC

open Set Metric

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n : ℕ}

omit [MetricSpace X] in
theorem preimage_inter_nonempty_iff {K : Set X} {A B : Set X} (hA : A ⊆ K) :
    ((Subtype.val : K → X) ⁻¹' A ∩ Subtype.val ⁻¹' B).Nonempty ↔ (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨z, h1, h2⟩; exact ⟨z.1, h1, h2⟩
  · rintro ⟨z, h1, h2⟩; exact ⟨⟨z, hA h1⟩, h1, h2⟩

/-- The restriction of a chain to a set containing its links. -/
def restrict (D : Chain X n) (K : Set X) (hK : ∀ j, D.link j ⊆ K) : Chain K n where
  link j := Subtype.val ⁻¹' D.link j
  isOpen j := (D.isOpen j).preimage continuous_subtype_val
  adjacent i j := by rw [preimage_inter_nonempty_iff (hK i), D.adjacent]

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q) (K : Set X) (hK : ∀ i t, (Δ.D i).link t ⊆ K)
include hK

theorem P_mem_of (i : ℕ) : P ∈ K := by
  obtain ⟨hn, hP, -⟩ := Δ.isFrom i
  exact hK i _ hP

theorem Q_mem_of (i : ℕ) : Q ∈ K := by
  obtain ⟨hn, -, hQ, -⟩ := Δ.isFrom i
  exact hK i _ hQ

/-- The restriction of a description to a set containing all its links. -/
noncomputable def restrict : Description K ⟨P, Δ.P_mem_of K hK 0⟩ ⟨Q, Δ.Q_mem_of K hK 0⟩ where
  n := Δ.n
  D i := (Δ.D i).restrict K (hK i)
  isFrom i := by
    obtain ⟨hn, hP, hQ, hP', hQ'⟩ := Δ.isFrom i
    exact ⟨hn, hP, hQ, fun j hj => hP' j hj, fun j hj => hQ' j hj⟩
  crooked i := by
    obtain ⟨href, hcr⟩ := Δ.crooked i
    refine ⟨fun t => ?_, fun h k hk a b ha hb => ?_⟩
    · obtain ⟨s, hs⟩ := href t
      exact ⟨s, preimage_mono hs⟩
    · have ha' := (Chain.preimage_inter_nonempty_iff (hK (i + 1) a)).mp ha
      have hb' := (Chain.preimage_inter_nonempty_iff (hK (i + 1) b)).mp hb
      obtain ⟨r, s, hb2, hr, hs⟩ := hcr h k hk a b ha' hb'
      exact ⟨r, s, hb2, preimage_mono hr, preimage_mono hs⟩
  closure_subset i t := by
    obtain ⟨s, hs⟩ := Δ.closure_subset i t
    exact ⟨s, (continuous_subtype_val.closure_preimage_subset _).trans (preimage_mono hs)⟩
  ε := Δ.ε
  ε_pos := Δ.ε_pos
  ε_tendsto := Δ.ε_tendsto
  bdd i t := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (Δ.bdd i t)
    exact Metric.isBounded_iff.mpr ⟨C, fun a ha b hb => hC ha hb⟩
  diam_le i t := by
    refine le_trans ?_ (Δ.diam_le i t)
    rw [← isometry_subtype_coe.diam_image]
    exact diam_mono (image_preimage_subset _ _) (Δ.bdd i t)

theorem restrict_M : (Δ.restrict K hK).M = Subtype.val ⁻¹' Δ.M := by
  ext z
  simp [Description.M, Chain.union, restrict, Chain.restrict]

theorem M_subset : Δ.M ⊆ K := by
  intro z hz
  simp only [Description.M, mem_iInter, Chain.union, mem_iUnion] at hz
  obtain ⟨t, ht⟩ := hz 0
  exact hK 0 t ht

theorem M_eq_image : Δ.M = Subtype.val '' (Δ.restrict K hK).M := by
  rw [restrict_M, Subtype.image_preimage_coe, inter_eq_right.mpr (Δ.M_subset K hK)]

/-- The described continuum is a continuum, if its links lie in a compact set. -/
theorem isContinuum_M_of (hKc : IsCompact K) : Fold.Q78.IsContinuum Δ.M := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  obtain ⟨h1, h2⟩ := (Δ.restrict K hK).isContinuum_M
  rw [Δ.M_eq_image K hK]
  exact ⟨h1.image continuous_subtype_val, h2.image _ continuous_subtype_val.continuousOn⟩

end Description

end HPC
