import HPC.Hagopian.H76Crosscut
import HPC.Hagopian.H75Composants
import HPC.Hagopian.H76T7

/-!
# Batch 167, item A: crossing translates (supporting file)

* `exists_mem_closure_component_notMem`: boundary bumping for components of an open subset of a
  continuum (the closure of the component through `p` leaves the open set).
* `isOpen_collar_image`: the collar maps open subsets of the open rectangle onto open sets.
* `collar_uniform`: points of the plane near `F(t, 0)`, `t ∈ [a', b'] ⊆ (0, 1)`, are `F`-images of
  points of the open rectangle near `(t, 0)`, uniformly in `t`.
* `pi_near_collar`: the same for `π`-images of points of `M` near the layers over `[a', b']`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- The collar is injective on the closed rectangle. -/
theorem collar_injOn {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) {z w : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
    (h : F z = F w) : z = w := by
  have := hF.1.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h
  exact congrArg Subtype.val this

theorem openRect_subset_rect :
    Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

/-- **The collar maps open subsets of the open rectangle onto open sets.** -/
theorem isOpen_collar_image {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVR : V ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :
    IsOpen (F '' V) := by
  obtain ⟨hFemb, -, hFo⟩ := hF
  set R := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1
  have hU : IsOpen ((Subtype.val : R → ℝ × ℝ) ⁻¹' V) := hV.preimage continuous_subtype_val
  obtain ⟨W, hW, hWU⟩ := hFemb.isInducing.isOpen_iff.1 hU
  have : F '' V = W ∩ F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z, hVR hz, rfl⟩
      have : (⟨z, openRect_subset_rect (hVR hz)⟩ : R) ∈ (R.restrict F) ⁻¹' W := by
        rw [hWU]; exact hz
      exact this
    · rintro ⟨hpW, z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      have : (⟨z, openRect_subset_rect hz⟩ : R) ∈ (R.restrict F) ⁻¹' W := hpW
      rw [hWU] at this
      exact this
  rw [this]
  exact hW.inter hFo

end HPC.Hagopian
