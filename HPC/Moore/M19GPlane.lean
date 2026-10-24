import HPC.Moore.M19GCollar
import HPC.Moore.M19F

/-!
# Moore 1919: a space satisfying Axioms 1–8 is a number plane (batch 144, item C)

Theorem F gives closed curves `Jₙ` with `Jₙ ∪ Iₙ ⊆ Iₙ₊₁` and `⋃ Iₙ = S`. The disc `J₀ ∪ I₀` is a
square (`exists_square_of_interior`), each annulus `Jₙ₊₁ ∪ Iₙ₊₁ − Iₙ` is a collar of `Jₙ`
(`exists_collar`), and the radial extensions are pasted (`HPC.Sq.plane_of_collars`).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section Plane

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

/-- **A space satisfying Axioms 1–8 is homeomorphic to `ℝ²`**, by a homeomorphism sending the
squares `[-(n+1), n+1]²` onto the discs `Jₙ ∪ Iₙ` of an exhaustion as in Theorem F.
*Axioms used: 1–8.* -/
theorem m19_plane_exhaust :
    ∃ (Jn In : ℕ → Set S) (e : @Homeomorph (ℝ × ℝ) S _ σ.topology),
      (∀ n, σ.IsInteriorOf (Jn n) (In n)) ∧ (∀ P, ∃ n, P ∈ In n) ∧
      (∀ n, Jn n ∪ In n ⊆ In (n + 1)) ∧
      ∀ n : ℕ, e '' HPC.Sq.Bsq ((n : ℝ) + 1) = Jn n ∪ In n := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  obtain ⟨Jn, In, hI, hcov, hsub⟩ := m19_theoremF_proof h1 h3 h2 h4 h5 h6 h7 h8
  have J := fun n => jordan h1 h2 h3 h4 h51 h7 (hI n)
  obtain ⟨f, hf, hfr, hbd⟩ := exists_square_of_interior h1 h2 h3 h4 h5 h6 h7 h8 (hI 0)
  obtain ⟨e, Ψ, hΨ, he⟩ := HPC.Sq.plane_of_collars Jn In (fun n => (J n).2.2.2.2.2.2.2.2.2.1.symm)
    hsub (fun n => (J n).1) hcov (HPC.Sq.stage_of_square f hf hfr hbd)
    (fun n => exists_collar h1 h2 h3 h4 h5 h6 h7 h8 (hI n) (hI (n + 1)) (hsub n))
  refine ⟨Jn, In, e, hI, hcov, hsub, fun n => ?_⟩
  rw [← (hΨ n).2.2.1]
  exact image_congr (he n)

/-- **Main theorem** (Moore 1919). A space satisfying Axioms 1–8 of F.A. is homeomorphic, in the
region topology, to `ℝ²`. *Axioms used: 1–8.* -/
theorem m19_plane_proof : Nonempty (@Homeomorph S (ℝ × ℝ) σ.topology _) := by
  obtain ⟨-, -, e, -⟩ := m19_plane_exhaust h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨@Homeomorph.symm _ _ _ σ.topology e⟩

end Plane

end HPC.Moore

namespace HPC.Moore

open Set Topology Gen Metric

variable {S : Type*} {σ : Space S}

section AnnulusSquare

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

end AnnulusSquare

end HPC.Moore
