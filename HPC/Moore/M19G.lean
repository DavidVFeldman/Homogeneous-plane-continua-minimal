import HPC.Moore.M19F
import HPC.Moore.M19ESchoenflies
import HPC.Moore.M19GPlane

/-!
# Batch 144 skeleton: Moore 1919, the end of the paper. A Σ-space is a number plane.

Save as `HPC/Moore/M19G.lean` (splitting under `HPC/Moore/` is expected); add `import HPC.Moore.M19G`
at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be adjusted, each change recorded
at the statement and in the report.

Route: the Schoenflies route recommended in REPORT-batch143 (accepted). Moore's Theorem G and his
final paragraph are derived as corollaries of the main theorem `m19_plane`.

**Batch 144.** All `sorry`s are replaced by proofs. One shape change: `m19_annulus` (whose shape was
left open, `True` in the skeleton) is stated in collar form; its square form is `m19_annulus_square`
(added). `m19_openCurve` (added) is the second half of the Theorem G item: an image of a closed
embedding of `ℝ` is an open curve in F.A.'s sense.
-/

namespace HPC.Moore

open Set Topology Filter

variable {S : Type*} {σ : Space S}

section M19G

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Main theorem** (Moore 1919: "every space `S` that satisfies Σ₁ or Σ₂ is a number plane"). A
space satisfying Axioms 1–8 of F.A. is homeomorphic, in the region topology, to `ℝ²`. -/
theorem m19_plane : Nonempty (@Homeomorph S (ℝ × ℝ) σ.topology _) :=
  m19_plane_proof h1 h2 h3 h4 h5 h6 h7 h8

end M19G

end HPC.Moore
