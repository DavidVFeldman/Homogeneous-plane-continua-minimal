import HPC.Moore.M25BDefs
import HPC.Plane.JanPoly

/-!
# Batch 146: refutations in the decomposition of the plane into its points

The decomposition `ptSetoid` of `S` into its points satisfies Moore's standing hypothesis
(`mooreDecomp_ptSetoid`), and `Quotient.mk` is a homeomorphism `ptHomeo : Pt ≃ₜ Quotient ptSetoid`.
Statements about sets of elements are therefore statements about plane sets, and the printed forms
of Theorems 2, 7, 10, 11 (and Mullikin's Theorem 5) are refuted by explicit plane examples.
-/

namespace HPC.Moore

open Set Topology Metric HPC.Plane

/-- The decomposition of the plane into its points. -/
def ptSetoid : Setoid Pt := ⟨(· = ·), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

theorem elt_ptSetoid (x : Pt) : elt ptSetoid x = {x} := by
  ext y; rfl

theorem isConnected_compl_singleton_pt (x : Pt) : IsConnected ({x}ᶜ : Set Pt) := by
  have := isConnected_diff_singleton_of_isOpen isOpen_univ isConnected_univ x
  rwa [← compl_eq_univ_diff] at this

/-- The decomposition into points satisfies the standing hypothesis of §I. -/
theorem mooreDecomp_ptSetoid : MooreDecomp ptSetoid where
  compact x := by rw [elt_ptSetoid]; exact isCompact_singleton
  connected x := by rw [elt_ptSetoid]; exact isConnected_singleton
  nonsep x := by rw [elt_ptSetoid, SeparatesPlane, not_not]; exact isConnected_compl_singleton_pt x
  usc x e he := ⟨e, he, fun y ⟨p, hp, hpd⟩ q hq => by
    rw [elt_ptSetoid, mem_singleton_iff] at hp hq
    rw [hq, ← hp]; exact hpd⟩

/-- For the decomposition into points, `Quotient.mk` is a homeomorphism. -/
def ptHomeo : Pt ≃ₜ Quotient ptSetoid where
  toFun := Quotient.mk ptSetoid
  invFun := Quotient.lift id (fun _ _ h => h)
  left_inv _ := rfl
  right_inv q := by induction q using Quotient.inductionOn; rfl
  continuous_toFun := continuous_quotient_mk'
  continuous_invFun := continuous_quot_lift _ continuous_id

/-! ## Plane facts -/

theorem not_isPreconnected_of_split {X : Type*} [TopologicalSpace X] {s u v : Set X}
    (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hs : s ⊆ u ∪ v) {a b : X} (ha : a ∈ s)
    (hau : a ∈ u) (hb : b ∈ s) (hbv : b ∈ v) : ¬ IsPreconnected s := fun h => by
  rcases h.subset_or_subset hu hv huv hs with h | h
  · exact disjoint_left.1 huv (h hb) hbv
  · exact disjoint_left.1 huv hau (h ha)

theorem false_of_split {X : Type*} [TopologicalSpace X] {C U V : Set X} (hC : IsPreconnected C)
    (hU : IsOpen U) (hV : IsOpen V) (hUn : U.Nonempty) (hVn : V.Nonempty) (hUV : Disjoint U V)
    (h : U ∪ V = C) : False := by
  obtain ⟨u, hu⟩ := hUn
  obtain ⟨v, hv⟩ := hVn
  exact not_isPreconnected_of_split hU hV hUV h.ge (h ▸ Or.inl hu) hu (h ▸ Or.inr hv) hv hC

end HPC.Moore
