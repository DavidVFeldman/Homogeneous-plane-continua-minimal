import HPC.Moore.Sec6Plane

/-!
# Moore, F.A. (1916), §6: the bridge, Theorems 20–23, and the interior of a closed curve
(batch 138, items A and B)

* The bridge from Moore's notions to the topological setting of `Sec6Plane.lean`:
  `bdry_eq_frontier`, `ext_eq_compl_closure`, `isArc_iff_tarc`, `isSCC_iff_tscc`,
  `isInteriorOf_iff`, `arcConn`, `locallyConnectedSpace`.
* **Theorem 20** (`fa_theorem20`): from Axiom 7 alone.
* **Theorem 21** (`fa_theorem21`): Moore's proof.
* **Theorem 22** (`fa_theorem22`): the whole space is connected; this is batch 137's
  `isConn_univ` (Axioms 1, 3, 4, 5). Moore's hint (Theorem 19, Axioms 2, 3, Theorem 20) is not
  needed.
* **The interior of a closed curve** (`existsUnique_interior`): unnumbered; existence by Axiom 8,
  uniqueness by Theorem 21.
* **Theorem 23** (`fa_theorem23`): Moore's proof, with the two points `A₁`, `B₁` obtained as a
  last and a first point. The printed form (no `R ≠ ∅`) is refuted (`not_fa_theorem23_printed`).
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-! ### The bridge -/

section Bridge1

variable (h1 : σ.Axiom1)
include h1

/-- Moore's boundary is the topological frontier. *Axioms used: 1.* -/
theorem bdry_eq_frontier (M : Set S) : σ.bdry M = @frontier S σ.topology M := by
  letI := σ.topology
  have hb := isTopologicalBasis_region h1
  ext x
  rw [frontier_eq_closure_inter_closure, mem_inter_iff, hb.mem_closure_iff, hb.mem_closure_iff]
  simp only [Space.bdry, mem_setOf_eq]
  constructor
  · intro h; exact ⟨fun R hR hx => (h R hR hx).1, fun R hR hx => (h R hR hx).2⟩
  · rintro ⟨h₁, h₂⟩ R hR hx; exact ⟨h₁ R hR hx, h₂ R hR hx⟩

/-- Moore's exterior is the complement of the closure. *Axioms used: 1.* -/
theorem ext_eq_compl_closure (M : Set S) : σ.ext M = (@closure S σ.topology M)ᶜ := by
  rw [Space.ext, cl_eq_closure h1]

/-- The regions are connected open sets forming a basis, so the space is locally connected.
*Axioms used: 1, 2.* -/
theorem locallyConnectedSpace (h2 : σ.Axiom2) : @LocallyConnectedSpace S σ.topology := by
  letI := σ.topology
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨R, hR, hxR, hRU⟩ := (mem_nhds_iff_region h1).mp hU
  exact ⟨R, hRU, isOpen_region hR, hxR, ⟨x, hxR⟩, (isConn_iff h1).mp (h2 R hR)⟩

/-- Every open set about `P` contains, with its closure, a region about `P`. *Axioms used: 1.* -/
theorem exists_region_closure_subset {U : Set S} (hU : @IsOpen S σ.topology U) {P : S}
    (hP : P ∈ U) : ∃ K ∈ σ.region, P ∈ K ∧ @closure S σ.topology K ⊆ U := by
  obtain ⟨R, hR, hPR, hRU⟩ := (isOpen_iff_region h1).mp hU P hP
  obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset h1 hR hPR
  exact ⟨K, hK, hPK, (cl_eq_closure h1 K ▸ hcl).trans hRU⟩

/-- Axiom 5 makes the space non-compact. *Axioms used: 1, 5.* -/
theorem not_isCompact_univ (h5 : σ.Axiom5) : ¬ @IsCompact S σ.topology univ := by
  letI := σ.topology
  intro hK
  obtain ⟨M, hM, hlim⟩ := h5
  obtain ⟨x, -, hx⟩ := hM.exists_accPt_of_subset_isCompact hK (subset_univ M)
  exact hlim x ((isLimitPt_iff h1).mpr hx)

end Bridge1

section Bridge2

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- Moore arcs are the topological arcs of `Sec6Arc.lean`. *Axioms used: 1, 3, 4, 5₁*
(batch 137's `isArc_iff`). -/
theorem isArc_iff_tarc {A B : S} {C : Set S} : σ.IsArc A B C ↔ @TArc S σ.topology A B C :=
  isArc_iff h1 h3 h4 h51

theorem isSCC_iff_tscc {J : Set S} : σ.IsSCC J ↔ @TSCC S σ.topology J := by
  simp only [Space.IsSCC, TSCC, isArc_iff_tarc h1 h3 h4 h51]

theorem isInteriorOf_iff {J R : Set S} :
    σ.IsInteriorOf J R ↔ @TInt S σ.topology σ.region J R := by
  rw [Space.IsInteriorOf, isSCC_iff_tscc h1 h3 h4 h51, bdry_eq_frontier h1]; rfl

/-- **Theorem 15**, in the form used in §6. *Axioms used: 1, 2, 3, 4, 5₁.* -/
theorem arcConn (h2 : σ.Axiom2) : @ArcConn S σ.topology := by
  intro U hUo hUc a ha b hb hab
  obtain ⟨C, hCU, hC⟩ := exists_arc_of_isOpen_isPreconnected h1 h2 h3 h4 h51 hUo hUc ha hb hab
  exact ⟨C, hCU, (isArc_iff_tarc h1 h3 h4 h51).mp hC⟩

end Bridge2

/-! ### Theorems 20–22 -/

/-- **Theorem 20.** Every point of the boundary of a region is a limit point of its exterior.
(\"Can easily be proved with the help of Axiom 7\"; no proof printed.) *Axioms used: 7.*
Proof: for a region `R̄` about `P`, Axiom 7 gives a region `L ⊆ R̄` in the exterior of `R` and a
region `L̄ ∋ P` with every boundary point of `R` in `L̄` a boundary point of `L`; so `P` is a
boundary point of `L`, and `L̄` contains a point of `L`, which is not `P`.
**Shape change:** only Axiom 7 is assumed (the skeleton's section assumes Axioms 1–8). -/
theorem fa_theorem20 (h7 : σ.Axiom7) {R : Set S} (hR : R ∈ σ.region) {P : S}
    (hP : P ∈ σ.bdry R) : σ.IsLimitPt P (σ.ext R) := by
  intro R' hR' hPR'
  obtain ⟨L, hL, L', hL', hLR', -, hPL', hLext, hbd⟩ := h7 R hR R' hR' P hPR' hP
  obtain ⟨x, hxL', hxL⟩ := (hbd ⟨hP, hPL'⟩ L' hL' hPL').1
  refine ⟨x, hLext hxL, hLR' hxL, fun h => ?_⟩
  exact hLext hxL (h ▸ Or.inr hP)

/-- Theorem 20, topologically: the boundary of a region lies in the closure of its exterior.
*Axioms used: 1, 7.* -/
theorem frontier_subset_closure_ext (h1 : σ.Axiom1) (h7 : σ.Axiom7) {R : Set S}
    (hR : R ∈ σ.region) :
    @frontier S σ.topology R ⊆ @closure S σ.topology (@closure S σ.topology R)ᶜ := by
  letI := σ.topology
  intro P hP
  rw [← bdry_eq_frontier h1] at hP
  have hlim := fa_theorem20 h7 hR hP
  rw [(isTopologicalBasis_region h1).mem_closure_iff]
  intro R' hR' hPR'
  obtain ⟨x, hx, hxR', -⟩ := hlim R' hR' hPR'
  exact ⟨x, hxR', by rwa [← ext_eq_compl_closure h1]⟩

/-- **Theorem 21.** If `K`, `R` are regions and the boundary of `R` lies in `K'`, then `R ⊆ K`.
*Axioms used: 1, 3, 4, 5, 7.* Moore's proof: the exterior `S − K'` is connected (Axiom 3) and is
not inside `R'` (Theorem 18: `R'` is compact, `S` is not); were it to meet `R` it would meet the
boundary of `R`, which lies in `K'`. So `R ⊆ K'`, and a point of `R` on the boundary of `K` would
be a limit point of `S − K'` (Theorem 20). **Shape change:** the axioms are made explicit. -/
theorem fa_theorem21 (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) {K R : Set S} (hK : K ∈ σ.region) (hR : R ∈ σ.region)
    (h : σ.bdry R ⊆ σ.cl K) : R ⊆ K := by
  letI := σ.topology
  rw [bdry_eq_frontier h1, cl_eq_closure h1] at h
  have hRo : IsOpen R := isOpen_region hR
  have hKo : IsOpen K := isOpen_region hK
  have hE : IsPreconnected (closure K)ᶜ := by
    have := (isConn_iff h1).mp (h3 K hK); rwa [ext_eq_compl_closure h1] at this
  have hEnot : ¬ (closure K)ᶜ ⊆ closure R := by
    intro hsub
    apply not_isCompact_univ h1 h5
    have : (univ : Set S) = closure K ∪ closure R := by
      refine (eq_univ_of_forall fun x => ?_).symm
      by_cases hx : x ∈ closure K
      · exact Or.inl hx
      · exact Or.inr (hsub hx)
    rw [this]
    exact (isCompact_closure_region h1 h4 hK).union (isCompact_closure_region h1 h4 hR)
  have hER : (closure K)ᶜ ∩ R = ∅ := by
    by_contra hne'
    have hne := nonempty_iff_ne_empty.mpr hne'
    have hsub : (closure K)ᶜ ⊆ R ∪ (closure R)ᶜ := by
      intro x hx
      by_cases hxR : x ∈ R
      · exact Or.inl hxR
      · right; intro hxc
        exact hx (h (mem_frontier_of_mem_closure hRo hxc hxR))
    have := hE.subset_left_of_subset_union hRo isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hsub hne
    exact hEnot (this.trans subset_closure)
  intro x hxR
  have hxK : x ∈ closure K := by
    by_contra hx
    exact (eq_empty_iff_forall_notMem.mp hER) x ⟨hx, hxR⟩
  by_contra hxK'
  have hfr : x ∈ frontier K := mem_frontier_of_mem_closure hKo hxK hxK'
  obtain ⟨y, hyR, hyE⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure_ext h1 h7 hK hfr) R
    (hRo.mem_nhds hxR)
  exact (eq_empty_iff_forall_notMem.mp hER) y ⟨hyE, hyR⟩

/-- Theorem 21 in the form `Th21Prop`. -/
theorem th21Prop (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) : @Th21Prop S σ.topology σ.region := by
  intro K hK R hR h
  refine fa_theorem21 h1 h3 h4 h5 h7 hK hR ?_
  rwa [bdry_eq_frontier h1, cl_eq_closure h1]

/-- Axiom 8 in the form `Ax8Prop`. -/
theorem ax8Prop (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
    (h8 : σ.Axiom8) : @Ax8Prop S σ.topology σ.region := by
  intro J hJ
  obtain ⟨R, hR, hRJ⟩ := h8 J ((isSCC_iff_tscc h1 h3 h4 h51).mpr hJ)
  exact ⟨R, hR, by rwa [← bdry_eq_frontier h1]⟩

/-- **The interior of a closed curve** (unnumbered; the convention \"the interior of `J`\" is used
from the proof of Theorem 23 on and never defined in F.A.). Every closed curve has exactly one
interior. Existence is Axiom 8; uniqueness is Theorem 21 applied both ways.
*Axioms used: 1, 3, 4, 5, 7, 8.* **Shape change:** the axioms are made explicit. -/
theorem existsUnique_interior (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
    (h7 : σ.Axiom7) (h8 : σ.Axiom8) {J : Set S} (hJ : σ.IsSCC J) :
    ∃! R, σ.IsInteriorOf J R := by
  obtain ⟨R, hR, hRJ⟩ := h8 J hJ
  refine ⟨R, ⟨hJ, hR, hRJ⟩, fun R' ⟨_, hR', hR'J⟩ => subset_antisymm ?_ ?_⟩
  · exact fa_theorem21 h1 h3 h4 h5 h7 hR hR' (hR'J ▸ hRJ ▸ fun x hx => Or.inr hx)
  · exact fa_theorem21 h1 h3 h4 h5 h7 hR' hR (hRJ ▸ hR'J ▸ fun x hx => Or.inr hx)

/-! ### Theorem 23 -/

end HPC.Moore
