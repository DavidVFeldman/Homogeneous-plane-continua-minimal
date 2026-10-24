import HPC.Moore.Thm15

/-!
# Moore, F.A. (1916), §5: arcs (batch 137, item E)

F.A. §5 (p. 139) says only that "it is possible to prove Theorems 2–9 of §4 of Lennes' paper".
These are replaced by the arc characterization (`isIrreducibleConnected_iff_arc`,
`HPC/Moore/ArcChar.lean`): `isArc_iff` identifies Moore arcs with embedded `[0, 1]`'s, and the
unnumbered facts of pp. 139–140 follow, each as its own lemma:

| p. 139–140 | here |
|---|---|
| splitting an arc at a point | `fa_sec5_arc_split` |
| the unique interval `XY` | `fa_sec5_interval_unique` |
| first and last points on a closed set | `fa_sec5_first_point`, `fa_sec5_last_point` |
| limit points along an arc | `fa_sec5_limitPt_iff`; the printed form fails: `not_fa_sec5_limitPt_printed` |
| the two arcs of a simple closed curve | `fa_scc_two_arcs` |

*Axioms used:* `isArc_iff` and everything that depends on it: 1, 3, 4, 5₁ (metrizability and the
compactness of bounded closed sets). `Space.IsArc.union`, `isArc_image_Icc`: 1, 4.

**Shape changes** (recorded at each statement): the skeleton's section hypotheses (Axioms 1–5)
are reduced to Axioms 1, 3, 4, 5₁; "between `P₁` and `B`" in the first-point statement is read
as "on the interval `P₁B`" (with `B ∈ K` the literal reading fails: `B` is not between `P₁` and
`B`); the limit-point statement admits intervals having `P` as an endpoint when `P` is `A` or `B`.
-/

namespace HPC.Moore

open Set Topology

variable {S : Type*} {σ : Space S}

theorem Space.IsArc.symm {A B : S} {C : Set S} (h : σ.IsArc A B C) : σ.IsArc B A C := by
  obtain ⟨hAB, hb, hc, hconn, hA, hB, hirr⟩ := h
  exact ⟨hAB.symm, hb, hc, hconn, hB, hA, fun H hHC hne hBH hAH => hirr H hHC hne hAH hBH⟩

theorem Space.IsArc.left_mem {A B : S} {C : Set S} (h : σ.IsArc A B C) : A ∈ C := h.2.2.2.2.1

theorem Space.IsArc.right_mem {A B : S} {C : Set S} (h : σ.IsArc A B C) : B ∈ C := h.2.2.2.2.2.1

section Topo

variable {X : Type*} [TopologicalSpace X]

/-- If a preconnected `H` lies in the union of closed sets `D`, `E` meeting in at most `Q`, and
`H` has a point outside `D`, then `H ∩ D` is preconnected. -/
theorem isPreconnected_inter_of_isClosed {H D E : Set X} (hH : IsPreconnected H)
    (hD : IsClosed D) (hE : IsClosed E) (hHDE : H ⊆ D ∪ E) {Q R : X} (hDE : D ∩ E ⊆ {Q})
    (hR : R ∈ H) (hRD : R ∉ D) : IsPreconnected (H ∩ D) := by
  have hRE : R ∈ E := (hHDE hR).resolve_left hRD
  have key : ∀ t t' : Set X, IsClosed t → IsClosed t' → H ∩ D ⊆ t ∪ t' →
      (H ∩ D ∩ t').Nonempty → H ∩ D ∩ (t ∩ t') = ∅ → (Q ∈ H ∩ D → Q ∈ t' → False) → False := by
    intro t t' ht ht' hsub hne' hemp hQ
    have hcov : H ⊆ ((t ∩ D) ∪ E) ∪ (t' ∩ D) := fun h hh => by
      rcases hHDE hh with hd | he
      · rcases hsub ⟨hh, hd⟩ with h1 | h2
        · exact Or.inl (Or.inl ⟨h1, hd⟩)
        · exact Or.inr ⟨h2, hd⟩
      · exact Or.inl (Or.inr he)
    obtain ⟨x, ⟨hxH, hxD⟩, hxt'⟩ := hne'
    obtain ⟨h, hh, h1, h2⟩ := (isPreconnected_closed_iff.mp hH) _ _ ((ht.inter hD).union hE)
      (ht'.inter hD) hcov ⟨R, hR, Or.inr hRE⟩ ⟨x, hxH, hxt', hxD⟩
    rcases h1 with ⟨hT, hD'⟩ | hE'
    · have : h ∈ H ∩ D ∩ (t ∩ t') := ⟨⟨hh, hD'⟩, hT, h2.1⟩
      rw [hemp] at this; exact this
    · have hq : h = Q := hDE ⟨h2.2, hE'⟩
      subst hq; exact hQ ⟨hh, h2.2⟩ h2.1
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hsub hne hne'
  by_contra hemp
  rw [not_nonempty_iff_eq_empty] at hemp
  by_cases hQ : Q ∈ t'
  · refine key t' t ht' ht (by rwa [union_comm]) hne (by rwa [inter_comm t']) fun hs hQt => ?_
    have : Q ∈ H ∩ D ∩ (t ∩ t') := ⟨hs, hQt, hQ⟩
    rw [hemp] at this; exact this
  · exact key t t' ht ht' hsub hne' hemp fun _ h => hQ h

theorem unitInterval_Icc_zero_one : Icc (0 : unitInterval) 1 = univ :=
  eq_univ_of_forall fun t => ⟨t.2.1, t.2.2⟩

end Topo

section A14

variable (h1 : σ.Axiom1) (h4 : σ.Axiom4)
include h1 h4

/-- The image of a nondegenerate interval under an embedding of `[0, 1]` is a Moore arc. -/
theorem isArc_image_Icc {f : unitInterval → S} (hf : @IsEmbedding _ _ _ σ.topology f)
    {s t : unitInterval} (hst : s < t) : σ.IsArc (f s) (f t) (f '' Icc s t) := by
  letI := σ.topology
  rw [isArc_iff_topological h1 h4]
  refine ⟨fun h => hst.ne (hf.injective h), isCompact_Icc.image hf.continuous,
    (isConnected_Icc hst.le).image _ hf.continuous.continuousOn,
    mem_image_of_mem _ (left_mem_Icc.mpr hst.le), mem_image_of_mem _ (right_mem_Icc.mpr hst.le),
    ?_⟩
  intro H hHC hne hsH htH hH
  apply hne
  refine subset_antisymm hHC ?_
  have hpre : IsPreconnected (f ⁻¹' H) := by
    rw [← hf.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset (hHC.trans (image_subset_range _ _))]
    exact hH.isPreconnected
  rintro _ ⟨u, hu, rfl⟩
  exact hpre.Icc_subset hsH htH hu

/-- **Gluing.** Two arcs `PQ`, `QR` meeting only in `Q` form an arc `PR`. -/
theorem Space.IsArc.union {P Q R : S} {D E : Set S} (hD : σ.IsArc P Q D) (hE : σ.IsArc Q R E)
    (hDE : D ∩ E = {Q}) : σ.IsArc P R (D ∪ E) := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨hPQ, hDc, hDconn, hPD, hQD, hDirr⟩ := (isArc_iff_topological h1 h4).mp hD
  obtain ⟨hQR, hEc, hEconn, hQE, hRE, hEirr⟩ := (isArc_iff_topological h1 h4).mp hE
  have hRD : R ∉ D := fun h => hQR (by
    have : R ∈ D ∩ E := ⟨h, hRE⟩
    rw [hDE] at this; exact this.symm)
  have hPE : P ∉ E := fun h => hPQ (by
    have : P ∈ D ∩ E := ⟨hPD, h⟩
    rw [hDE] at this; exact this)
  rw [isArc_iff_topological h1 h4]
  refine ⟨fun h => hRD (h ▸ hPD), hDc.union hEc, hDconn.union ⟨Q, hQD, hQE⟩ hEconn, Or.inl hPD,
    Or.inr hRE, ?_⟩
  intro H hHC hne hPH hRH hH
  apply hne
  have hQH : Q ∈ H := by
    obtain ⟨x, hxH, hxD, hxE⟩ := isPreconnected_closed_iff.mp hH.isPreconnected D E
      hDc.isClosed hEc.isClosed hHC ⟨P, hPH, hPD⟩ ⟨R, hRH, hRE⟩
    have : x ∈ D ∩ E := ⟨hxD, hxE⟩
    rw [hDE] at this
    exact (mem_singleton_iff.mp this) ▸ hxH
  have hHD : H ∩ D = D := by
    by_contra hne'
    exact hDirr (H ∩ D) inter_subset_right hne' ⟨hPH, hPD⟩ ⟨hQH, hQD⟩
      ⟨⟨P, hPH, hPD⟩, isPreconnected_inter_of_isClosed hH.isPreconnected hDc.isClosed
        hEc.isClosed hHC hDE.subset hRH hRD⟩
  have hHE : H ∩ E = E := by
    by_contra hne'
    exact hEirr (H ∩ E) inter_subset_right hne' ⟨hQH, hQE⟩ ⟨hRH, hRE⟩
      ⟨⟨R, hRH, hRE⟩, isPreconnected_inter_of_isClosed hH.isPreconnected hEc.isClosed
        hDc.isClosed (by rwa [union_comm]) (by rw [inter_comm]; exact hDE.subset) hPH hPE⟩
  refine subset_antisymm hHC ?_
  rintro x (hx | hx)
  · rw [← hHD] at hx; exact hx.1
  · rw [← hHE] at hx; exact hx.1

end A14

section A1345

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

/-- **Moore arcs are arcs** (Lennes's definition = embedded `[0, 1]`). *Axioms used: 1, 3, 4, 5₁.*
**Shape change:** the skeleton's Axioms 1–5 are reduced to 1, 3, 4, 5₁ (5₁ follows from 5). -/
theorem isArc_iff {A B : S} {C : Set S} :
    σ.IsArc A B C ↔ A ≠ B ∧ ∃ f : unitInterval → S,
      @IsEmbedding _ _ _ σ.topology f ∧ range f = C ∧ f 0 = A ∧ f 1 = B := by
  letI := σ.topology
  haveI := metrizable h1 h3 h51
  rw [isArc_iff_topological h1 h4]
  constructor
  · rintro ⟨hAB, h⟩; exact ⟨hAB, (isIrreducibleConnected_iff_arc hAB).mp h⟩
  · rintro ⟨hAB, h⟩; exact ⟨hAB, (isIrreducibleConnected_iff_arc hAB).mpr h⟩

/-- p. 139 (unnumbered): a point `X` of the arc `AB` other than an endpoint splits it into arcs
`AX`, `XB` meeting only in `X`. -/
theorem fa_sec5_arc_split {A B X : S} {C : Set S} (hC : σ.IsArc A B C) (hX : X ∈ C)
    (hXA : X ≠ A) (hXB : X ≠ B) :
    ∃ C₁ C₂, σ.IsArc A X C₁ ∧ σ.IsArc X B C₂ ∧ C₁ ∪ C₂ = C ∧ C₁ ∩ C₂ = {X} := by
  letI := σ.topology
  obtain ⟨-, f, hf, hrange, hf0, hf1⟩ := (isArc_iff h1 h3 h4 h51).mp hC
  obtain ⟨x, rfl⟩ : X ∈ range f := hrange ▸ hX
  have h0x : 0 < x := lt_of_le_of_ne x.2.1 fun h => hXA (by rw [← hf0, ← h])
  have hx1 : x < 1 := lt_of_le_of_ne x.2.2 fun h => hXB (by rw [← hf1, h])
  refine ⟨f '' Icc 0 x, f '' Icc x 1, ?_, ?_, ?_, ?_⟩
  · have := isArc_image_Icc h1 h4 hf h0x; rwa [hf0] at this
  · have := isArc_image_Icc h1 h4 hf hx1; rwa [hf1] at this
  · rw [← image_union, Icc_union_Icc_eq_Icc h0x.le hx1.le, unitInterval_Icc_zero_one, image_univ,
      hrange]
  · rw [← image_inter hf.injective, Icc_inter_Icc_eq_singleton h0x.le hx1.le, image_singleton]

/-- An arc minus its endpoints is connected and nonempty. -/
theorem isPreconnected_diff_endpoints {A B : S} {C : Set S} (hC : σ.IsArc A B C) :
    @IsPreconnected S σ.topology (C \ {A, B}) ∧ (C \ {A, B}).Nonempty := by
  letI := σ.topology
  obtain ⟨-, f, hf, hrange, hf0, hf1⟩ := (isArc_iff h1 h3 h4 h51).mp hC
  have heq : C \ {A, B} = f '' Ioo 0 1 := by
    ext z
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, mem_image, mem_Ioo]
    constructor
    · rintro ⟨hz, hzA, hzB⟩
      obtain ⟨t, rfl⟩ : z ∈ range f := hrange ▸ hz
      exact ⟨t, ⟨lt_of_le_of_ne t.2.1 fun h => hzA (by rw [← h, hf0]),
        lt_of_le_of_ne t.2.2 fun h => hzB (by rw [h, hf1])⟩, rfl⟩
    · rintro ⟨t, ⟨h0, h1'⟩, rfl⟩
      exact ⟨hrange ▸ mem_range_self t, fun h => h0.ne' (hf.injective (h.trans hf0.symm)),
        fun h => h1'.ne (hf.injective (h.trans hf1.symm))⟩
  rw [heq]
  refine ⟨isPreconnected_Ioo.image _ hf.continuous.continuousOn, ?_⟩
  obtain ⟨t, ht⟩ := exists_between (zero_lt_one : (0 : unitInterval) < 1)
  exact ⟨f t, mem_image_of_mem f ht⟩

/-- Two arcs `AB` meeting only in `A`, `B`: every arc from `A` to `B` inside their union is one
of them. -/
theorem arc_eq_of_subset_union {A B : S} {D₁ D₂ C : Set S} (hD₁ : σ.IsArc A B D₁)
    (hD₂ : σ.IsArc A B D₂) (hint : D₁ ∩ D₂ = {A, B}) (hCJ : C ⊆ D₁ ∪ D₂) (hC : σ.IsArc A B C) :
    C = D₁ ∨ C = D₂ := by
  letI := σ.topology
  haveI := t2Space h1
  obtain ⟨hpc, -⟩ := isPreconnected_diff_endpoints h1 h3 h4 h51 hC
  have hD₁c : IsClosed D₁ := ((isArc_iff_topological h1 h4).mp hD₁).2.1.isClosed
  have hD₂c : IsClosed D₂ := ((isArc_iff_topological h1 h4).mp hD₂).2.1.isClosed
  have hAB : ∀ z, z ∈ D₁ → z ∈ D₂ → z = A ∨ z = B := fun z h1' h2' => by
    have : z ∈ D₁ ∩ D₂ := ⟨h1', h2'⟩
    rw [hint] at this; simpa using this
  have hcov : C \ {A, B} ⊆ D₂ᶜ ∪ D₁ᶜ := by
    rintro z ⟨hzC, hzAB⟩
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hzAB (by simpa using hAB z h.2 h.1)
  have hdisj : C \ {A, B} ∩ (D₂ᶜ ∩ D₁ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_diff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzC h2' h1'
    rcases hCJ hzC.1 with h | h
    · exact h1' h
    · exact h2' h
  have hirr : ∀ {D : Set S}, σ.IsArc A B D → C ⊆ D → C = D := fun {D} hD hCD => by
    by_contra hne
    exact hD.2.2.2.2.2.2 C hCD hne hC.left_mem hC.right_mem hC.2.2.2.1
  rcases isPreconnected_iff_subset_of_disjoint.mp hpc _ _ hD₂c.isOpen_compl hD₁c.isOpen_compl
      hcov hdisj with h | h
  · left
    refine hirr hD₁ fun z hz => ?_
    by_cases hzAB : z = A ∨ z = B
    · rcases hzAB with rfl | rfl
      · exact hD₁.left_mem
      · exact hD₁.right_mem
    · have : z ∉ D₂ := h ⟨hz, by simpa using hzAB⟩
      exact (hCJ hz).resolve_right this
  · right
    refine hirr hD₂ fun z hz => ?_
    by_cases hzAB : z = A ∨ z = B
    · rcases hzAB with rfl | rfl
      · exact hD₂.left_mem
      · exact hD₂.right_mem
    · have : z ∉ D₁ := h ⟨hz, by simpa using hzAB⟩
      exact (hCJ hz).resolve_left this

/-- Moving an endpoint of a simple closed curve's representation: if `J = C₁ ∪ C₂` with `C₁`,
`C₂` arcs from `P` to `Q` meeting only in `P`, `Q`, and `X ∈ J` is neither, then `J` is the union
of two arcs from `X` to `Q` meeting only in `X`, `Q`. -/
theorem scc_rebase {P Q X : S} {C₁ C₂ : Set S} (hC₁ : σ.IsArc P Q C₁) (hC₂ : σ.IsArc P Q C₂)
    (hint : C₁ ∩ C₂ = {P, Q}) (hX : X ∈ C₁ ∪ C₂) (hXP : X ≠ P) (hXQ : X ≠ Q) :
    ∃ E₁ E₂, σ.IsArc X Q E₁ ∧ σ.IsArc X Q E₂ ∧ E₁ ∩ E₂ = {X, Q} ∧ E₁ ∪ E₂ = C₁ ∪ C₂ := by
  have main : ∀ C₁ C₂ : Set S, σ.IsArc P Q C₁ → σ.IsArc P Q C₂ → C₁ ∩ C₂ = {P, Q} → X ∈ C₁ →
      ∃ E₁ E₂, σ.IsArc X Q E₁ ∧ σ.IsArc X Q E₂ ∧ E₁ ∩ E₂ = {X, Q} ∧ E₁ ∪ E₂ = C₁ ∪ C₂ := by
    intro C₁ C₂ hC₁ hC₂ hint hX
    obtain ⟨Pa, Qa, hPa, hQa, hU, hI⟩ := fa_sec5_arc_split h1 h3 h4 h51 hC₁ hX hXP hXQ
    have hPaC₁ : Pa ⊆ C₁ := hU ▸ subset_union_left
    have hQaC₁ : Qa ⊆ C₁ := hU ▸ subset_union_right
    have hmem : ∀ z, z ∈ C₁ → z ∈ C₂ → z = P ∨ z = Q := fun z h1' h2' => by
      have : z ∈ C₁ ∩ C₂ := ⟨h1', h2'⟩
      rw [hint] at this; simpa using this
    have hPQa : ∀ z, z ∈ Pa → z ∈ Qa → z = X := fun z h1' h2' => by
      have : z ∈ Pa ∩ Qa := ⟨h1', h2'⟩
      rw [hI] at this; exact this
    have hPaC₂ : Pa ∩ C₂ = {P} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hz1, hz2⟩
        rcases hmem z (hPaC₁ hz1) hz2 with h | h
        · exact h
        · exact absurd (hPQa z hz1 (h ▸ hQa.right_mem)) (h ▸ hXQ.symm)
      · rintro rfl; exact ⟨hPa.left_mem, hC₂.left_mem⟩
    refine ⟨Qa, Pa ∪ C₂, hQa, (hPa.symm).union h1 h4 hC₂ hPaC₂, ?_, ?_⟩
    · ext z
      simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hzQ, hz | hz⟩
        · exact Or.inl (hPQa z hz hzQ)
        · rcases hmem z (hQaC₁ hzQ) hz with h | h
          · exact absurd (hPQa z (h ▸ hPa.left_mem) hzQ) (h ▸ hXP.symm)
          · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hQa.left_mem, Or.inl hPa.right_mem⟩
        · exact ⟨hQa.right_mem, Or.inr hC₂.right_mem⟩
    · rw [← hU]; ext z; simp only [mem_union]; tauto
  rcases hX with hX | hX
  · exact main C₁ C₂ hC₁ hC₂ hint hX
  · obtain ⟨E₁, E₂, h1', h2', h3', h4'⟩ := main C₂ C₁ hC₂ hC₁ (by rwa [inter_comm]) hX
    exact ⟨E₁, E₂, h1', h2', h3', by rw [h4', union_comm]⟩

/-- Two distinct points of a simple closed curve split it into two arcs meeting only in them. -/
theorem exists_two_arcs_of_isSCC {J : Set S} (hJ : σ.IsSCC J) {A B : S} (hA : A ∈ J)
    (hB : B ∈ J) (hAB : A ≠ B) :
    ∃ D₁ D₂, σ.IsArc A B D₁ ∧ σ.IsArc A B D₂ ∧ D₁ ∩ D₂ = {A, B} ∧ D₁ ∪ D₂ = J := by
  obtain ⟨P, Q, C₁, C₂, hC₁, hC₂, hint, rfl⟩ := hJ
  -- make `A` an endpoint
  obtain ⟨Z, E₁, E₂, hE₁, hE₂, hEi, hEu⟩ : ∃ Z E₁ E₂, σ.IsArc A Z E₁ ∧ σ.IsArc A Z E₂ ∧
      E₁ ∩ E₂ = {A, Z} ∧ E₁ ∪ E₂ = C₁ ∪ C₂ := by
    by_cases hAP : A = P
    · subst hAP; exact ⟨Q, C₁, C₂, hC₁, hC₂, hint, rfl⟩
    by_cases hAQ : A = Q
    · subst hAQ; exact ⟨P, C₁, C₂, hC₁.symm, hC₂.symm, by rw [hint, pair_comm], rfl⟩
    exact ⟨Q, scc_rebase h1 h3 h4 h51 hC₁ hC₂ hint hA hAP hAQ⟩
  by_cases hBZ : B = Z
  · subst hBZ; exact ⟨E₁, E₂, hE₁, hE₂, hEi, hEu⟩
  obtain ⟨F₁, F₂, hF₁, hF₂, hFi, hFu⟩ := scc_rebase h1 h3 h4 h51 hE₁.symm hE₂.symm
    (by rw [hEi, pair_comm]) (hEu ▸ hB) hBZ (Ne.symm hAB)
  exact ⟨F₁, F₂, hF₁.symm, hF₂.symm, by rw [hFi, pair_comm], hFu.trans hEu⟩

/-- p. 140 (unnumbered): two distinct points `A`, `B` of a simple closed curve `J` split it into
exactly two arcs from `A` to `B`, meeting only in `A` and `B`. *Axioms used: 1, 3, 4, 5₁.*
**Shape change:** the skeleton's Axioms 1–5 are reduced to 1, 3, 4, 5₁. -/
theorem fa_scc_two_arcs {J : Set S} (hJ : σ.IsSCC J) {A B : S} (hA : A ∈ J) (hB : B ∈ J)
    (hAB : A ≠ B) :
    ∃ C₁ C₂, σ.IsArc A B C₁ ∧ σ.IsArc A B C₂ ∧ C₁ ∩ C₂ = {A, B} ∧ C₁ ∪ C₂ = J ∧
      ∀ C ⊆ J, σ.IsArc A B C → C = C₁ ∨ C = C₂ := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu⟩ := exists_two_arcs_of_isSCC h1 h3 h4 h51 hJ hA hB hAB
  exact ⟨D₁, D₂, hD₁, hD₂, hDi, hDu, fun C hCJ hC =>
    arc_eq_of_subset_union h1 h3 h4 h51 hD₁ hD₂ hDi (hDu ▸ hCJ) hC⟩

end A1345

end HPC.Moore
