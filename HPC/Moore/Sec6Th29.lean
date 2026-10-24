import HPC.Moore.Sec6Th28

/-!
# Moore, F.A. (1916), §6: Theorems 29 and 30 (batch 138, item B)

**Theorem 29.** If `A`, `B` separate `C`, `D` on `J`, and the open arcs `AXB`, `CYD` are both
within or both without `J`, then they meet.

**Theorem 30.** Under the same hypothesis, the interiors of `AXBDA` and `CYDBC` meet. (No proof
printed.)

Moore's proof of Theorem 29 (pp. 145–146): Case I (both within) by Theorem 25; Case II (both
without) by Theorem 27. In Case I Moore argues with a point `P` of `CYD` near `C`; here the same
argument is phrased with Axiom 2: the connected open arc `CYD` lies in `R₁ + R₂` (Theorem 25)
and so in one of them, but `D` is without `R₁` and `C` without `R₂` (Theorem 24).

The proof of Theorem 30 supplied here (`Gen.th30`) uses a point `Q` of `J`, on the open arc `ADB`
and on the open arc `DBC`, near `D`. Case I: near `Q`, the points of `R` lie in `R₁` (Theorems
24, 25 for `AXB`) and in `R₂` (Theorems 24, 25 for `CYD`). Case II: Theorem 27 for `AXB` and for
`CYD` gives two alternatives each; in the four combinations a common point is found in `R`, near
`C`, near a point of the other arc `DAC` of `J`, or near `Q` outside `J` (Theorem 20).
-/

namespace HPC.Moore

open Set Topology

namespace Gen

variable {T : Type*} [TopologicalSpace T] [T2Space T] {reg : Set (Set T)}

omit [T2Space T] in
/-- An arc `AXB` whose open part misses `J`, together with an arc `ACB` of `J`, forms a closed
curve. -/
theorem tscc_of_open_disjoint {J : Set T} {A B : T} {Ci Xa : Set T} (hCi : TArc A B Ci)
    (hX : TArc A B Xa) (hCiJ : Ci ⊆ J) (hXJ : ∀ x ∈ Xa \ {A, B}, x ∉ J) : TSCC (Xa ∪ Ci) := by
  refine ⟨A, B, Xa, Ci, hX, hCi, ?_, rfl⟩
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    by_contra h
    exact hXJ x ⟨hx, h⟩ (hCiJ hxC)
  · rintro (rfl | rfl)
    · exact ⟨hX.left_mem, hCi.left_mem⟩
    · exact ⟨hX.right_mem, hCi.right_mem⟩

/-- Theorem 27, both alternatives: if the open arc `AXB` is without `J`, then the interior of
`AXBDA` is `ACB (open) + R + R₁`, or the interior of `AXBCA` is `ADB (open) + R + R₂`. -/
theorem th27_dich [LocallyConnectedSpace T] (hopen : ∀ R ∈ reg, IsOpen R)
    (hpc : ∀ R ∈ reg, IsPreconnected R) (h21 : Th21Prop reg) (harc : ArcConn T)
    (h8 : Ax8Prop reg) (hext : ∀ R ∈ reg, IsPreconnected (closure R)ᶜ)
    (hcpt : ∀ R ∈ reg, IsCompact (closure R)) (hnc : ¬ IsCompact (univ : Set T))
    {J R : Set T} (hR : TInt reg J R) {A B C D : T} {C₁ C₂ : Set T} (hC₁ : TArc A B C₁)
    (hC₂ : TArc A B C₂) (hC12 : C₁ ∩ C₂ = {A, B}) (hCJ : C₁ ∪ C₂ = J)
    (hC : C ∈ C₁ \ {A, B}) (hD : D ∈ C₂ \ {A, B})
    {Xa : Set T} (hX : TArc A B Xa) (hXR : Xa \ {A, B} ⊆ (closure R)ᶜ) {R₁ R₂ : Set T}
    (hR₁ : TInt reg (Xa ∪ C₁) R₁) (hR₂ : TInt reg (Xa ∪ C₂) R₂) :
    R₂ = C₁ \ {A, B} ∪ R ∪ R₁ ∨ R₁ = C₂ \ {A, B} ∪ R ∪ R₂ := by
  have h := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₁ hC₂ hC12 hCJ hC hD hX hXR hR₁ hR₂
  have h' := th27 hopen hpc h21 harc h8 hext hcpt hnc hR hC₂ hC₁
    (by rw [inter_comm]; exact hC12) (by rw [union_comm]; exact hCJ) hD hC hX hXR hR₂ hR₁
  rcases h.1 with h1 | h1
  · exact Or.inl (h.2 h1).2
  · exact Or.inr (h'.2 h1).2

end Gen

variable {S : Type*} {σ : Space S}

end HPC.Moore
