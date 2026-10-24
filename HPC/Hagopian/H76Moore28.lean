import HPC.Jones.Jones49FTheta
import HPC.Jones.Whyburn

/-!
# Batch 158, item E: Moore 1962, Theorem 28

"If `D` is a simple domain and each of the two mutually exclusive continua `H` and `K` is a subset of
`D` [read: of `D ∪ J`] and each of them intersects `J`, the boundary of `D`, then no pair of points of
`H` separates two points of `K` from each other on `J`."

The excerpt of Moore 1962 in the repository breaks off inside the proof (p. 171 is followed by
p. 172 of a different section), so Moore's route could not be followed. The route used:

1. `J = P ∪ Q`, arcs from `a` to `b` (`tscc_split`); if `c`, `f` lie in different components of
   `J − {a, b}`, one lies in `P − {a, b}` and the other in `Q − {a, b}`.
2. `D` is the bounded side `I` of `J` (Jordan curve theorem); `E = (Cl D)ᶜ` is the other side.
3. An arc `L` from `a` to `b` lying, except for its ends, in `E` (`exists_exterior_arc`): `J` is
   aposyndetic and cyclic, so every point of `J` is accessible from `E` (`accessible_of_cyclic`,
   batch 152); two accessing arcs from a point of `E` are joined (`TArc.join`).
4. `P ∪ L` is a simple closed curve; its side `S` containing `Q − {a, b}` contains `D`, and the other
   side `T` misses `Cl D`.
5. Points `x ∈ T` near `c` and `y ∈ E` near `f` are joined in the complement of `H ∪ L` (through `K`)
   and in the complement of `Cl D` (in `E`); `(H ∪ L) ∩ Cl D = H` is connected. By Janiszewski's
   theorem (`janiszewski_compact`, batch 146) `L ∪ Cl D` does not separate `x` from `y`; but the
   component of `x` in its complement lies in `T`, and `y ∈ S`.

Neither the Schoenflies theorem nor the batch-151 crossing results are used.
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Moore.Gen HPC.Jones

section Moore28

/-- A simple closed curve splits at any two of its points into two arcs. -/
theorem tscc_split_at {J : Set Pt} (hJ : TSCC J) {a b : Pt} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ P Q : Set Pt, TArc a b P ∧ TArc a b Q ∧ P ∩ Q = {a, b} ∧ P ∪ Q = J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, h12, rfl⟩ := hJ
  exact tscc_split h₁ h₂ h12 ha hb hab

theorem TSCC.isCompact' {J : Set Pt} (hJ : TSCC J) : IsCompact J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, -, rfl⟩ := hJ
  exact h₁.isCompact.union h₂.isCompact

theorem TSCC.isConnected' {J : Set Pt} (hJ : TSCC J) : IsConnected J := by
  obtain ⟨s, t, C₁, C₂, h₁, h₂, -, rfl⟩ := hJ
  exact ⟨⟨s, Or.inl h₁.left_mem⟩,
    IsPreconnected.union s h₁.left_mem h₂.left_mem h₁.isPreconnected h₂.isPreconnected⟩

/-- A simple closed curve is aposyndetic. -/
theorem tscc_aposyndetic {J : Set Pt} (hJ : TSCC J) : IsAposyndetic J := by
  intro x y hxy
  have hxy' : (x : Pt) ≠ y := fun h => hxy (Subtype.ext h)
  obtain ⟨L₁, L₂, h₁, h₂, -, hU⟩ := tscc_split_at hJ x.2 y.2 hxy'
  obtain ⟨u, hu, hu'⟩ := h₁.nonempty_diff
  obtain ⟨v, hv, hv'⟩ := h₂.nonempty_diff
  have hux : u ≠ x := fun h => hu' (Or.inl h)
  have huy : u ≠ y := fun h => hu' (Or.inr h)
  have hvx : v ≠ x := fun h => hv' (Or.inl h)
  have hvy : v ≠ y := fun h => hv' (Or.inr h)
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, hΓU, hΓI⟩ := h₁.split hu hux huy
  obtain ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, hΔU, hΔI⟩ := h₂.split hv hvx hvy
  have hsubJ : Γ₁ ∪ Δ₁ ⊆ J := by
    rw [← hU, ← hΓU, ← hΔU]
    exact union_subset_union subset_union_left subset_union_left
  have himg : Subtype.val '' (Subtype.val ⁻¹' (Γ₁ ∪ Δ₁) : Set J) = Γ₁ ∪ Δ₁ := by
    rw [Subtype.image_preimage_coe]; exact inter_eq_right.2 hsubJ
  have hmem2 : ∀ {z w : Pt} {Γ Γ' : Set Pt}, Γ ∩ Γ' = {w} → z ∈ Γ → z ∈ Γ' → z = w :=
    fun {z w Γ Γ'} h hz hz' => by
      have h3 : z ∈ Γ ∩ Γ' := ⟨hz, hz'⟩
      rw [h] at h3; exact h3
  refine ⟨Subtype.val ⁻¹' (Γ₁ ∪ Δ₁), Subtype.val ⁻¹' (Γ₂ ∪ Δ₂)ᶜ, ⟨?_, ?_⟩,
    (hΓ₂.isClosed.union hΔ₂.isClosed).isOpen_compl.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · rw [Subtype.isCompact_iff, himg]; exact hΓ₁.isCompact.union hΔ₁.isCompact
  · refine ⟨⟨x, Or.inl hΓ₁.left_mem⟩, Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_⟩
    rw [himg]
    exact IsPreconnected.union (x : Pt) hΓ₁.left_mem hΔ₁.left_mem
      hΓ₁.isPreconnected hΔ₁.isPreconnected
  · rintro (h | h)
    · exact hux (hmem2 hΓI hΓ₁.left_mem h).symm
    · exact hvx (hmem2 hΔI hΔ₁.left_mem h).symm
  · intro z hz
    have hzJ : (z : Pt) ∈ L₁ ∪ L₂ := hU ▸ z.2
    rw [← hΓU, ← hΔU] at hzJ
    simp only [mem_preimage, mem_compl_iff, mem_union, not_or] at hz
    simp only [mem_preimage, mem_union]
    rcases hzJ with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd h hz.1
    · exact Or.inr h
    · exact absurd h hz.2
  · rintro (h | h)
    · exact huy (hmem2 hΓI h hΓ₂.right_mem).symm
    · exact hvy (hmem2 hΔI h hΔ₂.right_mem).symm

/-- A simple closed curve has no cut point. -/
theorem tscc_cyclic {J : Set Pt} (hJ : TSCC J) (z : J) : IsConnected ({z}ᶜ : Set J) := by
  obtain ⟨w, hwJ, hwz⟩ : ∃ w ∈ J, w ≠ (z : Pt) := by
    obtain ⟨s, t, C₁, C₂, h₁, h₂, -, hJeq⟩ := hJ
    by_cases hs : s = z
    · exact ⟨t, hJeq ▸ Or.inl h₁.right_mem, fun h => h₁.ne (hs.trans h.symm)⟩
    · exact ⟨s, hJeq ▸ Or.inl h₁.left_mem, hs⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, -, hU⟩ := tscc_split_at hJ z.2 hwJ hwz.symm
  have himg : Subtype.val '' ({z}ᶜ : Set J) = J \ {(z : Pt)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, fun h => hq (Subtype.ext h)⟩
    · rintro ⟨hp, hpz⟩; exact ⟨⟨p, hp⟩, fun h => hpz (congrArg Subtype.val h), rfl⟩
  refine ⟨⟨⟨w, hwJ⟩, fun h => hwz (congrArg Subtype.val h)⟩,
    Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_⟩
  have hJz : (L₁ ∪ L₂) \ {(z : Pt)} = J \ {(z : Pt)} := congrArg (fun S => S \ {(z : Pt)}) hU
  rw [himg, ← hJz, union_diff_distrib]
  exact IsPreconnected.union w ⟨hL₁.right_mem, hwz⟩
    ⟨hL₂.right_mem, hwz⟩ hL₁.symm.isPreconnected_diff_right hL₂.symm.isPreconnected_diff_right

/-- **Every point of a simple closed curve is accessible from each side**; in particular two points
`a ≠ b` of `J` are the ends of an arc lying, except for its ends, in a given side `E`. -/
theorem exists_side_arc {J : Set Pt} (hJ : TSCC J) {E : Set Pt} (hEc : IsConnected E)
    (hEJ : Disjoint E J) (hfE : frontier E = J) {a b : Pt} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ L : Set Pt, TArc a b L ∧ L \ {a, b} ⊆ E := by
  have hJc := TSCC.isCompact' hJ
  have hJconn := TSCC.isConnected' hJ
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  haveI : ConnectedSpace J := isConnected_iff_connectedSpace.1 hJconn
  have hS : ∀ z : J, SemiLocConnAt z := semiLocConn_of_isAposyndetic (tscc_aposyndetic hJ)
  obtain ⟨w, hw⟩ := hEc.nonempty
  have hwJ : w ∉ J := disjoint_left.1 hEJ hw
  have hcc : connectedComponentIn Jᶜ w = E := side_eq_cc hEc.isPreconnected hfE hEJ hw
  obtain ⟨Ca, hCa, hCaE⟩ := accessible_of_cyclic hJc hJconn hS (tscc_cyclic hJ) hwJ
    (p := a) (by rw [hcc, hfE]; exact ha) (y := w) (by rw [hcc]; exact hw)
    (fun h => hwJ (h ▸ ha))
  obtain ⟨Cb, hCb, hCbE⟩ := accessible_of_cyclic hJc hJconn hS (tscc_cyclic hJ) hwJ
    (p := b) (by rw [hcc, hfE]; exact hb) (y := w) (by rw [hcc]; exact hw)
    (fun h => hwJ (h ▸ hb))
  obtain ⟨L, hLsub, hL⟩ := hCa.symm.join hCb.symm ⟨w, hCa.left_mem, hCb.left_mem⟩ hab
  refine ⟨L, hL, fun z hz => ?_⟩
  rcases hLsub hz.1 with h | h
  · rw [← hcc]; exact hCaE ⟨h, fun h' => hz.2 (Or.inl h')⟩
  · rw [← hcc]; exact hCbE ⟨h, fun h' => hz.2 (Or.inr h')⟩

end Moore28

end HPC.Hagopian
