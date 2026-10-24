import HPC.Moore.M19A

/-!
# Moore 1919: the arc of footnote * of p. 174, used in Theorem D (batch 140, item B)

Theorem D (p. 173) uses: "Within `g₁` (and within `J` except for the point `A₁`) there is* an arc
`A₁E′₁` that has in common with `E₁E′₁` only the point `E′₁`", with footnote *: "Make use of
Theorems 43 and 40 and the existence of the curve `ABTNA` described on page 149 of *Foundations*".
`m19_D_arc` states it in the form Theorem D needs and proves it without Theorem 43: the component
`Q` of `I_g − J` containing `E₁E′₁ − E₁` stays connected when the arc `E₁E′₁` is removed
(`hair_isPreconnected`, Kline's proof of Theorem 33 for any connected open set: this is the role of
the curve `ABTNA`), it has the points of the interval `E₁A₁` of `J` as limit points
(`side_propagate`), and batch 138's `accessible` reaches `A₁` and `E′₁` from it.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- **Theorem 33 for any connected open set** (Kline's proof, as in `fa_theorem33`, which uses only
that the region is open and connected): if `A ∉ R`, `B ∈ R` and the arc `AB` has `AB − A ⊆ R`, then
`R − AB` is connected. *Axioms used: 1–8.* -/
theorem hair_isPreconnected (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h5 : σ.Axiom5) (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8) {R : Set S}
    (hRo : @IsOpen S σ.topology R) (hRc : @IsPreconnected S σ.topology R) {A B : S} (hAR : A ∉ R)
    (hB : B ∈ R) {K : Set S} (hK : @TArc S σ.topology A B K) (hKR : K \ {A} ⊆ R) :
    @IsPreconnected S σ.topology (R \ K) := by
  letI := σ.topology
  haveI := t2Space h1
  have h51 := axiom5₁_of_axiom5 h5
  have harc := arcConn h1 h3 h4 h51 h2
  obtain ⟨hAB, g, hg, rfl, rfl, rfl⟩ := hK
  have hKarc : TArc (g 0) (g 1) (range g) := ⟨hAB, g, hg, rfl, rfl, rfl⟩
  have hgO : ∀ u ∈ Ioo 0 1, g u ∈ R := fun u hu =>
    hKR ⟨mem_range_self u, fun e => hu.1.ne' (hg.injective e)⟩
  have step1 : ∀ P ∈ R \ range g, ∃ Γ, TArc P (g 1) Γ ∧ Γ ⊆ R ∧ Γ ∩ range g = {g 1} := by
    intro P hP
    obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P hP.1 (g 1) hB
      (fun e => hP.2 (e ▸ mem_range_self 1))
    exact reach_end h1 h2 h3 h4 h5 h6 h7 h8 hg hRo hgO hB hP hΓ₀ hΓ₀R (mem_range_self 1)
      (fun h => hAR (hΓ₀R h))
  refine isPreconnected_of_forall_pair fun P hP P' hP' => ?_
  obtain ⟨Γ, hΓ, hΓR, hΓK⟩ := step1 P hP
  have hPB : P ≠ g 1 := fun e => hP.2 (e ▸ mem_range_self 1)
  by_cases hP'Γ : P' ∈ Γ
  · refine ⟨Γ \ {g 1}, fun x hx => ⟨hΓR hx.1, fun h => hx.2 ?_⟩, ⟨hΓ.left_mem, hPB⟩,
      ⟨hP'Γ, fun e => hP'.2 (e ▸ mem_range_self 1)⟩, hΓ.isPreconnected_diff_right⟩
    have : x ∈ Γ ∩ range g := ⟨hx.1, h⟩
    rwa [hΓK] at this
  have hK'' : TArc P (g 0) (Γ ∪ range g) := hΓ.union hKarc.symm hΓK
  obtain ⟨-, φ, hφ, hφr, hφ0, hφ1⟩ := hK''.symm
  have hφO : ∀ u ∈ Ioo 0 1, φ u ∈ R := by
    intro u hu
    have hu' : φ u ∈ Γ ∪ range g := hφr ▸ mem_range_self u
    have hne : φ u ≠ g 0 := fun e => hu.1.ne' (hφ.injective (e.trans hφ0.symm))
    rcases hu' with h | h
    · exact hΓR h
    · exact hKR ⟨h, hne⟩
  have hP'φ : P' ∈ R \ range φ := ⟨hP'.1, by rw [hφr]; rintro (h | h); exacts [hP'Γ h, hP'.2 h]⟩
  have hPP' : P' ≠ P := fun e => hP'Γ (e ▸ hΓ.left_mem)
  obtain ⟨Γ₀, hΓ₀R, hΓ₀⟩ := harc R hRo hRc P' hP'.1 P hP.1 hPP'
  obtain ⟨τ, hτ, hτR, hτK⟩ := reach_end h1 h2 h3 h4 h5 h6 h7 h8 hφ hRo hφO (hφ1 ▸ hP.1) hP'φ
    hΓ₀ hΓ₀R (hφ1 ▸ mem_range_self 1) (by rw [hφ0]; exact fun h => hAR (hΓ₀R h))
  rw [hφ1] at hτ hτK
  refine ⟨τ, fun x hx => ⟨hτR hx, fun h => hP.2 ?_⟩, hτ.right_mem, hτ.left_mem, hτ.isPreconnected⟩
  have : x ∈ τ ∩ range φ := ⟨hx, hφr ▸ Or.inr h⟩
  rw [hτK] at this
  exact this ▸ h

end HPC.Moore
