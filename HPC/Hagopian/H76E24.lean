import HPC.Hagopian.H76Restrict

/-!
# Batch 183, §2: E2.4 by Bing's arc `ab`

Commission 183 §2. Hagopian p. 348: "The point `yᵢ₋₁` is below `Cᵢ` and `ρ(yᵢ₋₁, d⁻¹[I]) ≥ ε₃`;
for otherwise, a subcontinuum of `L` would violate Property 2." Bing p. 227: "If `q` were above
`tu`, we would take `p = a` and let `b` be a point of `vw` between `p` and `x₂ᵢ₋₁x₂ᵢ`. If `q` were
below `tu` and `ρ(q, x₂ᵢ₋₁x₂ᵢ) < ε₄`, we would take `q` to be `b` and `a` to be a point of `tu`
between `q` and `x₂ᵢ₋₁x₂ᵢ`. Since the existence of such an arc `ab` violates the definition of
`ε₄`, we suppose that `ρ(q, x₂ᵢ₋₁x₂ᵢ) ≥ ε₄`."

* Steps 1–2 (the pair `a`, `b`): `Thm1Setup.cap_point_o` (the cap lemma returning the point of
  `Cl W` on the segment), `Thm1Setup.near_strand_cross_o`, `e24_pair_between` (Bing: "`q` above
  `tu`", `a = yᵢ`), `e24_pair_below` (Bing's second case, `b = yᵢ₋₁`).
* Step 3 (`H`): `minimalAdmissible_restrict` (`H76Restrict.lean`).
* Step 6: `Thm1Setup.exists_Rset_over` (a point of `R(E)` over `F(r, 0)`, e.g. over `p₄`,
  `r = 15/22`, or `p₂`, `r = 7/22`); `Thm1Setup.FarFrom` (named: `H` does not come within `ε₂` of
  `π⁻¹F(r, 0)`); `property2_violation`.
* Assembly: the named `Prop` `E24Claims` (steps 4–6 for the specific pair) and
  `e24_between_false`, `e24_below_far` (the field `far` of `Case1WitnessO`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section E24

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## Steps 1–2: the pair `a`, `b` -/

/-! ## Step 6: a point of `R(E)` over `F(r, 0)`, and the violation of Property 2 -/

/-- Every parameter of `[s, t]` is `restrictParam s t _ τ` for some `τ`. -/
theorem exists_restrictParam_eq {s t : unitInterval} (hst : s < t) {w : unitInterval}
    (hw : w ∈ Icc s t) : ∃ τ, restrictParam s t hst.le τ = w := by
  have hts : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 hst
  have h1 : (s : ℝ) ≤ w := hw.1
  have h2 : (w : ℝ) ≤ t := hw.2
  refine ⟨⟨((w : ℝ) - s) / (t - s), div_nonneg (by linarith) hts.le,
    (div_le_one hts).2 (by linarith)⟩, Subtype.ext ?_⟩
  show (s : ℝ) + ((w : ℝ) - s) / (t - s) * (t - s) = w
  rw [div_mul_cancel₀ _ hts.ne']
  ring

/-! ## Assembly: the field `far` -/

end E24

end HPC.Hagopian
