import HPC.Moore.Bridge

/-!
# Moore, F.A. (1916), §4: Theorems 11–14, and §5: Theorems 17–19 (batch 137, items C and E)

The section heading of F.A. §4 is "Consequences of Axioms 1–4, 5"; that of §5 is "Consequences
of Axioms 2–5 and Theorem 5". Each statement carries only the axioms its proof uses:

| statement | axioms used |
|---|---|
| Theorems 11, 12, 13, 14 | Axioms 1, 4 |
| Theorems 17, 18 | Axioms 1, 4, 5 |
| Theorem 19 | Axioms 1, 3, 4, 5 |

Moore's proofs go through Heine–Borel arguments; here they go through the bridge
(`HPC/Moore/Bridge.lean`): Moore's `M'` is the closure, Heine–Borel is compactness, and `(R₁ + ⋯ +
Rₙ)'` is compact by Axiom 4.

**Theorem 14 as printed is false** (`not_fa_theorem14_printed`): with every `Mₙ = ∅` its
hypotheses hold and its conclusion fails, in every space satisfying Axiom 1. Moore's proof begins
"For each `n`, `Mₙ` contains at least one point"; the hypothesis `hne` is needed.
-/

namespace HPC.Moore

open Set Topology Space

variable {S : Type*} {σ : Space S}

/-- Axiom 5 implies Axiom 5₁ (Moore, footnote p. 133: "this proposition is a part of
Axiom 5"). -/
theorem axiom5₁_of_axiom5 (h5 : σ.Axiom5) : Space.Axiom5₁ (S := S) := by
  obtain ⟨M, hM, -⟩ := h5
  obtain ⟨a, -⟩ := hM.nonempty
  obtain ⟨b, -, hba⟩ := (hM.diff (finite_singleton a)).nonempty
  obtain ⟨c, -, hc⟩ := (hM.diff (toFinite {a, b})).nonempty
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hc hba
  exact ⟨a, b, c, fun h => hba h.symm, fun h => hc.2 h.symm, fun h => hc.1 h.symm⟩

section Sec4

variable (h1 : σ.Axiom1) (h4 : σ.Axiom4)
include h1 h4

/-- **Theorem 12.** Every closed bounded set has the Heine–Borel property. *Axioms used: 1, 4.* -/
theorem fa_theorem12 {M : Set S} (hc : σ.IsClosedM M) (hb : σ.IsBoundedM M) :
    σ.HeineBorel M := by
  letI := σ.topology
  obtain ⟨C, hC, hMC⟩ := exists_isCompact_of_isBoundedM h1 h4 hb
  exact heineBorel_iff.mpr (hC.of_isClosed_subset ((isClosedM_iff h1).mp hc) hMC)

/-- **Theorem 13.** Every infinite bounded set has a limit point. (Moore: "see Hausdorff,
*Grundzüge*, p. 231"; no proof printed.) *Axioms used: 1, 4.* An infinite subset of a compact
set has an accumulation point. -/
theorem fa_theorem13 {M : Set S} (hi : M.Infinite) (hb : σ.IsBoundedM M) :
    ∃ P, σ.IsLimitPt P M := by
  letI := σ.topology
  obtain ⟨P, -, hP⟩ := hi.exists_accPt_of_subset_isCompact
    (isCompact_closure_of_isBoundedM h1 h4 hb) subset_closure
  exact ⟨P, (isLimitPt_iff h1).mpr hP⟩

end Sec4

section Sec5

variable (h1 : σ.Axiom1) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
include h1 h4 h5

/-- **Theorem 17.** The exterior of a region contains an infinite set with no limit point.
("A consequence of Axiom 5 and Theorem 13.") *Axioms used: 1, 4, 5.* The infinite set `M` of
Axiom 5 meets the bounded set `R'` in a finite set (Theorem 13), so `M − R'` will do. -/
theorem fa_theorem17 {R : Set S} (hR : R ∈ σ.region) :
    ∃ M ⊆ σ.ext R, M.Infinite ∧ ∀ P, ¬ σ.IsLimitPt P M := by
  obtain ⟨M, hM, hlim⟩ := h5
  have hfin : (M ∩ σ.cl R).Finite := by
    by_contra hinf
    obtain ⟨P, hP⟩ := fa_theorem13 h1 h4 hinf ⟨{R}, by simpa using hR, by simp⟩
    exact hlim P (hP.mono inter_subset_left)
  refine ⟨M \ σ.cl R, fun x hx => hx.2, by rw [← diff_self_inter]; exact hM.diff hfin, fun P hP => hlim P (hP.mono diff_subset)⟩

/-- **Theorem 19.** Every (nonempty) region has at least one boundary point.
*Axioms used: 1, 3, 4, 5.* Moore's proof: a region `Rₙ ∋ P` with `Rₙ' ⊆ R − X`; its exterior is
connected (Axiom 3) and meets both `R` (at `X`) and `S − R` (Theorem 17); a point of the exterior
outside `R` which is a limit point of the part inside `R` is a boundary point of `R`.
**Shape change:** `R.Nonempty` is added, as in Theorem 4 (`∅` has no boundary point). -/
theorem fa_theorem19 (h3 : σ.Axiom3) {R : Set S} (hR : R ∈ σ.region) (hne : R.Nonempty) :
    (σ.bdry R).Nonempty := by
  obtain ⟨P, hP⟩ := hne
  obtain ⟨X, hX, hXP⟩ := exists_ne_of_region h1 h3 (axiom5₁_of_axiom5 h5) hR hP
  obtain ⟨K, hK, hPK, hcl⟩ := exists_region_cl_subset_diff h1 hR hP hX hXP.symm
  obtain ⟨M, hMR, hMinf, -⟩ := fa_theorem17 h1 h4 h5 hR
  obtain ⟨Y, hY⟩ := hMinf.nonempty
  have hYK : Y ∈ σ.ext K := fun h => hMR hY ((hcl h).1 |> subset_cl R)
  have hYR : Y ∉ R := fun h => hMR hY (subset_cl R h)
  have hXK : X ∈ σ.ext K := fun h => (hcl h).2 rfl
  rcases h3 K hK (σ.ext K ∩ R) (σ.ext K \ R) (inter_union_diff _ _) disjoint_sdiff_inter.symm
      ⟨X, hXK, hX⟩ ⟨Y, hYK, hYR⟩ with ⟨Z, ⟨-, hZR⟩, hlim⟩ | ⟨Z, ⟨-, hZR⟩, hlim⟩
  · obtain ⟨W, ⟨-, hWR⟩, hW, -⟩ := hlim R hR hZR
    exact absurd hW hWR
  · exact ⟨Z, mem_bdry_of_isLimitPt (hlim.mono inter_subset_right) hZR⟩

end Sec5

end HPC.Moore
