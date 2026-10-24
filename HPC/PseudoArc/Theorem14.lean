import HPC.PseudoArc.Theorem13
import HPC.Fold.BingCrook
import HPC.Fold.Pair79Chain
import HPC.Fold.Minimal
import HPC.Fold.OffCenter
import HPC.Fold.Faithful
import HPC.Fold.Zig77Main
import HPC.Fold.Splice78
import Mathlib.Tactic
import HPC.PseudoArc.T14Irred

/-!
# Bing 1948, Theorems 14 and 15: preliminaries; irreducible subcontinua

**Theorems 14 and 15 are proved**, in `HPC/PseudoArc/Thm14.lean` (`HPC.Description.theorem14`,
`HPC.Description.theorem15`, batch 115); the covering descriptions come from Lehner's Lemma 3
(`HPC/PseudoArc/Lehner.lean`, batch 114). Neither is open. This file keeps the preliminaries
(irreducible subcontinua, `theorem15_of_theorem14`, the reduction of the covering description to
one level).

Skeleton for batch 83 (save as `HPC/PseudoArc/Theorem14.lean`; add `import HPC.PseudoArc.Theorem14`
to the root `HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be
adjusted with the change recorded, except that `theorem14` and `theorem15` keep their conclusions.

Conventions as in `Theorem13.lean`: `Δ : Description X P Q` with `P ≠ Q` in a compact `X`;
`composant Δ.M p` is the union of the proper subcontinua of `Δ.M` containing `p`
(`Statements79.lean`); `Fold.Q78.IsContinuum K` is `IsCompact K ∧ IsConnected K`.

The hypotheses Bing leaves implicit and the skeleton states are listed in COMMISSION-batch83.md
§3.2 and §3.5: `W_i ≠ M` in Theorem 15; `P_i ≠ R_i` in Theorem 14; `Q_i ∈ M`.

*Batch 83 status.* `exists_irreducible`, `irreducible_unique` and `theorem15_of_theorem14` are
proved, statements unchanged. `exists_description_covering` is reduced
(`exists_description_covering_of_step`, proved) to the one-level claim `covering_step`;
`theorem14` was not proved in batch 83, so `theorem15` was then conditional on it (both are now
proved, see above). See REPORT-batch83.md.

*Batch 114.* `covering_step` and `exists_description_covering` are proved in
`HPC/PseudoArc/Lehner.lean` (Lehner's Lemma 3, `n = 2`) and have been moved there.

*Batch 115.* `theorem14` is proved in `HPC/PseudoArc/Thm14.lean` (the tracked alternating
construction) and has been moved there with `theorem15`, both with their statements unchanged.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- `W` is a continuum containing `A` and `B`, and no proper subcontinuum of `W` contains both:
Bing's "subcontinuum irreducible from `A` to `B`". -/
def IsIrreducibleBetween (W : Set X) (A B : X) : Prop :=
  Fold.Q78.IsContinuum W ∧ A ∈ W ∧ B ∈ W ∧
    ∀ K : Set X, Fold.Q78.IsContinuum K → K ⊆ W → A ∈ K → B ∈ K → K = W

/-- **Irreducible subcontinua exist.** A continuum containing `A` and `B` contains a subcontinuum
irreducible between them. (Zorn on the subcontinua containing `A` and `B`, ordered by reverse
inclusion; a nested intersection of continua is a continuum.) -/
theorem exists_irreducible [CompactSpace X] {K : Set X} (hK : Fold.Q78.IsContinuum K) {A B : X}
    (hA : A ∈ K) (hB : B ∈ K) : ∃ W, W ⊆ K ∧ IsIrreducibleBetween W A B := by
  set S : Set (Set X) := {W | W ⊆ K ∧ Fold.Q78.IsContinuum W ∧ A ∈ W ∧ B ∈ W}
  obtain ⟨m, hmK, hm⟩ := zorn_superset_nonempty S (fun c hcS hch hne => by
    refine ⟨⋂₀ c, ⟨?_, ⟨?_, ⟨A, ?_⟩, ?_⟩, ?_, ?_⟩, fun W hW => sInter_subset_of_mem hW⟩
    · obtain ⟨W, hW⟩ := hne
      exact (sInter_subset_of_mem hW).trans (hcS hW).1
    · exact (isClosed_sInter fun W hW => (hcS hW).2.1.1.isClosed).isCompact
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.1
    · exact T14.isPreconnected_sInter_chain hne hch (fun W hW => (hcS hW).2.1.1)
        (fun W hW => (hcS hW).2.1.2.isPreconnected)
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.1
    · exact mem_sInter.mpr fun W hW => (hcS hW).2.2.2) K ⟨subset_rfl, hK, hA, hB⟩
  obtain ⟨⟨-, hmc, hAm, hBm⟩, hmin⟩ := hm
  refine ⟨m, hmK, hmc, hAm, hBm, fun K' hK' hK'm hAK hBK => ?_⟩
  exact Subset.antisymm hK'm (hmin ⟨hK'm.trans hmK, hK', hAK, hBK⟩ hK'm)

namespace Description

variable {P Q : X}

-- `covering_step` and `exists_description_covering` moved to `HPC/PseudoArc/Lehner.lean` in batch
-- 114 (proved there by Lehner's Lemma 3, `n = 2`), with their statements unchanged.

-- `theorem14` (formerly open, item 3 of OPEN.md before batch 116) and `theorem15` moved to `HPC/PseudoArc/Thm14.lean`
-- in batch 115, where they are proved (Theorem 14 by the tracked alternating construction, Theorem
-- 15 by `theorem15_of_theorem14` as before), with their statements unchanged.

end Description

end HPC
