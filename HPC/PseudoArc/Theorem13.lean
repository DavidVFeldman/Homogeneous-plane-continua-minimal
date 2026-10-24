import HPC.PseudoArc.Theorem5
import HPC.PseudoArc.T13Step

/-!
# Bing 1948, Theorem 13: the described continuum is homogeneous

Skeleton for batch 81 (save as `HPC/PseudoArc/Theorem13.lean`; add `import HPC.PseudoArc.Theorem13`
to the root `HPC.lean`). Statements only; every proof was a `sorry` work item (batch 81: all filled in). The auxiliary
statements are the claims of Bing's proof (COMMISSION-batch81.md §3) that the repository does not
yet have; their shapes may be adjusted, with the change recorded, provided `theorem13` is reached.

## Batch-81 record

All four statements are proved; no statement was reshaped. The only edits to the skeleton are the
two index-bound placeholders in `exists_subchain_meets_ends` (`0 < Δ.n j`, discharged from
`Δ.isFrom j`) and the import of the supporting files:

* `T13Topo.lean` — limits of finely chained sets are connected; a proper subcontinuum of an
  indecomposable continuum has empty interior (clopen boundary bumping); Baire.
* `T13Chains.lean` — `M` is connected; subchains between two points; the limit argument of
  Bing's first paragraph.
* `T13Step.lean` — Theorem 4 (`Fold.theorem4_pair`) on a subchain from `R` to `S`; one step of
  the sequence `E_1, E_2, …`; the description from `R` to `S`.

The hypothesis `hnd : M.Nontrivial` of `composant_ne_of_indecomposable` turned out to be
unnecessary (for `M` a single point the composant is empty); it is kept because the skeleton has it.
-/

namespace HPC

open Set

variable {X : Type*} [MetricSpace X]

/-- **Composants are proper.** In an indecomposable continuum `M` the composant of any point is
not all of `M` (Bing uses this at p. 740, "a point belonging to a composant of `M` not containing
`P_n`"). Standard proof: the composant is a countable union of proper subcontinua, each with empty
interior in `M`; Baire.

(Batch 81: the hypothesis `hnd` is not used by the proof.) -/
theorem composant_ne_of_indecomposable [CompactSpace X] {M : Set X}
    (hM : Fold.Q78.IsIndecomposable M) (hnd : M.Nontrivial) {p : X} (hp : p ∈ M) :
    composant M p ≠ M := by
  obtain ⟨y, hyM, hy⟩ := T13.exists_not_mem_proper_subcontinua (M := M) hM hp
  intro heq
  have hyc : y ∈ composant M p := by rw [heq]; exact hyM
  obtain ⟨K, ⟨hK, hKM, hKne, hpK⟩, hyK⟩ := mem_sUnion.mp hyc
  exact hy K hK hKM hKne hpK hyK

namespace Description

variable {P Q : X}

end Description

end HPC
