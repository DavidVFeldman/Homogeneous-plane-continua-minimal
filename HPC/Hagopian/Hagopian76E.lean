import HPC.Hagopian.Hagopian76D
import HPC.Hagopian.H76Essential
import HPC.Hagopian.H76Defs
import HPC.Hagopian.H76Schoen

/-!
# Batch 160 skeleton: Hagopian 1976, Lemma 6 (steps 1–8) and the unnumbered claims, Lemma 7;
# two-sided Schoenflies, the metric form of upper semicontinuity, Lemma 9

The proofs are in `H76USC`, `H76Schoen2`, `H76Absorb`, `H76Lemma6`, `H76Step8`, `H76Composant`,
`H76Essential` (report `doc/batches/REPORT-batch160.md`). All statement shapes are the skeleton's,
unchanged. Lemma 7 and Lemma 9 remain open and are commented out below with their obstructions.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345.

**Already in the repository** (report 159 §1.A, item 1, overlooked them):
* `hagopian76_lemma4_chain`: extensions away from `X` are linearly ordered by inclusion;
* `hagopian76_lemma4`: no maximal element;
* `hagopian76_lemma4_seq`: the strictly increasing sequence `{Fᵢ}` with `R(X, E) = ⋃ Fᵢ`;
* `hagopian76_initial_segment`: each smaller extension is an initial segment of each larger one,
  with its layers among the larger one's (apply it with `E := F`, since both have end set `X`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## A. Lemma 6 -/

/-- **Lemma 6, first part** (pp. 342–343, steps 1–7): "First we prove that `Cl R(X, E)` is
indecomposable." Supporting lemmas for the steps are expected (commission §2 A). -/
theorem hagopian76_lemma6_X (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (extUnion E (layer k 0))) :=
  lemma6_X_aux hX hi hE

/-! ## B. Lemma 7 -/

-- `hagopian76_lemma7`: proved in batch 162, `Hagopian76G.lean`.

/-! ## C. Upper semicontinuity in metric form -/

end Section2

/-! ## D. Two-sided Schoenflies -/

/-! ## E. Lemma 9 (restated from `Hagopian76D.lean`) -/

section Lemma9

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

-- `hagopian76_lemma9` (Lemma 9, collar form): proved in batch 163, `Hagopian76H.lean`.

end Lemma9

end HPC.Hagopian
