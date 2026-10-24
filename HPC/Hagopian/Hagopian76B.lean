import HPC.Hagopian.Hagopian76A
import HPC.Hagopian.H76D1
import HPC.Hagopian.H76Lemma5
import HPC.Hagopian.H76NoSep
import HPC.Hagopian.H76Defs
import HPC.Moore.Sec6Arc
import HPC.Moore.M25C

/-!
# Batch 157 skeleton: Hagopian 1976, §2 continued (the first paragraph of Lemma 4; Lemmas 5–7)
# and the set-up of Theorem 1 (the quotient `R²/S`, the arc `π[E]`, accessibility)

Batch 157 (`doc/batches/COMMISSION-batch157.md`; report `doc/batches/REPORT-batch157.md`). The
skeleton is kept as `doc/batches/skeletons/Hagopian76B.lean`. Supporting proofs are in
`H76SepInv.lean`, `H76NoSep.lean`, `H76D1.lean`, `H76Lemma5.lean`, `H76Setup.lean`; the definitions
of the set-up (`layerKey`, `layerSetoid`, `IsAccessibleFrom`) are moved, verbatim, to
`H76BDefs.lean`. Items that remain open are commented out (no `sorry`), each with an
`OPEN (batch 157)` note; their obstructions are in `OPEN.md`. Shape changes are recorded at the
statement and in the report.

Source: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 341–345, read from page images at
200 dpi. Batch 156 left D1, E, F, G open (`OPEN.md`).

**Standing remark** (batch 156): under the section hypotheses no type A′ `E` exists (Theorem 1), so
no statement here can be refuted inside a homogeneous indecomposable `M`; a statement can only be
proved, or shown not to follow from the hypotheses actually used (by a model without homogeneity).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## D1. The first paragraph of Lemma 4 -/

-- `hagopian76_lemma4_layers` (re-rendered): proved in batch 158, `Hagopian76C.lean`.

-- `hagopian76_no_swallowed_layer`: proved in batch 158, `Hagopian76C.lean`.

/-! ## E. Lemma 5 -/

-- `hagopian76_lemma5`: proved in batch 158, `Hagopian76C.lean`.

/- OPEN (batch 157): `hagopian76_two_sided_extension` — the natural argument (irreducibility of `F₁ ∪ F₂`, then Kuratowski and the 1975 ¶2 argument as in `ext_of_branch`) needs the tails `d₁⁻¹[[s₁, 1]]`, `d₂⁻¹[[s₂, 1]]` to meet `E` only in `Z`, `X` respectively, so that `F₁ ∩ F₂ = E`: D1 at both ends. Without it the tails may overlap inside `E`. See `OPEN.md`, batch 157, item B.

/-- **The continuum `F` of Lemma 5** (p. 341): "There exists a type A′ continuum `F` in `R(E)` that
is the union of two extensions of `E` such that the end sets `T` and `V` of `F` miss `E` (Lemma
4)." -/
theorem hagopian76_two_sided_extension (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ (F₁ F₂ : Set M) (d : (F₁ ∪ F₂ : Set M) → unitInterval),
      IsExtensionAway E (layer k 0) F₁ ∧ IsExtensionAway E (layer k 1) F₂ ∧
      IsMinimalAdmissible (F₁ ∪ F₂) d ∧ Disjoint (layer d 0 ∪ layer d 1) E := by
  sorry
-/

/-! ## F. Lemma 6 and the unnumbered claims (restated verbatim from `Hagopian76A.lean`) -/

/- OPEN (batch 157): `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`, `hagopian76_essential_typeA'` — each uses Lemma 5 at the end sets (the decomposition of an extension `F` is continuous at its end sets and has the decomposition of `E` as a subcollection, the latter being D1). Steps 1–8 of Lemma 6 are checked in `doc/batches/REPORT-batch157.md` §1.C; not formalized. See `OPEN.md`, batch 157, item C.

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343). -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry
-/

/-! ## G. Lemma 7 (restated verbatim from `Hagopian76A.lean`) -/

/- OPEN (batch 157): `hagopian76_lemma7` — uses Lemma 5 (the decompositions of essential continua) and Lemma 6 (the limit points `t`, `u`, `p` in `Cl R(E)`, and the essential continuum `F` of `fhᵢ[R(E)]`); blocked by items B and C. See `OPEN.md`, batch 157, item D.

/-- **Lemma 7** (p. 343). -/
theorem hagopian76_lemma7 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : M ≃ₜ M, (∀ v, dist v (h v) < δ) →
      ∀ H : Set M, IsEssential k (h ⁻¹' H) → ∀ d : H → unitInterval, IsMinimalAdmissible H d →
        (∃ t ∈ layer d 0, ∃ v ∈ layer d 1, dist t v < δ) →
        (∃ u : unitInterval, ∀ t ∈ layer d 0, ∀ w ∈ layer d u, ε < dist t w) →
        ∀ p ∈ Rset k, ∃ q ∈ H, dist p q < ε := by
  sorry
-/

end Section2

/-! ## H. The set-up of Theorem 1 (pp. 344–345) -/

section Setup

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **"Since `M` is indecomposable and homogeneous, no proper subcontinuum of `M` separates `R²` [5,
Lemma 1 (second paragraph of proof)]"** (p. 344). To be extracted from the proof of
`hereditarilyUnicoherent_of_homogeneous_indecomposable` (`H75Lemma1.lean`).

*Proof* (`no_proper_subcontinuum_separates_aux`, `H76NoSep.lean`): the 1975 argument, with one
supplied step. The copies `h[K]` of `K` in the composants of `M` need not be known to separate the
plane (that would be Borsuk's invariance theorem); it suffices that each contains a separating
continuum, which is `exists_separating_subcontinuum_of_homeomorph` (`H76SepInv.lean`: `z − p` has no
logarithm on a separating `K`, every nonvanishing map has one on a tree-like continuum, and Bing's
Theorem 6 makes a continuum without separating subcontinua tree-like). -/
theorem no_proper_subcontinuum_separates (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {K : Set M} (hK : Fold.Q78.IsContinuum K) (hKM : K ≠ univ) : ¬ SeparatesPlane (toPt K) :=
  no_proper_subcontinuum_separates_aux hX hi hK hKM

/-! `layerKey`, `layerSetoid` (the relation `S`, p. 345) and `IsAccessibleFrom` are in
`H76BDefs.lean`, verbatim. -/

end Setup

end HPC.Hagopian
