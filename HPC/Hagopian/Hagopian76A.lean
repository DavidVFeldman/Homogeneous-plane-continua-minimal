import HPC.Hagopian.H76Lemma2
import HPC.Hagopian.H76Lemma4
import HPC.Hagopian.H76Lemma4Ext
import HPC.Hagopian.H76NoMax
import HPC.Hagopian.H76Lemma4Layers
import HPC.Hagopian.H76Lemma3
import HPC.Plane.SorgenfreyDefs
import HPC.Hagopian.H76Defs

/-!
# Batch 156 skeleton: Hagopian 1976, §2 (Lemmas 2–8) and the consequences of Theorem 1

Batch 156 (`doc/batches/COMMISSION-batch156.md`). Supporting proofs are in `H76*.lean`. Items
that remain open are commented out (no `sorry`), each with an `OPEN (batch 156)` note; their
obstructions are in `OPEN.md`. Shape changes are recorded at the statement and in
`doc/batches/REPORT-batch156.md`.

Source: C. L. Hagopian, *Indecomposable homogeneous plane continua are hereditarily
indecomposable*, Trans. AMS 224 (1976), 339–350 (`doc/sources/hagopian1976.pdf`), read from page
images at 200 dpi. Here `[5]` is Hagopian 1975 (`HPC/Hagopian/Hagopian75.lean`) and `[14]` is
Thomas 1966 (not in hand).

§2 (p. 340): "In this section `M` is an indecomposable homogeneous continuum in `R²` and `E` is a
type A′ subcontinuum of `M`. Let `k : E → [0, 1]` be the quotient map associated with the minimal
admissible decomposition of `E` [5, Lemma 3]. Hereafter, we shall refer to this decomposition as
simply *the decomposition* of `E`." In the skeleton, "the decomposition" is an admissible map whose
layers have void interior (`IsMinimalAdmissible`); by `hagopian75_lemma3_unique` its layers are
determined by `E`.

Lemma 9 and Theorem 1 (the quotient `R²/S`, decomposable accessibility, Properties 1–4) are for
batch 157.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! The definitions (p. 340) and `Hagopian76Thm1` are in `H76Defs.lean`, verbatim. -/

/-! ## §2. Lemmas 2–8 -/

section Section2

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- **Lemma 2** (p. 340). "Suppose `ε` is a given positive number and `x` is a point of `M`. Then
`{y ∈ M: an ε-homeomorphism of M onto M takes x to y}` is an open subset of `M` that contains `x`
[5, Lemma 4 (proof)]." -/
theorem hagopian76_lemma2 (hX : IsHomogeneous M) {ε : ℝ} (hε : 0 < ε) (x : M) :
    IsOpen {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} ∧
      x ∈ {y : M | ∃ h : M ≃ₜ M, h x = y ∧ ∀ v, dist v (h v) < ε} := by
  exact lemma2_aux hX hε x

/-- **Lemma 3** (p. 340). "Let `Y` be an element of the decomposition of `E` distinct from the end
sets `X` and `Z` of `E`. Let `F` be a type A′ subcontinuum of `M` with end sets `T` and `V`, and let
`U` be an element of the decomposition of `F` distinct from `T` and `V`. Suppose `h` is a
homeomorphism of `M` onto `M` such that `U ∩ h[Y] ≠ ∅` and `U ∩ h[X ∪ Z] = ∅ = h[Y] ∩ (T ∪ V)`.
Then `h[Y] = U`." Proof: "This lemma follows from the argument presented in paragraphs 9 through 11
in the proof of Theorem 1 of [5]." The printed hypotheses carry no `ε`, unlike
`hagopian75_layer_invariant`; record what replaces it.

*What replaces `ε`:* the hypothesis `h[Y] ∩ (T ∪ V) = ∅`. With it the 1975 ¶9 triod puts `h[Y]` inside
`F`; then `J = F ∩ h[E]` is a continuum, and with `[γ, δ] = k(h⁻¹[J])`: if `γ = s` (or `δ = s`), the
continuum `h k⁻¹[[0, s]]` (or `h k⁻¹[[s, 1]]`) meets `F` only in `h[Y]`, so by the same triod it lies in
`F`, which puts `h[X]` (or `h[Z]`) in `h[Y]`; if `γ < s < δ` and `h[Y] ≠ U`, `h[Y]` contains an open
subset of `F`, and the 1975 ¶10 argument (a neighbourhood meeting `h[E]` only in `h[Y]`) gives `Y`
nonvoid interior in `E`. So `h[Y] ⊆ U`; the same for `h⁻¹`, `U`, `Y` (using `U ∩ h[X ∪ Z] = ∅`) gives
`U ⊆ h[Y]`. The 1975 argument goes through; Lemma 3 holds as printed. See `H76Lemma3.lean`.

*Shape change:* `hu0 : 0 < u` and `hu1 : u < 1` are dropped (not used: `U` meets `h[Y]`, which misses
`T ∪ V`, so `U` is neither end set). -/
theorem hagopian76_lemma3 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E F : Set M}
    {k : E → unitInterval} {d : F → unitInterval} (hE : IsMinimalAdmissible E k)
    (hF : IsMinimalAdmissible F d) {s u : unitInterval} (hs0 : 0 < s) (hs1 : s < 1)
    (h : M ≃ₜ M) (h1 : (layer d u ∩ h '' layer k s).Nonempty)
    (h2 : Disjoint (layer d u) (h '' (layer k 0 ∪ layer k 1)))
    (h3 : Disjoint (h '' layer k s) (layer d 0 ∪ layer d 1)) :
    h '' layer k s = layer d u :=
  lemma3_aux (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hF hs0 hs1 h h1 h2 h3

-- `hagopian76_lemma4_layers` (D1): re-rendered as printed in `Hagopian76B.lean` (open, batch 157; see `OPEN.md`).

/-- **Lemma 4, linear order** (the first half of `hagopian76_lemma4`). The proof is Hagopian's triod
(`ext_chain`, `H76Lemma4.lean`); the first paragraph is not needed. -/
theorem hagopian76_lemma4_chain (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} :=
  fun _ hF _ hH _ => ext_chain (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE hF hH

/-- **Lemma 4** (p. 340). "The collection `𝓕` of extensions of `E` away from the end set `X` is
linearly ordered by inclusion and does not have a maximal element." Proof (p. 341): "If `H` is an
element of `𝓕`, then `F ⊂ H` or `H ⊂ F`; for otherwise, the continuum `H ∩ d⁻¹[[s, 1]]` (Lemma 1)
would separate `F ∪ H` into three nonempty disjoint open sets"; and, for no maximal element, "it is
a proper subset of an element of `𝓕` that is contained in `F ∪ h⁻¹[F]` (Lemma 1)".

The linear order is `ext_chain` (`H76Lemma4.lean`). "No maximal element" is
`exists_proper_extension` (`H76NoMax.lean`); the step Hagopian leaves unargued (how a proper
extension inside `F ∪ h⁻¹[F]` is obtained) is supplied there by a case analysis on how `h⁻¹[F]`
meets `F` (see `OPEN.md`, batch 156, item D2, now closed). -/
theorem hagopian76_lemma4 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    IsChain (· ⊆ ·) {F | IsExtensionAway E (layer k 0) F} ∧
      ∀ F ∈ {F | IsExtensionAway E (layer k 0) F},
        ∃ H ∈ {F | IsExtensionAway E (layer k 0) F}, F ⊂ H :=
  lemma4_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE

/-- **Lemma 4, the countable form used in Lemma 6** (p. 342). "Since `M` is second countable, there
exists a monotone strictly increasing sequence `{Fᵢ}` of elements of `𝓕` such that
`R(X, E) = ⋃ Fᵢ` (Lemma 4)." -/
theorem hagopian76_lemma4_seq (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    ∃ Fs : ℕ → Set M, StrictMono Fs ∧ (∀ i, IsExtensionAway E (layer k 0) (Fs i)) ∧
      extUnion E (layer k 0) = ⋃ i, Fs i :=
  lemma4_seq_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hE

-- `hagopian76_lemma5`: proved in batch 158, `Hagopian76C.lean`.

/- OPEN (batch 156): `hagopian76_closure_extUnion` — depends on Lemmas 4 and 5. See `OPEN.md`, batch 156, item F.

/-- **Lemma 6, the step "`Cl R(X, E) = Cl R(E)`"** (p. 343): "We complete this proof by showing that
`Cl R(X, E) = Cl R(E)` … (see the second paragraph in the proof of Theorem 1 of [5])." -/
theorem hagopian76_closure_extUnion (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    closure (extUnion E (layer k 0)) = closure (Rset k) := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_lemma6` — depends on Lemmas 4 and 5. See `OPEN.md`, batch 156, item F.

/-- **Lemma 6** (p. 341). "The continuum `Cl R(E)` is indecomposable." -/
theorem hagopian76_lemma6 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E : Set M}
    {k : E → unitInterval} (hE : IsMinimalAdmissible E k) :
    Fold.Q78.IsIndecomposable (closure (Rset k)) := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_Rset_composant` — depends on Lemma 6. See `OPEN.md`, batch 156, item F.

/-- **"Since `M` is atriodic, `R(E)` is a composant of `Cl R(E)`"** (p. 343, unnumbered). -/
theorem hagopian76_Rset_composant (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {x : M}
    (hx : x ∈ Rset k) : Rset k = HPC.composant (closure (Rset k)) x := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_essential_typeA'` — depends on Lemma 5. See `OPEN.md`, batch 156, item F.

/-- **"Note that every continuum essential to `R(E)` is of type A′ (Lemma 5)"** (p. 343,
unnumbered). -/
theorem hagopian76_essential_typeA' (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M)
    {E : Set M} {k : E → unitInterval} (hE : IsMinimalAdmissible E k) {H : Set M}
    (hH : IsEssential k H) : IsTypeA' H := by
  sorry
-/

/- OPEN (batch 156): `hagopian76_lemma7` — depends on Lemmas 5 and 6. See `OPEN.md`, batch 156, item G.

/-- **Lemma 7** (p. 343). "For each positive number `ε`, there exists a positive number `δ` such
that if `h` is a `δ`-homeomorphism of `M` onto `M`, then `h[R(E)]` has the following property. If
`H` is a continuum essential to `h[R(E)]` with end sets `T` and `V` such that `ρ(T, V) < δ` and if
there exists an element `U` of the decomposition of `H` such that `ρ(T, U) > ε`, then each point of
`R(E)` is within `ε` of `H`." Shape: "essential to `h[R(E)]`" is read as `h⁻¹[H]` essential to
`R(E)`; `ρ` between sets is the infimum distance (attained, the sets being compact). -/
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

/-! ## Theorem 1 as a statement, and its consequences -/

section Consequences

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

end Consequences

end HPC.Hagopian
