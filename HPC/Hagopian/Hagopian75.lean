import HPC.Hagopian.H75Transfer
import HPC.Hagopian.H75Composants
import HPC.Jones.Jones49F
import HPC.Jones.Jones55T2A
import HPC.Plane.Atriodic51Defs
import HPC.Hagopian.H75Thm1B
import HPC.Hagopian.H75Basic
import HPC.Hagopian.H75MooreB
import HPC.Hagopian.H75Defs

/-!
# Batch 155 skeleton: Hagopian 1975, *Homogeneous plane continua*, §§2–5 (Lemmas 1–4; the
type A′ subcontinuum; the invariance and homogeneity of interior layers)

Save as `HPC/Hagopian/Hagopian75.lean` (splitting under `HPC/Hagopian/` is expected); add
`import HPC.Hagopian.Hagopian75` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may
be adjusted, each change recorded at the statement and in the report.

Source: C. L. Hagopian, *Homogeneous plane continua*, Houston J. Math. 1 (1975), 35–41
(`doc/sources/hagopian1975.pdf`), read from page images at 200 dpi. Hagopian's *continuum* is
nondegenerate (p. 35).

Other sources:
* Moore, *Foundations of point set theory*, rev. ed. 1962 (`doc/sources/moore1962-excerpts.pdf`:
  pp. 15, 49–50, 58–59, 156, 172–175, 214–223), Theorems 135–139 (composants), Theorem 22 p. 175
  (Janiszewski), Theorem 84 p. 222 (triods).
* Kuratowski, *Topology* Vol. 2 (1968), §48, pp. 190–220 (`doc/sources/kuratowski2-s48.pdf`):
  irreducible continua, layers, Theorems VII.1–6. This replaces Thomas 1966 (Rozprawy Mat. 50),
  which is not in hand.

**Use downstream.** Hagopian 1976 (Trans. AMS 224) cites this paper's Lemma 1, Lemma 3, the proof of
Lemma 4, paragraphs 1–3 of the proof of Theorem 1 (a type A′ subcontinuum exists) and paragraphs
9–11 (the invariance of an interior layer). Paragraph 4 of that proof (a nondegenerate layer exists)
cites Bing 1960 (Canad. J. Math. 12), which 1976 does not use; it is isolated here as a hypothesis.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## §2–3. Definitions -/

section Defs

variable {X : Type*} [MetricSpace X]

end Defs

/-! ## Composants (Moore 1962, Theorems 135–139, pp. 58–59) -/

section Composants

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Moore Theorem 135.** Every composant of a nondegenerate compact continuum is dense. -/
theorem composant_dense [Nontrivial X] (x : X) : Dense (Jones.composant x) :=
  composant_dense' x

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Moore Theorem 138.** Two composants of an indecomposable continuum are equal or disjoint.
(Reuse `HPC/PseudoArc/Theorem13.lean` if it applies.)

*Shape change (generalization):* the section's `[CompactSpace X] [ConnectedSpace X]` are omitted
(not used: the argument is the decomposition `K ∪ L` of a union of two proper subcontinua). -/
theorem composant_eq_or_disjoint (hi : ¬ IsDecomposableSpace X) (x y : X) :
    Jones.composant x = Jones.composant y ∨ Disjoint (Jones.composant x) (Jones.composant y) :=
  composant_eq_or_disjoint' hi x y

/-- **Moore Theorem 139.** An indecomposable nondegenerate compact continuum has uncountably many
composants.

*Shape change:* the skeleton's conclusion `(range (Jones.composant : X → Set X)).Uncountable` does
not elaborate (Mathlib has no `Set.Uncountable`); it is stated as `¬ (range …).Countable`. -/
theorem uncountable_composants [Nontrivial X] (hi : ¬ IsDecomposableSpace X) :
    ¬ (range (Jones.composant : X → Set X)).Countable :=
  uncountable_composants' hi

end Composants

/-! ## Moore's triod theorem (Moore 1962, Theorem 84, p. 222) -/

/-! ## §2. Lemma 1 -/

section Lemma1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Lemma 1** (p. 36). "If `M` is a homogeneous indecomposable plane continuum, then `M` is
atriodic and hereditarily unicoherent." Proof, first paragraph: composants (Moore 138, 139); "Since
`M` is homogeneous, it follows that each of its composants contains a triod"; Moore 84. Second
paragraph: "Note that `F` separates the plane [Moore 22, p. 175]. Since the plane is separable and
`M` has uncountably many composants, there exists a proper subcontinuum of `M` having two
complementary domains that intersect `M`. This contradicts the fact that each composant is dense in
`M` [Moore 135]." (No nondegeneracy hypothesis: for a point both conclusions hold vacuously. Add
`[Nontrivial M]` if the proof wants it, and record it.)

Statement verbatim. No nondegeneracy hypothesis is needed. Atriodicity uses Moore's triod theorem
(`mooreTriodStatement`); hereditary unicoherence does not (`hagopian75_lemma1_hu`). -/
theorem hagopian75_lemma1 (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) :
    IsAtriodic (univ : Set M) ∧ IsHereditarilyUnicoherent (univ : Set M) :=
  ⟨atriodic_of_homogeneous_indecomposable mooreTriodStatement hX hi,
    hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi⟩

/-- **Lemma 1, second paragraph**, unconditionally: a homogeneous indecomposable plane continuum is
hereditarily unicoherent. (Moore 22 by Borsuk's theorem; the "separable" step by disjointness of the
complementary domains missing `M`; the density step by Baire and Moore 138; see `H75Lemma1.lean`.) -/
theorem hagopian75_lemma1_hu (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) :
    IsHereditarilyUnicoherent (univ : Set M) :=
  hereditarilyUnicoherent_of_homogeneous_indecomposable hX hi

end Lemma1

/-! ## §3. Lemmas 2 and 3: type A′ continua -/

section TypeA

variable {X : Type*} [MetricSpace X]

/-! **End sets** (used in Hagopian 1976 §2, citing Thomas Theorem 8, p. 14). For an admissible map
of a continuum irreducible between `a` and `b`, `a` and `b` lie in the two end layers; and a
subcontinuum meeting both end layers is all of `E`.

**Refuted as stated** (`not_admissible_end_sets`, `H75Counter.lean`): the second half fails without
the type A′ condition. On `E = [0, 2] ⊆ ℝ`, irreducible between `0` and `2`, the map
`k(x) = max 0 (x − 1)` is admissible with end layer `k⁻¹(0) = [0, 1]`, and `K = [1, 2]` meets both end
layers. The statement is kept, commented out; `admissible_end_sets'` below adds `hk0`. -/
/-
theorem admissible_end_sets {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b) (hab : a ≠ b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) :
    ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
      ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty → (K ∩ layer k 1).Nonempty →
        K = E := by
  sorry
-/

/-- **End sets, corrected.** *Shape change:* the type A′ hypothesis `hk0` is added (it is satisfied
wherever Hagopian 1976 uses end sets: the map of a type A′ continuum); `hab` is dropped (not used).
The first half holds for every admissible map (`end_layers`). -/
theorem admissible_end_sets' {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b)
    {k : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) :
    ((k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0)) ∧
      ∀ K ⊆ E, Fold.Q78.IsContinuum K → (K ∩ layer k 0).Nonempty → (K ∩ layer k 1).Nonempty →
        K = E :=
  ⟨end_layers hE hk, fun _ hKE hK h0 h1 => eq_of_meets_ends hE hk hk0 hKE hK h0 h1⟩

/-- **Uniqueness.** Two admissible maps of a type A′ continuum whose layers have void interior have
the same layers. So the decomposition is intrinsic, and a homeomorphism carries it to the
decomposition of the image (as paragraph 10 of Theorem 1 uses). -/
theorem hagopian75_lemma3_unique {E : Set X} (hE : ∃ a b, IsIrreducibleBetween E a b)
    {k k' : E → unitInterval} (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hk' : IsAdmissibleMap E k') (hk'0 : ∀ t, interior (k' ⁻¹' {t}) = ∅) :
    ∀ x y : E, k x = k y ↔ k' x = k' y := by
  obtain ⟨a, b, hab⟩ := hE
  exact fibre_eq_iff hab hk hk0 hk' hk'0

/-! **Paragraph 4, the alternative** (Thomas Theorem 21, p. 29; Kuratowski §48 VII, Theorem 6): if
every interior layer of a type A′ continuum is degenerate, the continuum is an arc.

**Refuted as stated** (`not_arc_of_degenerate_layers`, `H75Sine.lean`): the `sin (1/x)`-continuum
`E = {(x, sin (1/x)) : 0 < x ≤ 1} ∪ ({0} × [−1, 1])` is irreducible between `(1, sin 1)` and `(0, 0)`,
the projection `k(x, y) = x` is admissible, its layers have void interior, and its interior layers
are points; but `E` is not an arc — the end layer `k⁻¹(0)` is not degenerate. What Hagopian uses
("`E` would contain an arc") is proved as `exists_arc_of_degenerate_layers`, and the arc conclusion
under degeneracy of *all* layers as `arc_of_degenerate_layers'` (`H75Counter.lean`). The printed
statement is kept, commented out. -/
/-
theorem arc_of_degenerate_layers {E : Set X} {a b : X} (hE : IsIrreducibleBetween E a b)
    (hab : a ≠ b) {k : E → unitInterval} (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅)
    (hdeg : ∀ s : unitInterval, 0 < s → s < 1 → (layer k s).Subsingleton) :
    Nonempty (E ≃ₜ unitInterval) := by
  sorry
-/

end TypeA

/-! ## §4. Lemma 4 -/

/-- **Lemma 4** (p. 37). "Suppose `M` is a homogeneous continuum, `ε` is a given positive number,
and `x` is a point of `M`. Then `x` belongs to an open subset `W` of `M` having the following
property. For each pair `y, z` of points of `W` there exists a homeomorphism `h` of `M` onto `M`
such that `h(y) = z` and `ρ(v, h(v)) < ε` for all `v` belonging to `M`." From
`HPC.Effros.effros_homogeneous`. -/
theorem hagopian75_lemma4 {Y : Type*} [MetricSpace Y] [CompactSpace Y] (hX : IsHomogeneous Y)
    {ε : ℝ} (hε : 0 < ε) (x : Y) :
    ∃ W : Set Y, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, ∀ z ∈ W,
      ∃ h : Y ≃ₜ Y, h y = z ∧ ∀ v, dist v (h v) < ε := by
  obtain ⟨δ, hδ, hh⟩ := HPC.Effros.effros_homogeneous hX hε
  refine ⟨ball x (δ / 2), isOpen_ball, mem_ball_self (half_pos hδ), fun y hy z hz => ?_⟩
  have hyz : dist y z < δ := by
    have := dist_triangle_right y z x
    rw [mem_ball] at hy hz
    linarith
  obtain ⟨h, hyz', hmove⟩ := hh y z hyz
  exact ⟨h, hyz', fun v => by rw [dist_comm]; exact hmove v⟩

/-! ## §5. Theorem 1, paragraphs 1–3 and 5–13 -/

section Theorem1

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **Theorem 1, paragraphs 1–3** (p. 38), the part Hagopian 1976 cites ("[5, Theorem 1
(paragraphs 1, 2, and 3 of proof)]"): a decomposable subcontinuum of a homogeneous indecomposable
plane continuum contains a continuum of type A′.

Statement verbatim. -/
theorem hagopian75_exists_typeA' (hX : IsHomogeneous M)
    (hi : ¬ IsDecomposableSpace M) {A : Set M} (hA : Fold.Q78.IsContinuum A)
    (hAd : ¬ Fold.Q78.IsIndecomposable A) : ∃ E ⊆ A, IsTypeA' E :=
  exists_typeA'_aux hX (hagopian75_lemma1_hu hX hi) (hagopian75_lemma1 hX hi).1 hA hAd

end Theorem1

end HPC.Hagopian
