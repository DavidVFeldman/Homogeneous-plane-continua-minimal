import HPC.BJ59.AtomicCircle
import HPC.BJ59.BJChains
import HPC.BJ59.Thm7
import HPC.BJ59.Thm7Ends2

/-!
# Batch 199: Part G, II — the circle-likeness step (Domokos–Prajs 2022, Theorem 6.1);
# Bing–Jones Theorems 7 and 9

The skeleton of commission 199. §§2–3 are in `HPC/BJ59/Atomic.lean` and §4 in
`HPC/BJ59/AtomicCircle.lean` and `HPC/BJ59/CircleLike.lean` (the statements verbatim, except where a
shape change is recorded at the statement); §§5–6 are here, except `IsBJChain` and
`exists_bjChain_shrink` (in `HPC/BJ59/BJChains.lean`).

Sources: A. Domokos and J. R. Prajs, *The Planck boundary within the hyperspace of the circle of
pseudo-arcs*, arXiv:2203.15906v1 (2022), §6 (`doc/sources/domokos-prajs2022.pdf`); R. H. Bing and
F. B. Jones, *Another homogeneous plane continuum*, Trans. AMS 90 (1959), §§4–5
(`doc/sources/bing-jones1959.pdf`; PDF page `n` is journal page `169 + n`). Route: commission 199.
-/

namespace HPC.BJ59

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.HO16

/- OPEN (batch 199, optional item of commission 199 §4): Domokos–Prajs's "one can easily show
that X is atriodic" (p. 14). Not attempted in this batch: the route of commission §4 (three
saturated continua whose images are arcs of the circle pairwise meeting exactly in one arc or
point) needs facts about subcontinua of the circle not developed here. The theorem is not used by
any route in this batch (Domokos–Prajs use it only for Hagopian–Marsh–Prajs Proposition 6, which
§3 replaces). See `OPEN.md`.

/-! **Domokos–Prajs (optional)**, p. 14: "one can easily show that X is atriodic". -/
theorem isAtriodic_of_atomic {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → Circle}
    (hf : IsAtomicCircPAMap f) : IsAtriodic (univ : Set X) := by
  sorry
-/

/-! ## §5. The decomposable case and the classification -/

/-- **The decomposable case without circle-likeness**: a decomposable homogeneous plane continuum
is a simple closed curve or has an open atomic map onto the circle with pseudo-arc fibres. -/
theorem circle_or_atomic_of_decomposable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]
    (hX : IsHomogeneous M) (hd : IsDecomposableSpace M) :
    Nonempty (M ≃ₜ Circle) ∨ ∃ f : M → Circle, IsAtomicCircPAMap f := by
  obtain ⟨hcd, ⟨e⟩, -⟩ := jones55_theorem2' hX hd
  set q : M → Circle := fun x => e (Quotient.mk _ x)
  have hqc : Continuous q := e.continuous.comp continuous_quotient_mk'
  have hqs : Function.Surjective q := e.surjective.comp Quotient.mk_surjective
  have hfib : ∀ x : M, q ⁻¹' {q x} = Lset x := fun x => by
    ext y
    simp only [mem_preimage, mem_singleton_iff, q, e.injective.eq_iff]
    rw [mk_eq_mk_iff_mem_cls, cls_lSetoid hX]
  by_cases hap : IsAposyndetic M
  · left
    have hinj : Function.Injective q := fun x y h => by
      have : y ∈ q ⁻¹' {q x} := h.symm
      rw [hfib, Lset_eq_singleton_of_isAposyndetic hap] at this
      exact this.symm
    exact ⟨hqc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q ⟨hinj, hqs⟩)⟩
  · right
    refine ⟨q, hqc, e.isOpenMap.comp (isOpenMap_quotient_mk_of_continuous hcd), hqs,
      fun z => ?_, fun z L hL hm => ?_⟩
    · obtain ⟨x, rfl⟩ := hqs z
      rw [hfib]
      exact isPseudoArc_Lset' hX hd x (jones55_elements hX hap x x).1
    · -- atomicity: Jones's elements are terminal (`jones55_c`)
      obtain ⟨x, rfl⟩ := hqs z
      rw [hfib] at hm ⊢
      by_cases h : L ⊆ Lset x
      · exact Or.inl h
      · obtain ⟨y, hyL, hy⟩ := not_subset.1 h
        exact Or.inr (jones55_c hX hL hm ⟨y, hyL, hy⟩)

/-- **`HOCircleLike`**, from Bing–Jones Theorem 10 and a plane circle of pseudo-arcs. -/
theorem hoCircleLike (h10 : BJThm10) (hEx : BJPlaneExample) : HOCircleLike := by
  intro M hc hk hX hd
  rcases circle_or_atomic_of_decomposable hX hd with he | ⟨f, hf⟩
  · obtain ⟨e⟩ := he
    exact isCircleLike_univ_of_homeomorph e isCircleLike_circle
  · obtain ⟨C, hC⟩ := hEx
    exact (isCircleOfPA_of_atomic h10 hf hC).1

/-- **The classification with Bing–Jones's third class**, from Theorem 10 and §7. -/
theorem ho16_classification₂ (h10 : BJThm10) (hEx : BJPlaneExample) (M : Set Pt)
    [CompactSpace M] [ConnectedSpace M] (hnt : (univ : Set M).Nontrivial) :
    IsHomogeneous M ↔ Nonempty (M ≃ₜ Circle) ∨ IsPseudoArc (univ : Set M) ∨ IsCircleOfPA M := by
  exact ho16_classification h10 (hoCircleLike h10 hEx) M hnt

/-- **The classification of homogeneous plane continua**, from Theorem 10 and §7. -/
theorem ho16_classification_plane₂ (h10 : BJThm10) (hEx : BJPlaneExample) :
    ∃ C₁ C₂ C₃ : Set Pt,
      (Nonempty (C₁ ≃ₜ Circle) ∧ IsPseudoArc C₂ ∧ IsCircleOfPA C₃) ∧
      (IsHomogeneous C₁ ∧ IsHomogeneous C₂ ∧ IsHomogeneous C₃) ∧
      (IsEmpty (C₁ ≃ₜ C₂) ∧ IsEmpty (C₁ ≃ₜ C₃) ∧ IsEmpty (C₂ ≃ₜ C₃)) ∧
      ∀ M : Set Pt, IsCompact M → IsConnected M → M.Nontrivial →
        (IsHomogeneous M ↔ Nonempty (M ≃ₜ C₁) ∨ Nonempty (M ≃ₜ C₂) ∨ Nonempty (M ≃ₜ C₃)) := by
  exact ho16_classification_plane h10 (hoCircleLike h10 hEx) hEx

/-! ## §6. Chains in Bing–Jones's sense; Theorems 7 and 9 -/

section Chains

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- OPEN (batch 199): Bing–Jones Theorem 9 (p. 179), the stretch item of commission 199 §6.
It needs the back-and-forth construction of a homeomorphism from two sequences of chains with
pattern maps (Bing–Jones pp. 179–180), resting on Theorem 7 and its second sentence (both proved
in this batch, `bj_theorem7`, `bj_theorem7_ends`); not attempted. See `OPEN.md`.

/-! **Bing–Jones, Theorem 9** (p. 179). -/
theorem bj_theorem9 {P : Set X} {Q : Set Y} (hP : IsPseudoArc P) (hQ : IsPseudoArc Q) {n m : ℕ}
    (D : Chain X n) (E : Chain Y m) (hD : IsBJChain D) (hE : IsBJChain E)
    (hDP : P ⊆ D.union) (hDp : ∀ i, (D.link i ∩ P).Nonempty)
    (hEQ : Q ⊆ E.union) (hEq : ∀ j, (E.link j ∩ Q).Nonempty)
    (H : Fin n → Fin m) (hH : IsChainMap H)
    (hHo : ∀ j, ∃ i, H i = j ∧ ∃ p ∈ P ∩ D.link i, ∀ i', i' ≠ i → p ∉ closure (D.link i')) :
    ∃ h : P ≃ₜ Q, ∀ (i : Fin n) (p : P), (p : X) ∈ D.link i → (h p : Y) ∈ E.link (H i) := by
  sorry
-/

end Chains

end HPC.BJ59
