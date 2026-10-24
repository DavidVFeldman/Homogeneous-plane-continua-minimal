import HPC.Moore.M19CDOrder

/-!
# Moore 1919: refinement and padding of double rulings (batch 141, items A and E)

* `doubleRuling_refine` (item E): Moore's "the arcs of these rulings may be extended in such a way
  that there will result a new double ruling `τ₂` of `ABCDA` such that each arc of `τ₁` is also an
  arc of `τ₂`" (p. 175; again in Theorem E, p. 176), for the double rulings of the commission.
* `doubleRuling_pad` (item A): every double ruling with `n` and `m` arcs can be extended, by adding
  arcs, to a double ruling with `max n m` arcs in each ruling whose subdivisions lie in those of the
  given one. So the choice of different numbers `n`, `m` is a convenience, not a necessity: the
  printed definition (equal numbers) loses nothing.
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

/-- `ABCDA` has a double ruling all of whose subdivisions have property `Good`. -/
def Space.DoubleRulable (σ : Space S) (Good : Set S → Prop) {J I : Set S} {A B C D : S}
    {sAB sBC sCD sDA : Set S} (q : σ.Quad J I A B C D sAB sBC sCD sDA) : Prop :=
  ∃ n m : ℕ, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, Good U

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

section Ax

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

omit h2 h6 h7 h8 in
theorem Space.DoubleRuling.arcX_injective {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : Function.Injective R.arcX := by
  letI := σ.topology
  intro i i' h
  by_contra hne
  have hX := ((isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcX i)).left_mem
  exact disjoint_left.mp (R.disjX i i' hne) hX (h ▸ hX)

omit h2 h6 h7 h8 in
theorem Space.DoubleRuling.arcY_injective {q : σ.Quad J I A B C D sAB sBC sCD sDA} {n m : ℕ}
    (R : σ.DoubleRuling q n m) : Function.Injective R.arcY := by
  letI := σ.topology
  intro j j' h
  by_contra hne
  have hY := ((isArc_iff_tarc h1 h3 h4 (axiom5₁_of_axiom5 h5)).mp (R.isArcY j)).left_mem
  exact disjoint_left.mp (R.disjY j j' hne) hY (h ▸ hY)

/-- **Refinement of a double ruling** (item E; used without proof on pp. 175 and 176). Let `Good`
be a property of sets inherited by subsets (in Moore's uses: *lies within some curve, or region, of a
given set*; *lies wholly without `g₁, …, gₖ` or within some curve of `G`*). If every subdivision of
the double ruling `R` of `ABCDA`, taken as the interior of a quadrilateral in any way, has a double
ruling all of whose subdivisions are `Good`, then `ABCDA` has a double ruling `R′` such that each arc
of `R` is an arc of `R′`, and each subdivision of `R′` is `Good` and lies in a subdivision of `R`.
*Axioms used: 1–8.* -/
theorem doubleRuling_refine {Good : Set S → Prop} (hGood : ∀ U V, U ⊆ V → Good V → Good U)
    (q : σ.Quad J I A B C D sAB sBC sCD sDA) {n m : ℕ} (R : σ.DoubleRuling q n m)
    (H : ∀ {J' I' : Set S} {A' B' C' D' : S} {s₁ s₂ s₃ s₄ : Set S}
      (q' : σ.Quad J' I' A' B' C' D' s₁ s₂ s₃ s₄), I' ∈ R.cells → σ.DoubleRulable Good q') :
    ∃ n' m' : ℕ, ∃ R' : σ.DoubleRuling q n' m', (∀ i, ∃ i', R'.arcX i' = R.arcX i) ∧
      (∀ j, ∃ j', R'.arcY j' = R.arcY j) ∧ ∀ U ∈ R'.cells, Good U ∧ ∃ V ∈ R.cells, U ⊆ V := by
  have RA := R.toArcRuling h1 h3 h4 h5
  have H' : σ.CellsRulable Good I (⋃₀ range R.arcX ∪ ⋃₀ range R.arcY) := by
    intro J' I' A' B' C' D' s₁ s₂ s₃ s₄ q' hI'
    rw [← R.carrier_eq, ← R.cells_eq_cellsOf] at hI'
    obtain ⟨n'', m'', R'', hG⟩ := H q' hI'
    refine ⟨_, _, R''.toArcRuling h1 h3 h4 h5, ?_⟩
    rw [← R''.carrier_eq, ← R''.cells_eq_cellsOf]
    exact hG
  obtain ⟨𝒳', 𝒴', hX, hY, R₁, hP⟩ := RA.refine h1 h2 h3 h4 h5 h6 h7 h8 hGood q H'
  obtain ⟨R', hr₁, hr₂⟩ := R₁.toDoubleRuling h1 h2 h3 h4 h5 h7 h8 q
  refine ⟨_, _, R', fun i => ?_, fun j => ?_, fun U hU => ?_⟩
  · have : R.arcX i ∈ range R'.arcX := by rw [hr₁]; exact hX (mem_range_self i)
    exact this
  · have : R.arcY j ∈ range R'.arcY := by rw [hr₂]; exact hY (mem_range_self j)
    exact this
  · rw [R'.cells_eq_cellsOf, R'.carrier_eq, hr₁, hr₂] at hU
    rw [R.cells_eq_cellsOf, R.carrier_eq]
    exact hP U hU

end Ax

end HPC.Moore
