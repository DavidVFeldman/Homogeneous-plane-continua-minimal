import HPC.Jones.Defs
import HPC.PseudoArc.Statements79

/-!
# Batch 135: Jones 1948, §§1–2 — Theorems 0–5 and 7–10

Theorem 6 is in `HPC/Jones/Theorem6.lean`.

* Theorems 1 and 2 are consequences of `isOpen_setOf_aposAt` (the pairs of aposyndesis form an
  open subset of `X × X`). Theorem 1 holds without its hypotheses `x ≠ y` and `yᵢ ≠ xᵢ`.
* Theorem 3 (no proof printed): closedness as for Theorem 2; connectedness from
  `aposAt_of_frontier` (finite covers and boundary bumping).
* Theorem 0 (\"with the help of the Heine–Borel theorem\"): finite covers.
* Theorems 4 and 5: projections of closed subsets of `X × X`.
* Theorem 7: Jones's continuum `H₀ + M₁(c₂)`, with `H₀` a product of a closed ball and a factor.
* Theorems 8–10, and the refutation of Theorem 10 as printed (`theorem10_printed_iff`,
  `not_theorem10_printed_unitInterval`).
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### The repository's notions -/

section Equivalences

variable [ConnectedSpace X]

theorem isContinuum_univ : Fold.Q78.IsContinuum (univ : Set X) :=
  ⟨isCompact_univ, isConnected_univ⟩

/-- `IsDecomposableSpace X` is the negation of `Fold.Q78.IsIndecomposable univ`. -/
theorem isDecomposableSpace_iff_not_isIndecomposable :
    IsDecomposableSpace X ↔ ¬ Fold.Q78.IsIndecomposable (univ : Set X) := by
  constructor
  · rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩ ⟨-, h⟩
    rcases h H K hH hK (subset_univ _) (subset_univ _) hHK with h | h
    · exact hHu h
    · exact hKu h
  · intro h
    by_contra hd
    apply h
    refine ⟨isContinuum_univ, fun A B hA hB _ _ hAB => ?_⟩
    by_contra hne
    push_neg at hne
    exact hd ⟨A, B, hA, hB, hne.1, hne.2, hAB⟩

end Equivalences

/-! ### Theorems 1–5 -/

omit [CompactSpace X] in
/-- The set of Theorem 3 is the set of all `x` with `X` not aposyndetic at `x` w.r.t. `y`. -/
theorem setOf_theorem3_eq (y : X) :
    {x | x ≠ y ∧ ¬ AposAt x y} ∪ {y} = {x | ¬ AposAt x y} := by
  ext x
  by_cases hx : x = y
  · subst hx; simp [not_aposAt_self]
  · simp [hx]

/-- **Theorem 3.** The set `L` of points `x ≠ y` such that `X` is not aposyndetic at `x` with
respect to `y`, together with `y`, is a continuum. (No proof printed. This is Jones 1955's `L_y`.)

Proof: `L` is closed (`isClosed_not_aposAt_left`). If `L = A ∪ B` with `A ∋ y`, `B` disjoint
nonempty closed, take an open `V ⊇ B` with `closure V ∩ A = ∅`; the frontier of `V` misses `L`, so
by `aposAt_of_frontier` `X` is aposyndetic at the points of `B` with respect to `y`. -/
theorem theorem3 [ConnectedSpace X] (y : X) :
    Fold.Q78.IsContinuum ({x | x ≠ y ∧ ¬ AposAt x y} ∪ {y}) := by
  rw [setOf_theorem3_eq]
  set L := {x | ¬ AposAt x y} with hL
  have hLcl : IsClosed L := isClosed_not_aposAt_left y
  have hyL : y ∈ L := not_aposAt_self y
  refine ⟨hLcl.isCompact, ⟨y, hyL⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  -- the key claim, for the piece containing `y`
  have key : ∀ u v : Set X, IsClosed u → IsClosed v → L ⊆ u ∪ v → L ∩ (u ∩ v) = ∅ → y ∈ u →
      L ⊆ u := by
    intro u v hu hv hLuv hLuv' hyu b hbL
    by_contra hbu
    have hbv : b ∈ v := (hLuv hbL).resolve_left hbu
    have hAcl : IsClosed (L ∩ u) := hLcl.inter hu
    have hBcl : IsClosed (L ∩ v) := hLcl.inter hv
    have hAB : L ∩ v ⊆ (L ∩ u)ᶜ := by
      rintro z ⟨hzL, hzv⟩ ⟨-, hzu⟩
      have : z ∈ L ∩ (u ∩ v) := ⟨hzL, hzu, hzv⟩
      rw [hLuv'] at this; exact this
    obtain ⟨V, hV, hBV, hVA⟩ := normal_exists_closure_subset hBcl hAcl.isOpen_compl hAB
    have hbV : b ∈ V := hBV ⟨hbL, hbv⟩
    have hyV : y ∉ closure V := fun h => hVA h ⟨hyL, hyu⟩
    have hfr : ∀ z ∈ frontier V, AposAt z y := by
      intro z hz
      by_contra hzna
      have hzL : z ∈ L := hzna
      rcases hLuv hzL with hzu | hzv
      · exact hVA hz.1 ⟨hzL, hzu⟩
      · exact hz.2 (by rw [hV.interior_eq]; exact hBV ⟨hzL, hzv⟩)
    exact hbL (aposAt_of_frontier hV hbV hyV hfr)
  intro u v hu hv hLuv hLuv'
  rcases hLuv hyL with hyu | hyv
  · exact Or.inl (key u v hu hv hLuv hLuv' hyu)
  · refine Or.inr (key v u hv hu (by rwa [union_comm]) ?_ hyv)
    rwa [inter_comm v u]

/-! ### Theorem 0 -/

/-- **Theorem 0.** `X` is semi-locally-connected at `p` iff it is aposyndetic at each point of
`X − p` with respect to `p`. (\"May be established with the help of the Heine–Borel theorem.\") -/
theorem theorem0 [ConnectedSpace X] (p : X) : SemiLocConnAt p ↔ ∀ x, x ≠ p → AposAt x p := by
  classical
  constructor
  · intro h x hxp
    set d := dist x p with hd
    have hdpos : 0 < d := dist_pos.mpr hxp
    obtain ⟨V, hV, hpV, hVU, F, hFV, hcov⟩ := h (ball p (d / 2)) isOpen_ball (mem_ball_self
      (half_pos hdpos))
    set O : Set X := (closedBall p (d / 2))ᶜ with hO
    have hOopen : IsOpen O := isClosed_closedBall.isOpen_compl
    have hxO : x ∈ O := by
      simp only [hO, mem_compl_iff, mem_closedBall, not_le]; linarith
    have hOU : O ⊆ (ball p (d / 2))ᶜ := compl_subset_compl.mpr ball_subset_closedBall
    obtain ⟨O', hO', hxO', hO'C⟩ := exists_open_subset_component hV.isClosed_compl F hOopen hxO
      (hOU.trans hcov)
    have hxV : x ∈ Vᶜ := by
      obtain ⟨c, -, hxc⟩ := mem_iUnion₂.mp (hcov (hOU hxO))
      exact connectedComponentIn_subset _ _ hxc
    refine ⟨connectedComponentIn Vᶜ x, O', ⟨(isClosed_connectedComponentIn'
      hV.isClosed_compl x).isCompact, isConnected_connectedComponentIn_iff.mpr hxV⟩, hO', hxO',
      hO'C, fun hp => ?_⟩
    exact connectedComponentIn_subset _ _ hp hpV
  · intro h U hU hpU
    obtain ⟨t, H, U', htH, hcov⟩ := exists_finite_apos_cover hU.isClosed_compl.isCompact
      (y := p) (fun x hx => h x fun hxp => hx (hxp ▸ hpU))
    have hHne : ∀ i ∈ t, (H i).Nonempty := fun i hi => (htH i hi).1.2.nonempty
    choose! c hc using hHne
    set V : Set X := U ∩ (⋃ i ∈ t, H i)ᶜ with hVdef
    have hVopen : IsOpen V :=
      hU.inter (isClosed_biUnion_finset fun i hi => (htH i hi).1.1.isClosed).isOpen_compl
    have hpV : p ∈ V := by
      refine ⟨hpU, fun hp => ?_⟩
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact (htH i hi).2.2.2 hpi
    have hHV : ∀ i ∈ t, H i ⊆ Vᶜ := fun i hi z hz hzV =>
      hzV.2 (mem_iUnion₂.mpr ⟨i, hi, hz⟩)
    refine ⟨V, hVopen, hpV, inter_subset_left, t.image c, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hHV i hi (hc i hi)
    · intro z hz
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hz)
      refine mem_iUnion₂.mpr ⟨c i, Finset.mem_image_of_mem c hi, ?_⟩
      exact (htH i hi).1.2.isPreconnected.subset_connectedComponentIn (hc i hi) (hHV i hi)
        ((htH i hi).2.2.1 hzi)

/-! ### Theorem 7 -/

section Theorem7

variable {Y Z : Type*} [MetricSpace Y] [ConnectedSpace Y] [MetricSpace Z] [ConnectedSpace Z]

end Theorem7

/-! ### §2: Theorems 8–10 -/

section Indecomposable

variable [ConnectedSpace X]

omit [CompactSpace X] [ConnectedSpace X] in
/-- In a decomposition `X = H ∪ K` into proper subcontinua, `X` is aposyndetic at each point of
`X − K` with respect to each point of `X − H`. -/
theorem aposAt_of_decomposition {H K : Set X} (hH : Fold.Q78.IsContinuum H) (hK : IsClosed K)
    (hHK : H ∪ K = univ) {x y : X} (hx : x ∉ K) (hy : y ∉ H) : AposAt x y := by
  refine ⟨H, Kᶜ, hH, hK.isOpen_compl, hx, fun z hz => ?_, hy⟩
  have : z ∈ H ∪ K := hHK ▸ mem_univ z
  exact this.resolve_right hz

/-- **Theorem 8.** `X` is decomposable iff there are distinct `x`, `y` with `X` aposyndetic at `x`
with respect to `y`. -/
theorem theorem8 : IsDecomposableSpace X ↔ ∃ x y : X, x ≠ y ∧ AposAt x y := by
  constructor
  · rintro ⟨H, K, hH, hK, hHu, hKu, hHK⟩
    obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem K).mp hKu
    obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem H).mp hHu
    have h := aposAt_of_decomposition hH hK.1.isClosed hHK hx hy
    exact ⟨x, y, h.ne, h⟩
  · rintro ⟨x, y, -, H, U, hH, hU, hxU, hUH, hyH⟩
    have hHu : H ≠ univ := fun h => hyH (h ▸ mem_univ y)
    by_cases hc : IsPreconnected Hᶜ
    · -- `X = H ∪ closure (X − H)`
      refine ⟨H, closure Hᶜ, hH, ⟨isClosed_closure.isCompact, ⟨y, subset_closure hyH⟩,
        hc.closure⟩, hHu, ?_, ?_⟩
      · intro h
        have hx : x ∈ closure Hᶜ := h ▸ mem_univ x
        obtain ⟨z, hzU, hzH⟩ := mem_closure_iff.mp hx U hU hxU
        exact hzH (hUH hzU)
      · exact eq_univ_of_forall fun z => by
          by_cases hz : z ∈ H
          · exact Or.inl hz
          · exact Or.inr (subset_closure hz)
    · obtain ⟨A, B, hA, hB, hcov, hAB, hBA⟩ := Plane.exists_separated_of_not_isPreconnected hc
      have hcov' : univ \ H = A ∪ B := by rw [← hcov]; ext; simp
      have hcov'' : univ \ H = B ∪ A := by rw [hcov', union_comm]
      have h1 := Plane.isContinuum_union_piece isContinuum_univ hH (subset_univ _) hcov' hAB hBA
      have h2 := Plane.isContinuum_union_piece isContinuum_univ hH (subset_univ _) hcov''
        hBA.symm hAB.symm
      have hAH : Disjoint A H := by
        rw [Set.disjoint_left]; intro z hz hzH
        have : z ∈ Hᶜ := hcov ▸ Or.inl hz
        exact this hzH
      have hBH : Disjoint B H := by
        rw [Set.disjoint_left]; intro z hz hzH
        have : z ∈ Hᶜ := hcov ▸ Or.inr hz
        exact this hzH
      refine ⟨H ∪ A, H ∪ B, h1, h2, ?_, ?_, ?_⟩
      · intro h
        obtain ⟨b, hb⟩ := hB
        have : b ∈ H ∪ A := h ▸ mem_univ b
        rcases this with h' | h'
        · exact Set.disjoint_left.mp hBH hb h'
        · exact Set.disjoint_left.mp hAB (subset_closure h') hb
      · intro h
        obtain ⟨a, ha⟩ := hA
        have : a ∈ H ∪ B := h ▸ mem_univ a
        rcases this with h' | h'
        · exact Set.disjoint_left.mp hAH ha h'
        · exact Set.disjoint_left.mp hAB (subset_closure ha) h'
      · refine eq_univ_of_forall fun z => ?_
        by_cases hz : z ∈ H
        · exact Or.inl (Or.inl hz)
        · have : z ∈ A ∪ B := hcov ▸ hz
          rcases this with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')

end Indecomposable

/-! ### The refutation of Theorem 10 as printed: an arc -/

end HPC.Jones
