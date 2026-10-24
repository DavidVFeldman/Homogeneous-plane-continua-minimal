import HPC.Plane.Atriodic51Defs
import HPC.PseudoArc.Theorem10

/-!
# Batch 96, §1: chain combinatorics for the necessity half of Theorem 11

General facts about `ε`-chains used for Nadler 12.2–12.5 (`HPC/Plane/Theorem11.lean`):

* `exists_link_of_mem_union`, `meets_between`: the links meeting a preconnected set covered by a
  chain have consecutive indices (from `Chain.inter_link_nonempty_between`).
* `chain_ivt`: a discrete intermediate value theorem along a chain of mesh `< ε` for a
  `1`-Lipschitz function.
* `chain_two_sets`: two sets meeting every link between the links `i` and `j` contain points `y`,
  `z` in a common link with `f y` within `ε` of a prescribed level.
* `isPreconnected_union_of_separated`: Nadler 6.3 for a subset (if `T = N ∪ A ∪ R` is preconnected,
  `N` is preconnected and nonempty, and `A`, `R` are separated, then `N ∪ A` is preconnected).
* `exists_pos_le_dist`: disjoint compact and closed sets are at positive distance.
-/

namespace HPC.Plane

open Set Topology Metric

section Chains

variable {X : Type*} [MetricSpace X]

theorem IsEpsChain.dist_lt {n : ℕ} {D : Chain X n} {ε : ℝ} (hD : IsEpsChain D ε) {i : Fin n}
    {x y : X} (hx : x ∈ D.link i) (hy : y ∈ D.link i) : dist x y < ε :=
  lt_of_le_of_lt (Metric.dist_le_diam_of_mem (hD i).1 hx hy) (hD i).2

theorem exists_link_of_mem_union {n : ℕ} {D : Chain X n} {x : X} (h : x ∈ D.union) :
    ∃ i, x ∈ D.link i := by
  simpa [Chain.union] using h

/-- The links meeting a preconnected set covered by a chain have consecutive indices. -/
theorem meets_between {n : ℕ} (D : Chain X n) {C : Set X} (hC : IsPreconnected C)
    (hCD : C ⊆ D.union) {i j : Fin n} (hi : (C ∩ D.link i).Nonempty)
    (hj : (C ∩ D.link j).Nonempty) :
    ∀ l : Fin n, min i.val j.val ≤ l.val → l.val ≤ max i.val j.val → (C ∩ D.link l).Nonempty := by
  intro l h1 h2
  by_cases hli : l = i
  · exact hli ▸ hi
  by_cases hlj : l = j
  · exact hlj ▸ hj
  have hli' : l.val ≠ i.val := fun e => hli (Fin.ext e)
  have hlj' : l.val ≠ j.val := fun e => hlj (Fin.ext e)
  rcases le_total i.val j.val with h | h
  · exact D.inter_link_nonempty_between hC hCD (a := i) (b := l) (c := j)
      (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega)) hi hj
  · exact D.inter_link_nonempty_between hC hCD (a := j) (b := l) (c := i)
      (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega)) hj hi

/-- The discrete intermediate value theorem along a chain, increasing direction. -/
theorem chain_ivt_aux {n : ℕ} (D : Chain X n) {ε : ℝ} (hD : IsEpsChain D ε) (f : X → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ dist x y) (Y : Set X) (c : ℝ) :
    ∀ k i (hik : i + k < n),
      (∀ l (hl : l < n), i ≤ l → l ≤ i + k → (Y ∩ D.link ⟨l, hl⟩).Nonempty) →
      (∃ x ∈ D.link ⟨i, by omega⟩, f x ≤ c) → (∃ x ∈ D.link ⟨i + k, hik⟩, c ≤ f x) →
      ∃ l, ∃ hl : l < n, i ≤ l ∧ l ≤ i + k ∧ ∃ y ∈ Y ∩ D.link ⟨l, hl⟩, |f y - c| < ε := by
  intro k
  induction k with
  | zero =>
    intro i hik hY hs he
    obtain ⟨x, hx, hfx⟩ := hs
    obtain ⟨x', hx', hfx'⟩ := he
    obtain ⟨y, hyY, hy⟩ := hY i (by omega) le_rfl (by omega)
    refine ⟨i, by omega, le_rfl, by omega, y, ⟨hyY, hy⟩, ?_⟩
    have hx'' : x' ∈ D.link ⟨i, by omega⟩ := by simpa using hx'
    have d1 := hD.dist_lt hy hx
    have d2 := hD.dist_lt hy hx''
    have e1 := hf y x
    have e2 := hf y x'
    rw [abs_le] at e1 e2
    rw [abs_lt]
    constructor <;> linarith
  | succ k ih =>
    intro i hik hY hs he
    by_cases h : ∃ x ∈ D.link ⟨i + 1, by omega⟩, f x ≤ c
    · have he' : ∃ x ∈ D.link ⟨i + 1 + k, by omega⟩, c ≤ f x := by
        have : (⟨i + 1 + k, by omega⟩ : Fin n) = ⟨i + (k + 1), hik⟩ := Fin.ext (by simp; omega)
        rw [this]; exact he
      obtain ⟨l, hl, h1, h2, hy⟩ := ih (i + 1) (by omega)
        (fun l hl h1 h2 => hY l hl (by omega) (by omega)) h he'
      exact ⟨l, hl, by omega, by omega, hy⟩
    · push_neg at h
      obtain ⟨x, hx, hfx⟩ := hs
      obtain ⟨w, hw0, hw1⟩ := (D.adjacent_iff ⟨i, by omega⟩ ⟨i + 1, by omega⟩).mpr
        (by simp only; omega)
      obtain ⟨y, hyY, hy⟩ := hY i (by omega) le_rfl (by omega)
      refine ⟨i, by omega, le_rfl, by omega, y, ⟨hyY, hy⟩, ?_⟩
      have hfw := h w hw1
      have d1 := hD.dist_lt hy hx
      have d2 := hD.dist_lt hy hw0
      have e1 := hf y x
      have e2 := hf y w
      rw [abs_le] at e1 e2
      rw [abs_lt]
      constructor <;> linarith

/-- **Discrete intermediate value theorem along a chain.** If `f` is `1`-Lipschitz, `Y` meets
every link with index between `i` and `j`, the link `i` has a point with `f ≤ c` and the link `j`
a point with `f ≥ c`, then some link between has a point `y ∈ Y` with `|f y - c| < ε`. -/
theorem chain_ivt {n : ℕ} (D : Chain X n) {ε : ℝ} (hD : IsEpsChain D ε) (f : X → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ dist x y) (Y : Set X) (c : ℝ) {i j : Fin n}
    (hY : ∀ l : Fin n, min i.val j.val ≤ l.val → l.val ≤ max i.val j.val → (Y ∩ D.link l).Nonempty)
    (hi : ∃ x ∈ D.link i, f x ≤ c) (hj : ∃ x ∈ D.link j, c ≤ f x) :
    ∃ l : Fin n, min i.val j.val ≤ l.val ∧ l.val ≤ max i.val j.val ∧
      ∃ y ∈ Y ∩ D.link l, |f y - c| < ε := by
  rcases le_total i.val j.val with h | h
  · have hj' : ∃ x ∈ D.link ⟨i.val + (j.val - i.val), by omega⟩, c ≤ f x := by
      have : (⟨i.val + (j.val - i.val), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
      rw [this]; exact hj
    obtain ⟨l, hl, h1, h2, hy⟩ := chain_ivt_aux D hD f hf Y c (j.val - i.val) i.val (by omega)
      (fun l hl h1 h2 => hY ⟨l, hl⟩ (by simp only; omega) (by simp only; omega)) hi hj'
    exact ⟨⟨l, hl⟩, by simp only; omega, by simp only; omega, hy⟩
  · have hf' : ∀ x y, |(-f x) - (-f y)| ≤ dist x y := fun x y => by
      rw [show (-f x) - (-f y) = -(f x - f y) by ring, abs_neg]; exact hf x y
    have hi' : ∃ x ∈ D.link ⟨j.val + (i.val - j.val), by omega⟩, -c ≤ -f x := by
      have : (⟨j.val + (i.val - j.val), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      rw [this]
      obtain ⟨x, hx, hfx⟩ := hi
      exact ⟨x, hx, by linarith⟩
    have hj' : ∃ x ∈ D.link ⟨j.val, by omega⟩, -f x ≤ -c := by
      obtain ⟨x, hx, hfx⟩ := hj
      exact ⟨x, hx, by linarith⟩
    obtain ⟨l, hl, h1, h2, y, hy, hfy⟩ := chain_ivt_aux D hD (fun x => -f x) hf' Y (-c)
      (i.val - j.val) j.val (by omega)
      (fun l hl h1 h2 => hY ⟨l, hl⟩ (by simp only; omega) (by simp only; omega)) hj' hi'
    refine ⟨⟨l, hl⟩, by simp only; omega, by simp only; omega, y, hy, ?_⟩
    rw [show -f y - -c = -(f y - c) by ring, abs_neg] at hfy
    exact hfy

/-- **Two sets crossing the same stretch of a chain** contain points `y`, `z` in a common link
(so `dist y z < ε`) with `f y` within `ε` of the level `c`. -/
theorem chain_two_sets {n : ℕ} (D : Chain X n) {ε : ℝ} (hD : IsEpsChain D ε) (f : X → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ dist x y) {Y Z : Set X} (c : ℝ) {i j : Fin n}
    (hY : ∀ l : Fin n, min i.val j.val ≤ l.val → l.val ≤ max i.val j.val → (Y ∩ D.link l).Nonempty)
    (hZ : ∀ l : Fin n, min i.val j.val ≤ l.val → l.val ≤ max i.val j.val → (Z ∩ D.link l).Nonempty)
    (hi : ∃ x ∈ D.link i, f x ≤ c) (hj : ∃ x ∈ D.link j, c ≤ f x) :
    ∃ y ∈ Y, ∃ z ∈ Z, |f y - c| < ε ∧ dist y z < ε := by
  obtain ⟨l, h1, h2, y, ⟨hyY, hyl⟩, hfy⟩ := chain_ivt D hD f hf Y c hY hi hj
  obtain ⟨z, hzZ, hzl⟩ := hZ l h1 h2
  exact ⟨y, hyY, z, hzZ, hfy, hD.dist_lt hyl hzl⟩

/-- `infDist · s` is `1`-Lipschitz, in the form used here. -/
theorem abs_infDist_sub_le (s : Set X) (x y : X) : |infDist x s - infDist y s| ≤ dist x y := by
  rw [abs_le]
  have h1 := infDist_le_infDist_add_dist (x := x) (y := y) (s := s)
  have h2 := infDist_le_infDist_add_dist (x := y) (y := x) (s := s)
  rw [dist_comm] at h2
  constructor <;> linarith

/-- Disjoint compact and closed sets are at positive distance. -/
theorem exists_pos_le_dist {A B : Set X} (hA : IsCompact A) (hB : IsClosed B)
    (h : Disjoint A B) : ∃ η > 0, ∀ a ∈ A, ∀ b ∈ B, η ≤ dist a b := by
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · exact ⟨1, one_pos, fun a _ b hb => by rw [hBe] at hb; exact hb.elim⟩
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨1, one_pos, fun a ha => by rw [hAe] at ha; exact ha.elim⟩
  obtain ⟨a₀, ha₀, hmin⟩ := hA.exists_isMinOn hAne (continuous_infDist_pt B).continuousOn
  have hpos : 0 < infDist a₀ B := (infDist_pos_iff_notMem_closure hBne).mp (by
    rw [hB.closure_eq]; exact Set.disjoint_left.mp h ha₀)
  refine ⟨infDist a₀ B, hpos, fun a ha b hb => ?_⟩
  exact (hmin ha).trans (infDist_le_dist_of_mem hb)

/-- **Nadler 6.3 for a subset.** If `T = N ∪ A ∪ R` is preconnected, `N` is preconnected and
nonempty, and `A`, `R` are separated, then `N ∪ A` is preconnected. -/
theorem isPreconnected_union_of_separated {T N A R : Set X} (hT : IsPreconnected T)
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hTdec : T = N ∪ A ∪ R)
    (h1 : Disjoint (closure A) R) (h2 : Disjoint A (closure R)) : IsPreconnected (N ∪ A) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  have aux : ∀ u v : Set X, IsOpen u → IsOpen v → N ∪ A ⊆ u ∪ v → (N ∪ A) ∩ (u ∩ v) = ∅ →
      N ⊆ u → N ∪ A ⊆ u := by
    intro u v hu hv hsub hdisj hNu
    have hno : ∀ x, x ∈ N ∪ A → x ∈ u → x ∈ v → False := fun x hx hxu hxv => by
      have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨hx, hxu, hxv⟩
      rw [hdisj] at this; exact this
    set O₁ := v ∩ (closure R)ᶜ
    set O₂ := u ∪ (closure A)ᶜ
    have hO₁ : IsOpen O₁ := hv.inter isClosed_closure.isOpen_compl
    have hO₂ : IsOpen O₂ := hu.union isClosed_closure.isOpen_compl
    have hcov : T ⊆ O₁ ∪ O₂ := by
      intro x hx
      rw [hTdec] at hx
      rcases hx with (hxN | hxA) | hxR
      · exact Or.inr (Or.inl (hNu hxN))
      · rcases hsub (Or.inr hxA) with hxu | hxv
        · exact Or.inr (Or.inl hxu)
        · exact Or.inl ⟨hxv, fun hc => Set.disjoint_left.mp h2 hxA hc⟩
      · exact Or.inr (Or.inr fun hc => Set.disjoint_left.mp h1 hc hxR)
    have hemp : T ∩ (O₁ ∩ O₂) = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hx ⟨hxv, hxR⟩ hx2
      rw [hTdec] at hx
      rcases hx with (hxN | hxA) | hxR'
      · exact hno x (Or.inl hxN) (hNu hxN) hxv
      · rcases hx2 with hxu | hxA'
        · exact hno x (Or.inr hxA) hxu hxv
        · exact hxA' (subset_closure hxA)
      · exact hxR (subset_closure hxR')
    rcases (isPreconnected_iff_subset_of_disjoint.mp hT) O₁ O₂ hO₁ hO₂ hcov hemp with h | h
    · exfalso
      obtain ⟨x, hx⟩ := hNne
      have hxT : x ∈ T := by rw [hTdec]; exact Or.inl (Or.inl hx)
      exact hno x (Or.inl hx) (hNu hx) (h hxT).1
    · intro x hx
      rcases hsub hx with hxu | hxv
      · exact hxu
      · exfalso
        rcases hx with hxN | hxA
        · exact hno x (Or.inl hxN) (hNu hxN) hxv
        · have hxT : x ∈ T := by rw [hTdec]; exact Or.inl (Or.inr hxA)
          have : x ∈ T ∩ (O₁ ∩ O₂) := ⟨hxT, ⟨hxv, fun hc => Set.disjoint_left.mp h2 hxA hc⟩, h hxT⟩
          rw [hemp] at this; exact this
  intro u v hu hv hsub hdisj
  rcases (isPreconnected_iff_subset_of_disjoint.mp hN) u v hu hv (subset_union_left.trans hsub)
    (by rw [← subset_empty_iff, ← hdisj]; exact inter_subset_inter_left _ subset_union_left)
    with h | h
  · exact Or.inl (aux u v hu hv hsub hdisj h)
  · exact Or.inr (aux v u hv hu (fun x hx => (hsub hx).symm)
      (by rw [inter_comm v u]; exact hdisj) h)

end Chains

/-! ## Necessity (Nadler 12.2–12.5) -/

section Necessity

/-- **Nadler 12.5.** A subcontinuum of a snake-like continuum is snake-like: the links of an
`ε`-chain covering `M` that meet `K` have consecutive indices (`meets_between`), so they form a
subchain covering `K`. -/
theorem isSnakeLike_of_subcontinuum_aux {X : Type*} [MetricSpace X] {M K : Set X}
    (hM : IsSnakeLike M) (hK : Fold.Q78.IsContinuum K) (hKM : K ⊆ M) : IsSnakeLike K := by
  classical
  refine ⟨hK, fun ε hε => ?_⟩
  obtain ⟨n, D, hD, hMD⟩ := hM.2 ε hε
  have hKD : K ⊆ D.union := hKM.trans hMD
  set I := Finset.univ.filter (fun i : Fin n => (K ∩ D.link i).Nonempty) with hI
  obtain ⟨x, hx⟩ := hK.2.nonempty
  obtain ⟨i0, hi0⟩ := exists_link_of_mem_union (hKD hx)
  have hIne : I.Nonempty := ⟨i0, by simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x, hx, hi0⟩⟩
  have hab : I.min' hIne ≤ I.max' hIne := Finset.min'_le_max' I hIne
  refine ⟨(I.max' hIne).val - (I.min' hIne).val + 1, D.sub _ _ hab, fun t => hD _, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := exists_link_of_mem_union (hKD hy)
  have htI : t ∈ I := by
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨y, hy, ht⟩
  have h1 := Fin.le_def.mp (Finset.min'_le I t htI)
  have h2 := Fin.le_def.mp (Finset.le_max' I t htI)
  simp only [Chain.union, mem_iUnion]
  refine ⟨⟨t.val - (I.min' hIne).val, by omega⟩, ?_⟩
  simp only [Chain.sub]
  convert ht using 2
  ext
  simp only
  omega

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Nadler 12.2.** A snake-like continuum is unicoherent. If `M = H ∪ K` and `H ∩ K = P ⊔ Q`
with `P`, `Q` closed, let `δ` be the distance from `Q` to `P` and `f = dist(·, P)`; the parts of
`H` and `K` in the band `δ/4 ≤ f ≤ 3δ/4` are disjoint compact sets, at distance `η > 0`. In an
`ε`-chain, `ε = min η (δ/8)`, both `H` and `K` cross every link between a link through `P` and a
link through `Q`; `chain_two_sets` gives `y ∈ H`, `z ∈ K` in one link inside the band, so
`η ≤ dist y z < ε`. -/
theorem isUnicoherent_of_isSnakeLike_aux {M : Set S} (hM : IsSnakeLike M) : IsUnicoherent M := by
  intro H K hH hK hHK
  have hHM : H ⊆ M := hHK ▸ subset_union_left
  have hKM : K ⊆ M := hHK ▸ subset_union_right
  have hne : (H ∩ K).Nonempty := by
    obtain ⟨x, hx⟩ := hH.2.nonempty
    obtain ⟨y, hy⟩ := hK.2.nonempty
    have := (isPreconnected_closed_iff.mp hM.1.2.isPreconnected) H K hH.1.isClosed
      hK.1.isClosed hHK.ge ⟨x, hHM hx, hx⟩ ⟨y, hKM hy, hy⟩
    exact this.mono inter_subset_right
  refine ⟨hne, ?_⟩
  by_contra hnc
  rw [isPreconnected_closed_iff] at hnc
  push_neg at hnc
  obtain ⟨t, t', ht, ht', hcov, ⟨p, hpHK, hpt⟩, ⟨q, hqHK, hqt'⟩, hemp⟩ := hnc
  have hHKc : IsClosed (H ∩ K) := hH.1.isClosed.inter hK.1.isClosed
  set P := H ∩ K ∩ t with hP
  set Q := H ∩ K ∩ t' with hQ
  have hPc : IsClosed P := hHKc.inter ht
  have hQc : IsClosed Q := hHKc.inter ht'
  have hdisj : Disjoint Q P := by
    rw [Set.disjoint_left]
    intro x hxQ hxP
    have : x ∈ H ∩ K ∩ (t ∩ t') := ⟨hxQ.1, hxP.2, hxQ.2⟩
    rw [hemp] at this; exact this
  have hpP : p ∈ P := ⟨hpHK, hpt⟩
  have hqQ : q ∈ Q := ⟨hqHK, hqt'⟩
  obtain ⟨δ, hδ, hδQ⟩ := exists_pos_le_dist hQc.isCompact hPc hdisj
  set f : S → ℝ := fun x => infDist x P with hf
  have hfP : ∀ x ∈ P, f x = 0 := fun x hx => infDist_zero_of_mem hx
  have hfQ : ∀ x ∈ Q, δ ≤ f x := fun x hx => (le_infDist ⟨p, hpP⟩).mpr fun y hy => hδQ x hx y hy
  set Y' := {x : S | δ / 4 ≤ f x ∧ f x ≤ 3 * δ / 4} with hY'
  have hY'c : IsClosed Y' :=
    (isClosed_le continuous_const (continuous_infDist_pt P)).inter
      (isClosed_le (continuous_infDist_pt P) continuous_const)
  have hdisj' : Disjoint (H ∩ Y') (K ∩ Y') := by
    rw [Set.disjoint_left]
    rintro x ⟨hxH, hx1, hx2⟩ ⟨hxK, -, -⟩
    rcases hcov ⟨hxH, hxK⟩ with hxt | hxt'
    · have := hfP x ⟨⟨hxH, hxK⟩, hxt⟩; linarith
    · have := hfQ x ⟨⟨hxH, hxK⟩, hxt'⟩; linarith
  obtain ⟨η, hη, hηd⟩ := exists_pos_le_dist (hH.1.isClosed.inter hY'c).isCompact
    (hK.1.isClosed.inter hY'c) hdisj'
  set ε := min η (δ / 8) with hε
  have hεpos : 0 < ε := lt_min hη (by linarith)
  have hεη : ε ≤ η := min_le_left _ _
  have hεδ : ε ≤ δ / 8 := min_le_right _ _
  obtain ⟨n, D, hD, hMD⟩ := hM.2 ε hεpos
  obtain ⟨i, hi⟩ := exists_link_of_mem_union (hMD (hHM hpHK.1))
  obtain ⟨j, hj⟩ := exists_link_of_mem_union (hMD (hHM hqHK.1))
  have hYH := meets_between D hH.2.isPreconnected (hHM.trans hMD) ⟨p, hpHK.1, hi⟩ ⟨q, hqHK.1, hj⟩
  have hYK := meets_between D hK.2.isPreconnected (hKM.trans hMD) ⟨p, hpHK.2, hi⟩ ⟨q, hqHK.2, hj⟩
  obtain ⟨y, hyH, z, hzK, hfy, hyz⟩ := chain_two_sets D hD f (abs_infDist_sub_le P) (δ / 2)
    hYH hYK ⟨p, hi, by rw [hfP p hpP]; linarith⟩ ⟨q, hj, by have := hfQ q hqQ; linarith⟩
  have hfz := abs_infDist_sub_le P z y
  rw [dist_comm] at hfz
  rw [abs_lt] at hfy
  rw [abs_le] at hfz
  have := hηd y ⟨hyH, by simp only [hY', mem_setOf_eq]; constructor <;> linarith⟩ z
    ⟨hzK, by simp only [hY', mem_setOf_eq]; constructor <;> linarith⟩
  linarith

end Necessity

end HPC.Plane
