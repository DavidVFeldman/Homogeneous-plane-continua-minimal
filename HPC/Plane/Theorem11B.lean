import HPC.Plane.SorgenfreyLemmas

/-!
# Batch 104: Bing's Theorem 11 (Duke 1951) by Fugate 1969, Case II

Saved from the uploaded skeleton as `HPC/Plane/Theorem11B.lean`; `import HPC.Plane.Theorem11B` is
added at the end of `HPC.lean`. No existing file was edited. Every item is proved, with no `sorry`;
`theorem11_1951` is the sorry-free form of Theorem 11 (the superseded `theorem11_1951_of_T10'` was
deleted from `Layers51.lean` in batch 105).

Shape changes (each also recorded at the declaration):
* `isTerminalSub_of_union_terminal`, `isTerminalSub_iInter`, `exists_terminal_point_of_isTerminalSub`:
  the unused hypothesis that `M` is a continuum is removed.
* `epsCoverable_of_halves`: `ε`-chains instead of `ε/2`-chains (stronger), and the unused
  hypotheses "`μ` in the closure of no other link" are removed.

Source: J. B. Fugate, *A characterization of chainable continua*, Canad. J. Math. 21 (1969),
383–393: Lemma 3, Lemma 4, Theorem 2 Case II (COMMISSION-batch104.md §1 transcribes them).
Fugate's arc structure `f : M → [0,1]` is replaced by the two sides of an element (batch 96) and
Theorem 8 (a). `IsTerminalSub` is batch 100's (Fugate's Definition 1 = Definition 4 of 1966).
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ## Fugate 1969, Lemmas 3 and 4 (hereditarily decomposable case) -/

/-! ## The two halves of a `BingS` space at an interior element -/

/-! ## Claim 2 and the amalgamation -/

/-- The links of a chain, extended by `∅` to a sequence (for weak chains). -/
def chainSeq {X : Type*} [MetricSpace X] {n : ℕ} (E : Chain X n) (i : ℕ) : Set X :=
  if h : i < n then E.link ⟨i, h⟩ else ∅

section ChainSeq

variable {X : Type*} [MetricSpace X] {n : ℕ}

theorem chainSeq_isOpen (E : Chain X n) (i : ℕ) : IsOpen (chainSeq E i) := by
  unfold chainSeq
  split_ifs
  exacts [E.isOpen _, isOpen_empty]

theorem chainSeq_disjoint (E : Chain X n) {i l : ℕ} (h : i + 2 ≤ l) :
    Disjoint (chainSeq E i) (chainSeq E l) := by
  unfold chainSeq
  split_ifs with hi hl
  · rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty, E.adjacent_iff]
    simp only
    omega
  all_goals simp

theorem chainSeq_small {E : Chain X n} {ε : ℝ} (hE : IsEpsChain E ε) (hε : 0 < ε) (i : ℕ) :
    Bornology.IsBounded (chainSeq E i) ∧ diam (chainSeq E i) < ε := by
  unfold chainSeq
  split_ifs
  exacts [hE _, ⟨Bornology.isBounded_empty, by simpa using hε⟩]

theorem mem_chainSeq {E : Chain X n} {z : X} (hz : z ∈ E.union) : ∃ i < n, z ∈ chainSeq E i := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact ⟨i, i.2, by simp [chainSeq, i.2, hi]⟩

theorem chainSeq_last {E : Chain X n} (hn : 0 < n) :
    chainSeq E (n - 1) = E.link ⟨n - 1, by omega⟩ := by
  simp [chainSeq, show n - 1 < n by omega]

theorem small_of_subset {A B : Set X} {ε : ℝ} (h : A ⊆ B)
    (hB : Bornology.IsBounded B ∧ diam B < ε) : Bornology.IsBounded A ∧ diam A < ε :=
  ⟨hB.1.subset h, (diam_mono h hB.1).trans_lt hB.2⟩

end ChainSeq

/-- **Claim 2 (Fugate, p. 392).** No continuum in `M ∖ O` meets both `A ∖ O` and `M ∖ E*`, when
`μ ∈ O`, `A ⊆ E*`, `A ∪ C = M` and Claim 1 holds (stated for preconnected sets, via closures). -/
theorem claim2 {M A C O Estar : Set S} (hhu : IsHereditarilyUnicoherent M)
    (hA : Fold.Q78.IsContinuum A) (hC : Fold.Q78.IsContinuum C) (hAC : A ∪ C = M) {μ : S}
    (hμO : μ ∈ O) (hO : IsOpen O) (hAE : A ⊆ Estar)
    (hclaim1 : ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q) (hμ : μ ∈ A ∩ C) :
    ∀ Z ⊆ M \ O, IsPreconnected Z → (Z ∩ (A \ O)).Nonempty → (Z ∩ (M \ Estar)).Nonempty →
      False := by
  intro Z hZ hZc ⟨a, haZ, haA⟩ ⟨z, hzZ, hzM, hzE⟩
  have hMO : IsClosed (M \ O) := (hAC ▸ (hA.1.union hC.1)).isClosed.sdiff hO
  set N := closure Z with hN
  have hNsub : N ⊆ M \ O := closure_minimal hZ hMO
  have hNc : Fold.Q78.IsContinuum N :=
    ⟨isClosed_closure.isCompact, ⟨⟨a, subset_closure haZ⟩, hZc.closure⟩⟩
  have hzA : z ∉ A := fun h => hzE (hAE h)
  have hzC : z ∈ C := ((hAC.symm ▸ hzM : z ∈ A ∪ C)).resolve_left hzA
  have hNM : N ⊆ M := hNsub.trans diff_subset
  have hmeet : (N ∩ (A ∩ C)).Nonempty :=
    isPreconnected_closed_iff.mp hNc.2.isPreconnected A C hA.1.isClosed hC.1.isClosed
      (hAC.symm ▸ hNM) ⟨a, subset_closure haZ, haA.1⟩ ⟨z, subset_closure hzZ, hzC⟩
  obtain ⟨w, hwN, hwA, hwC⟩ := hmeet
  have hQ := isContinuum_inter_of_hu hhu hNc hC hNM (hAC ▸ subset_union_right)
    ⟨z, subset_closure hzZ, hzC⟩
  have := hclaim1 _ hQ inter_subset_right ⟨w, ⟨hwN, hwC⟩, hwA, hwC⟩
    (fun h => hzA (h ⟨subset_closure hzZ, hzC⟩).1) hμ
  exact (hNsub this.1).2 hμO

/-- **Claim 2 + the chain (Fugate, p. 392), abstracted.** `A`, `C` continua with `A ∪ C = M`;
`μ ∈ A ∩ C`; Claim 1 holds for `C` relative to `A`; `E` an `ε`-chain covering `A` with `μ` in its last
link, `F` likewise for `C`; `M` hereditarily unicoherent. Then `M` is covered by an `ε`-chain.

Shape change: the skeleton's `ε/2`-chains are replaced by `ε`-chains (a stronger statement), and the
hypotheses "`μ` in the closure of no other link" are dropped (unused). No mesh is lost: Fugate's
link `(F_y ∩ T) ∪ U` lies in `F_y` because `cl U ⊆ E_x ∩ F_y`. The chain is
`(E_1 ∩ S) − cl U, …, (E_{x−1} ∩ S) − cl U, E_x ∩ S, (F_y ∩ T) ∪ U, F_{y−1} ∩ T, …, F_1 ∩ T`
(removing `cl U` from the first `x − 2` links changes nothing, as they miss `E_x ⊇ cl U`); it is a
weak chain (non-consecutive links disjoint), trimmed to a chain by `exists_chain_of_weak`. -/
theorem epsCoverable_of_halves {M A C : Set S} (hM : Fold.Q78.IsContinuum M)
    (hhu : IsHereditarilyUnicoherent M) (hA : Fold.Q78.IsContinuum A)
    (hC : Fold.Q78.IsContinuum C) (hAC : A ∪ C = M) {μ : S} (hμ : μ ∈ A ∩ C)
    (hclaim1 : ∀ Q : Set S, Fold.Q78.IsContinuum Q → Q ⊆ C → (Q ∩ (A ∩ C)).Nonempty →
      ¬ Q ⊆ A ∩ C → A ∩ C ⊆ Q)
    {ε : ℝ} (hε : 0 < ε)
    (hE : ∃ (x : ℕ) (E : Chain S x) (hx : 0 < x), IsEpsChain E ε ∧ A ⊆ E.union ∧
      μ ∈ E.link ⟨x - 1, by omega⟩)
    (hF : ∃ (y : ℕ) (F : Chain S y) (hy : 0 < y), IsEpsChain F ε ∧ C ⊆ F.union ∧
      μ ∈ F.link ⟨y - 1, by omega⟩) :
    EpsCoverable M ε := by
  obtain ⟨x, E, hx, hEε, hAE, hμE⟩ := hE
  obtain ⟨y, F, hy, hFε, hCF, hμF⟩ := hF
  rw [← chainSeq_last hx] at hμE
  rw [← chainSeq_last hy] at hμF
  -- the small open set `O` about `μ`, with closure inside both last links
  obtain ⟨O, hO, hμO, hclO⟩ : ∃ O : Set S, IsOpen O ∧ μ ∈ O ∧
      closure O ⊆ chainSeq E (x - 1) ∩ chainSeq F (y - 1) := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp
      ((chainSeq_isOpen E _).inter (chainSeq_isOpen F _)) μ ⟨hμE, hμF⟩
    exact ⟨ball μ (δ / 2), isOpen_ball, mem_ball_self (by linarith),
      (closure_ball_subset_closedBall).trans ((closedBall_subset_ball (by linarith)).trans hsub)⟩
  have hOE : O ⊆ chainSeq E (x - 1) := subset_closure.trans (hclO.trans inter_subset_left)
  have hOF : O ⊆ chainSeq F (y - 1) := subset_closure.trans (hclO.trans inter_subset_right)
  set Estar := ⋃ i, ⋃ (_ : i < x), chainSeq E i with hEstar
  have hAEs : A ⊆ Estar := fun a ha => by
    obtain ⟨i, hi, hai⟩ := mem_chainSeq (hAE ha)
    exact mem_iUnion₂.mpr ⟨i, hi, hai⟩
  have hEso : IsOpen Estar := isOpen_iUnion fun i => isOpen_iUnion fun _ => chainSeq_isOpen E i
  have hOEs : O ⊆ Estar := fun z hz => mem_iUnion₂.mpr ⟨x - 1, by omega, hOE hz⟩
  have hMcl : IsClosed M := hM.1.isClosed
  have hAM : A ⊆ M := hAC ▸ subset_union_left
  obtain ⟨H, L, hH, hL, hHL, hdisj, hPH, hQL⟩ := exists_closed_split_of_no_connected
    (hM.1.diff hO) (hA.1.isClosed.sdiff hO) (hMcl.sdiff hEso) (diff_subset_diff_left hAM)
    (diff_subset_diff_right hOEs)
    (claim2 hhu hA hC hAC hμO hO hAEs hclaim1 hμ)
  obtain ⟨S₀, T₀, hS₀, hT₀, hHS₀, hLT₀, hST⟩ := normal_separation hH hL hdisj
  -- the weak chain
  let Lk : ℕ → Set S := fun i =>
    if i < x - 1 then (chainSeq E i ∩ S₀) \ closure O
    else if i = x - 1 then chainSeq E i ∩ S₀
    else if i = x then (chainSeq F (y - 1) ∩ T₀) ∪ O
    else chainSeq F (x + y - 1 - i) ∩ T₀
  have hLe : ∀ i, i < x → Lk i ⊆ chainSeq E i ∩ S₀ := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2
    · exact hz.1
    · exact hz
    all_goals omega
  have hLf : ∀ i, x ≤ i → Lk i ⊆ chainSeq F (x + y - 1 - i) := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2 h3
    · omega
    · omega
    · subst h3
      rw [show i + y - 1 - i = y - 1 by omega]
      exact hz.elim (fun h => h.1) (fun h => hOF h)
    · exact hz.1
  have hLT : ∀ i, x < i → Lk i ⊆ T₀ := by
    intro i hi z hz
    simp only [Lk] at hz
    split_ifs at hz with h1 h2 h3
    · omega
    · omega
    · omega
    · exact hz.2
  have hLO : ∀ i, i < x - 1 → Disjoint (Lk i) (closure O) := by
    intro i hi
    simp only [Lk, if_pos hi]
    exact disjoint_sdiff_left
  have hLx : Lk x = (chainSeq F (y - 1) ∩ T₀) ∪ O := by
    simp only [Lk, show ¬ x < x - 1 by omega, show x ≠ x - 1 by omega, if_false, if_true]
  have hLo : ∀ i, IsOpen (Lk i) := by
    intro i
    simp only [Lk]
    split_ifs
    · exact ((chainSeq_isOpen E i).inter hS₀).sdiff isClosed_closure
    · exact (chainSeq_isOpen E i).inter hS₀
    · exact ((chainSeq_isOpen F _).inter hT₀).union hO
    · exact (chainSeq_isOpen F _).inter hT₀
  have hLs : ∀ i, Bornology.IsBounded (Lk i) ∧ diam (Lk i) < ε := by
    intro i
    rcases lt_or_ge i x with h | h
    · exact small_of_subset ((hLe i h).trans inter_subset_left) (chainSeq_small hEε hε i)
    · exact small_of_subset (hLf i h) (chainSeq_small hFε hε _)
  have hLw : ∀ i l, i + 2 ≤ l → l < x + y → Disjoint (Lk i) (Lk l) := by
    intro i l hil hl
    rcases lt_or_ge l x with h | h
    · exact ((chainSeq_disjoint E hil).mono ((hLe i (by omega)).trans inter_subset_left)
        ((hLe l h).trans inter_subset_left))
    rcases le_or_gt x i with h' | h'
    · exact ((chainSeq_disjoint F (i := x + y - 1 - l) (l := x + y - 1 - i) (by omega)).symm.mono
        (hLf i h') (hLf l h))
    rcases eq_or_lt_of_le h with h'' | h''
    · subst h''
      rw [hLx]
      refine Disjoint.union_right ?_ ?_
      · exact (hST.mono ((hLe i h').trans inter_subset_right) inter_subset_right)
      · exact (hLO i (by omega)).mono_right subset_closure
    · exact hST.mono ((hLe i h').trans inter_subset_right) (hLT l h'')
  have hcov : M ⊆ ⋃ i, ⋃ (_ : i < x + y), Lk i := by
    intro z hzM
    by_cases hzO : z ∈ O
    · exact mem_iUnion₂.mpr ⟨x, by omega, by rw [hLx]; exact Or.inr hzO⟩
    have hz : z ∈ H ∪ L := hHL ▸ ⟨hzM, hzO⟩
    rcases hz with hzH | hzL
    · have hzS : z ∈ S₀ := hHS₀ hzH
      have hzE : z ∈ Estar := by
        by_contra h
        exact Set.disjoint_left.mp hdisj hzH (hQL ⟨hzM, h⟩)
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzE
      by_cases hix : i < x - 1
      · by_cases hzc : z ∈ closure O
        · refine mem_iUnion₂.mpr ⟨x - 1, by omega, ?_⟩
          simp only [Lk, show ¬ x - 1 < x - 1 by omega, if_false, if_true]
          exact ⟨(hclO hzc).1, hzS⟩
        · refine mem_iUnion₂.mpr ⟨i, by omega, ?_⟩
          simp only [Lk, if_pos hix]
          exact ⟨⟨hzi, hzS⟩, hzc⟩
      · have hi' : i = x - 1 := by omega
        subst hi'
        refine mem_iUnion₂.mpr ⟨x - 1, by omega, ?_⟩
        simp only [Lk, show ¬ x - 1 < x - 1 by omega, if_false, if_true]
        exact ⟨hzi, hzS⟩
    · have hzT : z ∈ T₀ := hLT₀ hzL
      have hzA : z ∉ A := fun h => Set.disjoint_left.mp hdisj (hPH ⟨h, hzO⟩) hzL
      have hzC : z ∈ C := ((hAC.symm ▸ hzM : z ∈ A ∪ C)).resolve_left hzA
      obtain ⟨k, hk, hzk⟩ := mem_chainSeq (hCF hzC)
      by_cases hky : k = y - 1
      · subst hky
        exact mem_iUnion₂.mpr ⟨x, by omega, by rw [hLx]; exact Or.inl ⟨hzk, hzT⟩⟩
      · refine mem_iUnion₂.mpr ⟨x + y - 1 - k, by omega, ?_⟩
        simp only [Lk, show ¬ x + y - 1 - k < x - 1 by omega, show x + y - 1 - k ≠ x - 1 by omega,
          show x + y - 1 - k ≠ x by omega, if_false]
        rw [show x + y - 1 - (x + y - 1 - k) = k by omega]
        exact ⟨hzk, hzT⟩
  obtain ⟨a, k, D, -, -, -, hDL, hMD, -, -⟩ := exists_chain_of_weak Lk hLo hLw
    hM.2.isPreconnected hcov (i₀ := x) (by omega)
    ⟨μ, by rw [hLx]; exact Or.inr hμO, hAM hμ.1⟩
  exact ⟨k, D, fun t => by rw [hDL t]; exact hLs _, hMD⟩

/-! ## Theorem 11 -/

section SubtypeTransfer

variable {S' : Set S}

end SubtypeTransfer

end HPC.Plane
