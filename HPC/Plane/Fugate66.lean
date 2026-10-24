import HPC.Plane.LastLink99

/-!
# Batch 100: Fugate 1966 — terminal subcontinua, Lemma 1 in general, Lemma 3, Theorem 1 (gluing),
# Corollaries 1–2

Source: J. B. Fugate, *Decomposable chainable continua*, Trans. Amer. Math. Soc. 123 (1966),
460–468. Definitions 3–5, Lemmas 1–4, Theorem 1, Corollaries 1–2 (COMMISSION-batch100.md §1
transcribes them). `IsAtriodic`, `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsTriod` are
batch 92's (Bing's definitions, over a compact metric space `S`).

Status of the items and the shape changes are recorded in `REPORT-batch100.md`.
-/

namespace HPC.Plane

open Set Topology Metric

variable {S : Type*} [MetricSpace S]

/-! ## Definitions -/

/-- **Fugate, Definition 4.** `A` is a *terminal subcontinuum* of `M`: for subcontinua `K`, `L` of
`M` both meeting `A`, `K ⊆ A ∪ L` or `L ⊆ K ∪ A`. (Degenerate `A = {p}`: Bing's condition B.) -/
def IsTerminalSub (M A : Set S) : Prop :=
  Fold.Q78.IsContinuum A ∧ A ⊆ M ∧
    ∀ K L : Set S, Fold.Q78.IsContinuum K → Fold.Q78.IsContinuum L → K ⊆ M → L ⊆ M →
      (K ∩ A).Nonempty → (L ∩ A).Nonempty → K ⊆ A ∪ L ∨ L ⊆ K ∪ A

theorem isContinuum_singleton' (p : S) : Fold.Q78.IsContinuum ({p} : Set S) :=
  ⟨isCompact_singleton, isConnected_singleton⟩

/-- **Definition 4 at a point is condition B.** Shape change: the skeleton's hypothesis that `M`
is a continuum is not used and has been removed. -/
theorem isTerminalSub_singleton_iff (M : Set S) (p : S) :
    IsTerminalSub M {p} ↔ CondB M p := by
  constructor
  · rintro ⟨-, hpM, hT⟩
    refine ⟨singleton_subset_iff.mp hpM, fun H K hHM hKM hH hK hpH hpK => ?_⟩
    rcases hT H K hH hK hHM hKM ⟨p, hpH, rfl⟩ ⟨p, hpK, rfl⟩ with h | h
    · exact Or.inl fun x hx => (h hx).elim (fun e => (mem_singleton_iff.mp e) ▸ hpK) id
    · exact Or.inr fun x hx => (h hx).elim id (fun e => (mem_singleton_iff.mp e) ▸ hpH)
  · rintro ⟨hpM, hB⟩
    refine ⟨isContinuum_singleton' p, singleton_subset_iff.mpr hpM,
      fun K L hK hL hKM hLM hKA hLA => ?_⟩
    obtain ⟨_, hpK, rfl⟩ := hKA
    obtain ⟨_, hpL, hpL'⟩ := hLA
    rw [mem_singleton_iff] at hpL'
    subst hpL'
    rcases hB K L hKM hLM hK hL hpK hpL with h | h
    · exact Or.inl (h.trans subset_union_right)
    · exact Or.inr (h.trans subset_union_left)

/-! ## Triods -/

/-- **A piece of the complement of a subcontinuum, with the subcontinuum, is connected** (a
special case of boundary bumping). `M` connected and closed, `N ⊆ M` connected, nonempty and
closed, `M ∖ N = A ∪ R` with `A`, `R` separated: then `N ∪ A` is preconnected. -/
theorem isPreconnected_union_piece {M N A R : Set S} (hM : IsPreconnected M) (hMc : IsClosed M)
    (hN : IsPreconnected N) (hNc : IsClosed N) (hNne : N.Nonempty) (hNM : N ⊆ M) (hcov : M \ N = A ∪ R)
    (hAR : Disjoint (closure A) R) (hRA : Disjoint A (closure R)) : IsPreconnected (N ∪ A) := by
  have hAM : A ⊆ M := fun x hx => (hcov.symm ▸ (Or.inl hx : x ∈ A ∪ R) : x ∈ M \ N).1
  have hMsplit : ∀ x ∈ M, x ∈ N ∨ x ∈ A ∨ x ∈ R := fun x hx => by
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · have : x ∈ A ∪ R := hcov ▸ ⟨hx, hxN⟩
      exact Or.inr this
  -- the key step, for one orientation
  have key : ∀ u v : Set S, IsClosed u → IsClosed v → N ∪ A ⊆ u ∪ v → (N ∪ A) ∩ (u ∩ v) = ∅ →
      N ⊆ u → N ∪ A ⊆ u := by
    intro u v hu hv hcuv hdisj hNu
    have hNv : ∀ x ∈ N, x ∉ v := fun x hx hxv => by
      have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inl hx, hNu hx, hxv⟩
      rw [hdisj] at this; exact this
    have hclA : closure A ⊆ N ∪ A := fun x hx => by
      have hxM : x ∈ M := closure_minimal hAM hMc hx
      rcases hMsplit x hxM with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (Set.disjoint_left.mp hAR hx)
    have hNAc : IsClosed (N ∪ A) := by
      have : N ∪ A = N ∪ closure A :=
        Subset.antisymm (union_subset_union_right _ subset_closure)
          (union_subset subset_union_left hclA)
      rw [this]; exact hNc.union isClosed_closure
    have hAv : ∀ x ∈ A, x ∉ v := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hM ((N ∪ A) ∩ v)
        (((N ∪ A) ∩ u) ∪ closure R) (hNAc.inter hv) ((hNAc.inter hu).union isClosed_closure)
        (fun x hx => by
          rcases hMsplit x hx with h | h | h
          · exact Or.inr (Or.inl ⟨Or.inl h, hNu h⟩)
          · rcases hcuv (Or.inr h : x ∈ N ∪ A) with h' | h'
            · exact Or.inr (Or.inl ⟨Or.inr h, h'⟩)
            · exact Or.inl ⟨Or.inr h, h'⟩
          · exact Or.inr (Or.inr (subset_closure h)))
        (by
          rw [eq_empty_iff_forall_notMem]
          rintro x ⟨-, ⟨hxNA, hxv⟩, hx2⟩
          rcases hx2 with ⟨-, hxu⟩ | hxR
          · have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨hxNA, hxu, hxv⟩
            rw [hdisj] at this; exact this
          · rcases hxNA with hxN | hxA
            · exact hNv x hxN hxv
            · exact Set.disjoint_left.mp hRA hxA hxR) with h | h
      · obtain ⟨y, hy⟩ := hNne
        exact absurd (h (hNM hy)).2 (hNv y hy)
      · intro x hxA hxv
        rcases h (hAM hxA) with ⟨-, hxu⟩ | hxR
        · have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inr hxA, hxu, hxv⟩
          rw [hdisj] at this; exact this
        · exact Set.disjoint_left.mp hRA hxA hxR
    intro x hx
    rcases hx with hxN | hxA
    · exact hNu hxN
    · exact (hcuv (Or.inr hxA)).resolve_right (hAv x hxA)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hcuv hdisj
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hN u v hu hv
    (subset_union_left.trans hcuv) (by
      rw [eq_empty_iff_forall_notMem]; intro x hx
      have : x ∈ (N ∪ A) ∩ (u ∩ v) := ⟨Or.inl hx.1, hx.2⟩
      rw [hdisj] at this; exact this) with h | h
  · exact Or.inl (key u v hu hv hcuv hdisj h)
  · exact Or.inr (key v u hv hu (by rwa [union_comm v u]) (by rwa [inter_comm v u]) h)

/-- In a hereditarily unicoherent continuum two intersecting subcontinua meet in a continuum. -/
theorem isContinuum_inter_of_hu {T H K : Set S} (hT : IsHereditarilyUnicoherent T)
    (hH : Fold.Q78.IsContinuum H) (hK : Fold.Q78.IsContinuum K) (hHT : H ⊆ T) (hKT : K ⊆ T)
    (hne : (H ∩ K).Nonempty) : Fold.Q78.IsContinuum (H ∩ K) := by
  refine ⟨hH.1.inter_right hK.1.isClosed, ?_⟩
  by_cases hnt : (H ∪ K).Nontrivial
  · exact hT (H ∪ K) (union_subset hHT hKT) (isContinuum_union hH hK hne) hnt H K hH hK rfl
  · rw [Set.not_nontrivial_iff] at hnt
    exact ⟨hne, (hnt.anti (inter_subset_left.trans subset_union_left)).isPreconnected⟩

-- Commented-out statement `isFugateTriod_iff_isTriod` removed in batch 103; see `LEDGER.md`.

-- Commented-out statement `isTriod_union_of_three` removed in batch 103; see `LEDGER.md`.

/-! ## Lemma 3 -/

variable [CompactSpace S]

-- `exists_irreducibleBetween_of_atriodic` and `isTerminalSub_iff_irreducible` (Fugate's Lemma 3):
-- proved in `HPC/Plane/Sorgenfrey.lean` (batch 103: the sorried versions were deleted here).

/-! ## Lemma 1 (general) and Lemma 2 -/

/-! **Fugate, Lemma 1** (`fugate_lemma1`) is proved in `HPC/Plane/Fugate66Lemma1.lean`, which
imports this file. -/

/-! **Fugate, Lemma 2** (`fugate_lemma2`) is proved in `HPC/Plane/Fugate66Lemma1.lean`. -/

/-! ## Theorem 1 and its corollaries -/

-- `fugate_theorem1_sufficiency` and `fugate_theorem1` (Fugate's Theorem 1): proved in
-- `HPC/Plane/Fugate66B.lean` (batch 103: the sorried versions were deleted here).

-- `fugate_cor1` (Fugate's Corollary 1): proved in `HPC/Plane/Ingram68.lean` (batch 132).

-- `fugate_cor2` (Fugate's Corollary 2): proved in `HPC/Plane/Fugate66B.lean` (batch 103: the sorried
-- version was deleted here).

/-! ## Tautness (Fugate §2, Barrett) -/

end HPC.Plane
