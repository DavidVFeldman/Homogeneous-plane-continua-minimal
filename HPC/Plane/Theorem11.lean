import HPC.Plane.Atriodic51BNine
import HPC.Plane.Atriodic51Defs
import HPC.Plane.NonCut51Gen
import HPC.Plane.Theorem11Gen

/-!
# Batch 96: Bing 1951 Theorem 11 — the easy half, and reconnaissance on the hard half

Skeleton of `COMMISSION-batch96.md`, saved as `HPC/Plane/Theorem11.lean` and imported at the end of
the root `HPC.lean`.

Theorem 11 (p. 660): *necessary and sufficient conditions that a compact hereditarily decomposable
continuum be snake-like are that it be atriodic and hereditarily unicoherent.*

§1 is the necessity ("it is easy to see"). §2 sets up Bing's minimal counterexample and the
structure his proof of sufficiency needs; §3 is sufficiency, conditional on `theorem10_1951`.

**Status (batch 96).**
* §1: all four statements proved (chain combinatorics in `HPC/Plane/Theorem11Nec.lean`).
* `not_separation_of_accumulates` (item 1) is **false as stated** (an open `N` may avoid a point of
  `g` without avoiding a neighbourhood of it): refuted by `not_separation_of_accumulates_false`
  (the commented-out statement was removed in batch 103; see `LEDGER.md`); the corrected statement, with `¬ g ⊆ closure N`, is
  `not_separation_of_accumulates'`, proved.
* Items 2, 4, 5, 7, 8 proved (`separation_of_degenerate`, `exists_two_sides`, `sides_continua`,
  `condA_side`, `epsCoverable_amalgam`, `exists_minimal_notCoverable`).
* Item 3 (`exists_degenerate_interior_elt`) is **false** (batch 97: refuted by
  `exists_degenerate_interior_elt_refuted`, `HPC/Plane/Layers51.lean`, in the Cantor organ); the
  sorried statement was removed in batch 103 (see `LEDGER.md`).
* `theorem11_1951_of_T10` and `theorem11_1951_iff_of_T10` are proved with the statement of
  `exists_degenerate_interior_elt` as a further hypothesis `hdeg` (shape change).

**Shape changes.**
* §1: `IsUnicoherent`, `IsHereditarilyUnicoherent`, `IsAtriodic` and `IsTriod` are defined only
  over a compact metric space (`Atriodic51Defs.lean`), so the last three statements of §1 are
  stated over `S` (compact) instead of `X`. `isSnakeLike_of_subcontinuum` stays over `X`.
* `EpsCoverable` is defined in `HPC/Plane/Theorem11Gen.lean` (same definition), so that the
  general lemmas there can use it.
* `exists_minimal_notCoverable` is stated over the compact space `S` (the Brouwer reduction used,
  `exists_minimal_of_seq`, needs second countability); the general form is unchanged otherwise.
* `theorem11_1951_of_T10`, `theorem11_1951_iff_of_T10`: extra hypothesis `hdeg`.
-/

namespace HPC.Plane

open Set Topology Metric

universe u

variable {X : Type*} [MetricSpace X]

/-! ## §1. Necessity: snake-like ⇒ atriodic and hereditarily unicoherent (Nadler 12.2–12.5) -/

/-- A subcontinuum of a snake-like continuum is snake-like (Nadler 12.5; Bing uses it without
comment). The links meeting `K` have consecutive indices (`meets_between`, from
`Chain.inter_link_nonempty_between`), so they form a subchain covering `K`. -/
theorem isSnakeLike_of_subcontinuum {M K : Set X} (hM : IsSnakeLike M) (hK : Fold.Q78.IsContinuum K)
    (hKM : K ⊆ M) : IsSnakeLike K :=
  isSnakeLike_of_subcontinuum_aux hM hK hKM

section CompactNecessity

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A snake-like continuum is unicoherent (Nadler 12.2). (Shape change: over a compact space.) -/
theorem isUnicoherent_of_isSnakeLike {M : Set S} (hM : IsSnakeLike M) : IsUnicoherent M :=
  isUnicoherent_of_isSnakeLike_aux hM

/-- A snake-like continuum is hereditarily unicoherent. (Shape change: over a compact space.) -/
theorem isHereditarilyUnicoherent_of_isSnakeLike {M : Set S} (hM : IsSnakeLike M) :
    IsHereditarilyUnicoherent M := fun _ hKM hK _ =>
  isUnicoherent_of_isSnakeLike (isSnakeLike_of_subcontinuum hM hK hKM)

end CompactNecessity

/-! ## §2. The hard half: structure -/

section Structure

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! `EpsCoverable` (`M` is covered by some `ε`-chain) is defined in `Theorem11Gen.lean`. -/

/-- If `ε`-chains refine to `E`, `E` is an `ε`-chain. -/
theorem isEpsChain_of_refines {m n : ℕ} {E : Chain X m} {D : Chain X n} (hED : E.Refines D)
    {ε : ℝ} (hD : IsEpsChain D ε) : IsEpsChain E ε := fun i => by
  obtain ⟨j, hj⟩ := hED i
  exact ⟨(hD j).1.subset hj, lt_of_le_of_lt (Metric.diam_mono hj (hD j).1) (hD j).2⟩

theorem exists_subset_of_iInter_subset {Y : Type*} [TopologicalSpace Y] {K : ℕ → Set Y}
    (hanti : Antitone K) (hc : IsCompact (K 0)) (hcl : ∀ n, IsClosed (K n)) {U : Set Y}
    (hU : IsOpen U) (h : ⋂ n, K n ⊆ U) : ∃ n, K n ⊆ U := by
  by_contra hno
  push_neg at hno
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => K n \ U) (fun i => diff_subset_diff_left (hanti (Nat.le_succ i)))
    (fun n => by obtain ⟨x, hx, hxU⟩ := not_subset.mp (hno n); exact ⟨x, hx, hxU⟩)
    (hc.diff hU) (fun n => (hcl n).sdiff hU)
  rw [mem_iInter] at hx
  exact (hx 0).2 (h (mem_iInter.mpr fun n => (hx n).1))

/-- The intersection of a decreasing sequence of continua is a continuum. -/
theorem isContinuum_iInter_antitone {K : ℕ → Set X} (hK : ∀ n, Fold.Q78.IsContinuum (K n))
    (hanti : Antitone K) : Fold.Q78.IsContinuum (⋂ n, K n) := by
  have hcl : ∀ n, IsClosed (K n) := fun n => (hK n).1.isClosed
  refine ⟨(hK 0).1.of_isClosed_subset (isClosed_iInter hcl) (iInter_subset _ 0), ?_, ?_⟩
  · exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
      (fun i => hanti (Nat.le_succ i)) (fun n => (hK n).2.nonempty) (hK 0).1 hcl
  · rw [isPreconnected_closed_iff]
    intro t t' ht ht' hcov ⟨a, haK, hat⟩ ⟨b, hbK, hbt'⟩
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hA : IsClosed ((⋂ n, K n) ∩ t) := (isClosed_iInter hcl).inter ht
    have hB : IsClosed ((⋂ n, K n) ∩ t') := (isClosed_iInter hcl).inter ht'
    have hAB : Disjoint ((⋂ n, K n) ∩ t) ((⋂ n, K n) ∩ t') := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have : x ∈ (⋂ n, K n) ∩ (t ∩ t') := ⟨hx1.1, hx1.2, hx2.2⟩
      rw [hemp] at this; exact this
    obtain ⟨O₁, O₂, hO₁, hO₂, hAO, hBO, hO⟩ := normal_separation hA hB hAB
    obtain ⟨n, hn⟩ := exists_subset_of_iInter_subset hanti (hK 0).1 hcl (hO₁.union hO₂)
      (fun x hx => by
        rcases hcov hx with h | h
        · exact Or.inl (hAO ⟨hx, h⟩)
        · exact Or.inr (hBO ⟨hx, h⟩))
    obtain ⟨z, -, hz1, hz2⟩ := (hK n).2.2 O₁ O₂ hO₁ hO₂ hn
      ⟨a, mem_iInter.mp haK n, hAO ⟨haK, hat⟩⟩ ⟨b, mem_iInter.mp hbK n, hBO ⟨hbK, hbt'⟩⟩
    exact Set.disjoint_left.mp hO hz1 hz2

/-- **Bing's minimal counterexample.** If a continuum is not `ε`-coverable, it contains a
subcontinuum which is not `ε`-coverable but all of whose proper subcontinua are (Brouwer
reduction, `exists_minimal_of_seq`: the property passes to intersections of decreasing sequences,
since a chain covering the intersection covers some member — `exists_subset_of_iInter_subset`).
(Shape change: over the compact space `S`. The skeleton's hypothesis `hε : 0 < ε` turned out
not to be needed; it is kept since it is part of the commissioned statement.) -/
theorem exists_minimal_notCoverable {M : Set S} (hM : Fold.Q78.IsContinuum M) {ε : ℝ}
    (hε : 0 < ε) (hnot : ¬ EpsCoverable M ε) :
    ∃ S' ⊆ M, Fold.Q78.IsContinuum S' ∧ ¬ EpsCoverable S' ε ∧
      ∀ K ⊆ S', Fold.Q78.IsContinuum K → K ≠ S' → EpsCoverable K ε := by
  set P : Set S → Prop := fun s => Fold.Q78.IsContinuum s ∧ s ⊆ M ∧ ¬ EpsCoverable s ε with hP
  have hseq : ∀ h : ℕ → Set S, (∀ n, P (h n)) → Antitone h → P (⋂ n, h n) := by
    intro h hh hanti
    refine ⟨isContinuum_iInter_antitone (fun n => (hh n).1) hanti,
      (iInter_subset h 0).trans (hh 0).2.1, ?_⟩
    rintro ⟨n, D, hD, hsub⟩
    obtain ⟨k, hk⟩ := exists_subset_of_iInter_subset hanti (hh 0).1.1
      (fun n => (hh n).1.1.isClosed) (isOpen_iUnion D.isOpen) hsub
    exact (hh k).2.2 ⟨n, D, hD, hk⟩
  obtain ⟨m, hmM, hPm, hmin⟩ := exists_minimal_of_seq P (fun s hs => hs.1.1.isClosed) hseq
    (s₀ := M) ⟨hM, subset_rfl, hnot⟩
  refine ⟨m, hmM, hPm.1, hPm.2.2, fun K hKm hK hne => ?_⟩
  by_contra hKc
  exact hne (hmin K ⟨hK, hKm.trans hmM, hKc⟩ hKm)

-- (Item 3, `exists_degenerate_interior_elt`, is false and was removed in batch 103: see `LEDGER.md`.)

-- Commented-out statement `not_separation_of_accumulates` removed in batch 103; see `LEDGER.md`.

end Structure

/-! ## §3. Sufficiency, conditional on Theorem 10 -/

section Sufficiency

variable {S : Type u} [MetricSpace S] [CompactSpace S]

end Sufficiency

end HPC.Plane
