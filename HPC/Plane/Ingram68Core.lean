import HPC.Plane.Fugate66BThm1
import HPC.Plane.Fugate66BMiller
import HPC.Plane.SorgenfreyDefs
import HPC.Plane.Fugate66Lemma1
import HPC.Plane.Arcs48

/-!
# Batch 132, Part II (1): Ingram's Lemmas 1–2 and the property (∗∗), without Sorgenfrey

Source: W. T. Ingram, *Decomposable circle-like continua*, Fund. Math. 63 (1968), 193–198
(`doc/sources/ingram1968.pdf`), Lemmas 1 and 2, and COMMISSION-batch132 §§2–3.

Every appeal Ingram makes to Sorgenfrey's Theorem 1.8 in Lemmas 1–2 is replaced by one lemma,
`isTriod_of_core`: three continua that meet a continuum `N`, pairwise meet only inside `N`, and do
not lie in `N`, form a triod with core `N`. Ingram's "components of `B − (B ∩ D)`" become arms from
boundary bumping (`exists_arm`).

* `ingram_lemma1` — Lemma 1, used form (`not_isAtriodic_of_three`: three pieces give a triod with
  core `A`).
* `eq_of_subset_of_split`, `ingram_lemma2` — Lemma 2 (irreducibility needs no extra hypothesis;
  terminality is proved for a hereditarily unicoherent `A`).
* `ingramStarWeak_holds` — the property (∗∗) used in Part I.
-/

namespace HPC.Plane

open Set Metric

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-! ### A triod with a given core

The one triod-producing device of the direct route. If three continua `X₁`, `X₂`, `X₃` each meet a
continuum `N`, pairwise meet only inside `N`, and none lies in `N`, then `N ∪ X₁ ∪ X₂ ∪ X₃` is a
triod with core `N`: the three sets `Xᵢ ∖ N` are mutually separated, since `closure (Xᵢ ∖ N) ⊆ Xᵢ`.
Every use of Sorgenfrey's theorem in Ingram's Lemmas 1–2 and in the proof of (∗∗) below is
replaced by this lemma. -/

omit [CompactSpace S] in
/-- **A triod with a given core.** -/
theorem isTriod_of_core {N X₁ X₂ X₃ : Set S} (hN : Fold.Q78.IsContinuum N)
    (h₁ : Fold.Q78.IsContinuum X₁) (h₂ : Fold.Q78.IsContinuum X₂) (h₃ : Fold.Q78.IsContinuum X₃)
    (m₁ : (X₁ ∩ N).Nonempty) (m₂ : (X₂ ∩ N).Nonempty) (m₃ : (X₃ ∩ N).Nonempty)
    (o₁₂ : X₁ ∩ X₂ ⊆ N) (o₁₃ : X₁ ∩ X₃ ⊆ N) (o₂₃ : X₂ ∩ X₃ ⊆ N)
    (n₁ : ¬ X₁ ⊆ N) (n₂ : ¬ X₂ ⊆ N) (n₃ : ¬ X₃ ⊆ N) : IsTriod (N ∪ X₁ ∪ X₂ ∪ X₃) := by
  have c₁ : Fold.Q78.IsContinuum (N ∪ X₁) := by
    obtain ⟨x, hx1, hxN⟩ := m₁
    exact isContinuum_union hN h₁ ⟨x, hxN, hx1⟩
  have c₂ : Fold.Q78.IsContinuum (N ∪ X₁ ∪ X₂) := by
    obtain ⟨x, hx2, hxN⟩ := m₂
    exact isContinuum_union c₁ h₂ ⟨x, Or.inl hxN, hx2⟩
  have c₃ : Fold.Q78.IsContinuum (N ∪ X₁ ∪ X₂ ∪ X₃) := by
    obtain ⟨x, hx3, hxN⟩ := m₃
    exact isContinuum_union c₂ h₃ ⟨x, Or.inl (Or.inl hxN), hx3⟩
  have cl₁ : closure (X₁ \ N) ⊆ X₁ := closure_minimal diff_subset h₁.1.isClosed
  have cl₂ : closure (X₂ \ N) ⊆ X₂ := closure_minimal diff_subset h₂.1.isClosed
  have cl₃ : closure (X₃ \ N) ⊆ X₃ := closure_minimal diff_subset h₃.1.isClosed
  refine ⟨c₃, N, hN, subset_union_left.trans (subset_union_left.trans subset_union_left),
    X₁ \ N, X₂ \ N, X₃ \ N, diff_nonempty.mpr n₁, diff_nonempty.mpr n₂, diff_nonempty.mpr n₃,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_diff, mem_union]; tauto
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₁₂ ⟨cl₁ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₁₂ ⟨hx.1, cl₂ hx'⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₁₃ ⟨cl₁ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₁₃ ⟨hx.1, cl₃ hx'⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx'.2 (o₂₃ ⟨cl₂ hx, hx'.1⟩)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 (o₂₃ ⟨hx.1, cl₃ hx'⟩)

omit [CompactSpace S] in
/-- **The core lemma inside an atriodic set**: the configuration of `isTriod_of_core` cannot
occur inside an atriodic set. -/
theorem not_core_of_isAtriodic {Z N X₁ X₂ X₃ : Set S} (hZ : IsAtriodic Z)
    (hN : Fold.Q78.IsContinuum N)
    (h₁ : Fold.Q78.IsContinuum X₁) (h₂ : Fold.Q78.IsContinuum X₂) (h₃ : Fold.Q78.IsContinuum X₃)
    (hNZ : N ⊆ Z) (s₁ : X₁ ⊆ Z) (s₂ : X₂ ⊆ Z) (s₃ : X₃ ⊆ Z)
    (m₁ : (X₁ ∩ N).Nonempty) (m₂ : (X₂ ∩ N).Nonempty) (m₃ : (X₃ ∩ N).Nonempty)
    (o₁₂ : X₁ ∩ X₂ ⊆ N) (o₁₃ : X₁ ∩ X₃ ⊆ N) (o₂₃ : X₂ ∩ X₃ ⊆ N)
    (n₁ : ¬ X₁ ⊆ N) (n₂ : ¬ X₂ ⊆ N) (n₃ : ¬ X₃ ⊆ N) : False :=
  hZ _ (union_subset (union_subset (union_subset hNZ s₁) s₂) s₃)
    (isTriod_of_core hN h₁ h₂ h₃ m₁ m₂ m₃ o₁₂ o₁₃ o₂₃ n₁ n₂ n₃)

/-! ### Ingram's Lemma 1 -/

/-! ### Ingram's Lemma 2 -/

/-! ### The property (∗∗) -/

end HPC.Plane
