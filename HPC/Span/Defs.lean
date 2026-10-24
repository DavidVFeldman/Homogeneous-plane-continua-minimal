import HPC.Fold.Questions78

/-!
# Batch 191, §2: span (Oversteegen–Tymchatyn 1982, p. 129; Hoehn–Oversteegen 2016, p. 184)

The definitions of the skeleton (`HPC/Span/OT82A.lean` in the commission), and the elementary
lemmas §2.1–§2.4. Only positivity of span matters, so the span notions are topological: a
continuum `Z ⊆ A × A` missing the diagonal.
-/

namespace HPC.Span

open Set Topology Metric Filter

section Defs

variable {X : Type*} [MetricSpace X]

/-- The off-diagonal condition. -/
def OffDiag (Z : Set (X × X)) : Prop := ∀ p ∈ Z, p.1 ≠ p.2

/-- **Positive surjective span** of `A` (O–T p. 129, `σ*(A) > 0`), topological form: a continuum
`Z ⊆ A × A` missing the diagonal, with both projections onto `A`. -/
def SurjSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A ∧ Prod.snd '' Z = A

/-- **Positive surjective semi-span** of `A` (`σ₀*(A) > 0`): the first projection onto `A`. -/
def SurjSemiSpanPos (A : Set X) : Prop :=
  ∃ Z ⊆ A ×ˢ A, Fold.Q78.IsContinuum Z ∧ OffDiag Z ∧ Prod.fst '' Z = A

/-- **Semi-span zero** (`σ₀(X) = 0`). -/
def SemiSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ A : Set X, Fold.Q78.IsContinuum A → ¬ SurjSemiSpanPos A

/-- **Span zero in the sense of Hoehn–Oversteegen** (2016, p. 184): every subcontinuum
`Z ⊆ X × X` with `π₁(Z) ⊆ π₂(Z)` meets the diagonal. -/
def HOSpanZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ Z : Set (X × X), Fold.Q78.IsContinuum Z → Prod.fst '' Z ⊆ Prod.snd '' Z → ∃ p ∈ Z, p.1 = p.2

end Defs

section SpanLemmas

variable {X : Type*} [MetricSpace X]

/-- Minimum step of §2.1: on a compact nonempty set off the diagonal, `d` has a positive lower
bound. -/
theorem exists_pos_le_dist {Z : Set (X × X)} (hZ : Fold.Q78.IsContinuum Z)
    (hoff : OffDiag Z) : ∃ α > 0, ∀ p ∈ Z, α ≤ dist p.1 p.2 := by
  obtain ⟨p₀, hp₀, hmin⟩ := hZ.1.exists_isMinOn hZ.2.nonempty
    (continuous_fst.dist continuous_snd).continuousOn
  exact ⟨dist p₀.1 p₀.2, dist_pos.2 (hoff p₀ hp₀), fun p hp => hmin hp⟩

/-- The image of a continuum off the diagonal under `f × f`, `f` injective on `A ⊇ πᵢ(Z)`. -/
private theorem image_prodMap_data {Y : Type*} [MetricSpace Y] {A : Set X} {Z : Set (X × X)}
    (hZA : Z ⊆ A ×ˢ A) (hZ : Fold.Q78.IsContinuum Z) (hoff : OffDiag Z) {f : X → Y}
    (hf : Continuous f) (hinj : InjOn f A) :
    Prod.map f f '' Z ⊆ (f '' A) ×ˢ (f '' A) ∧ Fold.Q78.IsContinuum (Prod.map f f '' Z) ∧
      OffDiag (Prod.map f f '' Z) ∧ Prod.fst '' (Prod.map f f '' Z) = f '' (Prod.fst '' Z) ∧
      Prod.snd '' (Prod.map f f '' Z) = f '' (Prod.snd '' Z) := by
  have hc : Continuous (Prod.map f f) := hf.prodMap hf
  refine ⟨?_, ⟨hZ.1.image hc, hZ.2.image _ hc.continuousOn⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem f (hZA hp).1, mem_image_of_mem f (hZA hp).2⟩
  · rintro _ ⟨p, hp, rfl⟩ h
    exact hoff p hp (hinj (hZA hp).1 (hZA hp).2 h)
  · rw [image_image, image_image]; rfl
  · rw [image_image, image_image]; rfl

/-- **§2.2**: positivity is carried by maps injective on `A`. -/
theorem SurjSpanPos.image {Y : Type*} [MetricSpace Y] {A : Set X} (h : SurjSpanPos A)
    {f : X → Y} (hf : Continuous f) (hinj : InjOn f A) : SurjSpanPos (f '' A) := by
  obtain ⟨Z, hZA, hZ, hoff, h1, h2⟩ := h
  obtain ⟨hs, hc, ho, e1, e2⟩ := image_prodMap_data hZA hZ hoff hf hinj
  exact ⟨_, hs, hc, ho, by rw [e1, h1], by rw [e2, h2]⟩

/-- The swap of a continuum is a continuum. -/
theorem isContinuum_swap {Z : Set (X × X)} (hZ : Fold.Q78.IsContinuum Z) :
    Fold.Q78.IsContinuum (Prod.swap '' Z) :=
  ⟨hZ.1.image continuous_swap, hZ.2.image _ continuous_swap.continuousOn⟩

omit [MetricSpace X] in
/-- The swap of a set off the diagonal is off the diagonal. -/
theorem offDiag_swap {Z : Set (X × X)} (hoff : OffDiag Z) : OffDiag (Prod.swap '' Z) := by
  rintro _ ⟨p, hp, rfl⟩ h
  exact hoff p hp h.symm

omit [MetricSpace X] in
theorem fst_image_swap (Z : Set (X × X)) : Prod.fst '' (Prod.swap '' Z) = Prod.snd '' Z := by
  rw [image_image]; rfl

omit [MetricSpace X] in
theorem snd_image_swap (Z : Set (X × X)) : Prod.snd '' (Prod.swap '' Z) = Prod.fst '' Z := by
  rw [image_image]; rfl

/-- **§2.3**: O–T's semi-span zero is H–O's span zero.

*Shape change:* the skeleton's `[CompactSpace X]` is not needed and has been removed. -/
theorem semiSpanZero_iff_hoSpanZero : SemiSpanZero X ↔ HOSpanZero X := by
  constructor
  · intro h Z hZ hsub
    by_contra hcon
    push_neg at hcon
    refine h (Prod.snd '' Z) ⟨hZ.1.image continuous_snd, hZ.2.image _ continuous_snd.continuousOn⟩
      ⟨Prod.swap '' Z, ?_, isContinuum_swap hZ, offDiag_swap hcon, fst_image_swap Z⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem _ hp, hsub (mem_image_of_mem _ hp)⟩
  · rintro h A - ⟨Z, hZA, hZ, hoff, h1⟩
    obtain ⟨p, hp, hpd⟩ := h (Prod.swap '' Z) (isContinuum_swap hZ) (by
      rw [fst_image_swap, snd_image_swap, h1]
      rintro _ ⟨p, hp, rfl⟩
      exact (hZA hp).2)
    exact offDiag_swap hoff p hp hpd

end SpanLemmas

end HPC.Span
