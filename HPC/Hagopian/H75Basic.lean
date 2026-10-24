import HPC.Hagopian.H75Defs

/-!
# Batch 155: admissible maps of irreducible continua (Hagopian 1975 §3)

Elementary facts about an admissible map `k : E → [0, 1]` (continuous, onto, connected fibres) of a
compact set `E`:

* `IsAdmissibleMap.isPreconnected_preimage`: preimages of preconnected sets are preconnected
  (`k` is closed, with connected fibres);
* `isContinuum_img`: the sets `k⁻¹(S)`, `S` a closed interval, are continua;
* for `E` irreducible between `a` and `b`: `a`, `b` lie in the end layers (`end_layers`), and a
  subcontinuum meeting the layers over `d < e` contains every layer strictly between
  (`layer_subset_of_meets'`);
* `not_isIndecomposable_of_typeA'`: the necessity half of Lemma 2;
* `fibre_subset_fibre`: the type A′ case of Lemma 3.
-/

namespace HPC.Hagopian

open Set Topology

variable {X : Type*} [MetricSpace X]

section Admissible

variable {E : Set X} {k : E → unitInterval}

/-- **Preimages of preconnected sets are preconnected** under an admissible map of a compact set
(a closed map with connected fibres). -/
theorem IsAdmissibleMap.isPreconnected_preimage (hEc : IsCompact E) (hk : IsAdmissibleMap E k)
    {S : Set unitInterval} (hS : IsPreconnected S) : IsPreconnected (k ⁻¹' S) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  have hcl : IsClosedMap k := hk.1.isClosedMap
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub hdis
  have hfib : ∀ s ∈ S, k ⁻¹' {s} ⊆ u ∨ k ⁻¹' {s} ⊆ v := by
    intro s hs
    refine (isPreconnected_iff_subset_of_disjoint_closed.1 (hk.2.2 s).isPreconnected) u v hu hv
      (fun x hx => hsub (show k x ∈ S from (mem_singleton_iff.1 hx) ▸ hs)) ?_
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxu, hxv⟩
    have : x ∈ k ⁻¹' S ∩ (u ∩ v) := ⟨show k x ∈ S from (mem_singleton_iff.1 hx) ▸ hs, hxu, hxv⟩
    rw [hdis] at this; exact this
  have hSsub : S ⊆ (k '' v)ᶜ ∪ (k '' u)ᶜ := by
    intro s hs
    rcases hfib s hs with h | h
    · left
      rintro ⟨x, hxv, rfl⟩
      have : x ∈ k ⁻¹' S ∩ (u ∩ v) := ⟨hs, h rfl, hxv⟩
      rw [hdis] at this; exact this
    · right
      rintro ⟨x, hxu, rfl⟩
      have : x ∈ k ⁻¹' S ∩ (u ∩ v) := ⟨hs, hxu, h rfl⟩
      rw [hdis] at this; exact this
  have hSdis : S ∩ ((k '' v)ᶜ ∩ (k '' u)ᶜ) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro s ⟨hs, hsv, hsu⟩
    obtain ⟨x, rfl⟩ := hk.2.1 s
    rcases hsub hs with h | h
    · exact hsu ⟨x, h, rfl⟩
    · exact hsv ⟨x, h, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint.1 hS) _ _ (hcl v hv).isOpen_compl
    (hcl u hu).isOpen_compl hSsub hSdis with h | h
  · left
    intro x hx
    rcases hsub hx with h' | h'
    · exact h'
    · exact absurd ⟨x, h', rfl⟩ (h hx)
  · right
    intro x hx
    rcases hsub hx with h' | h'
    · exact absurd ⟨x, h', rfl⟩ (h hx)
    · exact h'

omit [MetricSpace X] in
theorem mem_img_iff {S : Set unitInterval} {x : X} :
    x ∈ Subtype.val '' (k ⁻¹' S) ↔ ∃ h : x ∈ E, k ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩; exact ⟨⟨x, h⟩, hx, rfl⟩

omit [MetricSpace X] in
theorem img_subset (S : Set unitInterval) : Subtype.val '' (k ⁻¹' S) ⊆ E := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

omit [MetricSpace X] in
theorem val_mem_img {S : Set unitInterval} {y : E} : (y : X) ∈ Subtype.val '' (k ⁻¹' S) ↔ k y ∈ S :=
  ⟨fun h => by obtain ⟨h', hy⟩ := mem_img_iff.1 h; exact hy, fun h => ⟨y, h, rfl⟩⟩

theorem isCompact_img (hEc : IsCompact E) (hk : Continuous k) {S : Set unitInterval}
    (hS : IsClosed S) : IsCompact (Subtype.val '' (k ⁻¹' S)) := by
  haveI : CompactSpace E := isCompact_iff_compactSpace.mp hEc
  exact ((hS.preimage hk).isCompact).image continuous_subtype_val

/-- The sets `k⁻¹(S)`, `S` closed, preconnected and nonempty, are continua. -/
theorem isContinuum_img (hEc : IsCompact E) (hk : IsAdmissibleMap E k) {S : Set unitInterval}
    (hS : IsClosed S) (hSp : IsPreconnected S) (hSne : S.Nonempty) :
    Fold.Q78.IsContinuum (Subtype.val '' (k ⁻¹' S)) := by
  refine ⟨isCompact_img hEc hk.1 hS, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hSne
    obtain ⟨y, rfl⟩ := hk.2.1 s
    exact ⟨_, y, hs, rfl⟩
  · exact (hk.isPreconnected_preimage hEc hSp).image _ continuous_subtype_val.continuousOn

theorem isContinuum_layer (hEc : IsCompact E) (hk : IsAdmissibleMap E k) (s : unitInterval) :
    Fold.Q78.IsContinuum (layer k s) :=
  isContinuum_img hEc hk isClosed_singleton isPreconnected_singleton (singleton_nonempty s)

/-- Swapping the ends of an irreducible continuum. -/
theorem IsIrreducibleBetween.symm' {a b : X} (h : IsIrreducibleBetween E a b) :
    IsIrreducibleBetween E b a :=
  ⟨h.1, h.2.2.1, h.2.1, fun K hK hKE hb ha => h.2.2.2 K hK hKE ha hb⟩

/-- An end of an irreducible continuum lies in an end layer. -/
theorem end_layer {a b : X} (hE : IsIrreducibleBetween E a b) (hk : IsAdmissibleMap E k) :
    k ⟨a, hE.2.1⟩ = 0 ∨ k ⟨a, hE.2.1⟩ = 1 := by
  by_contra hcon
  push_neg at hcon
  set t := k ⟨a, hE.2.1⟩ with ht
  have h0 : 0 < t := lt_of_le_of_ne (show (0 : unitInterval) ≤ t from t.2.1) (fun h => hcon.1 h.symm)
  have h1 : t < 1 := lt_of_le_of_ne (show t ≤ (1 : unitInterval) from t.2.2) (fun h => hcon.2 h)
  have hEc := hE.1.1
  have key : ∀ S : Set unitInterval, IsClosed S → IsPreconnected S → t ∈ S →
      (k ⟨b, hE.2.2.1⟩ ∈ S) → S = univ := by
    intro S hS hSp htS hbS
    have hc := isContinuum_img hEc hk hS hSp ⟨t, htS⟩
    have heq := hE.2.2.2 _ hc (img_subset S) (val_mem_img.2 htS) (val_mem_img.2 hbS)
    refine eq_univ_of_forall fun s => ?_
    obtain ⟨y, rfl⟩ := hk.2.1 s
    have : (y : X) ∈ Subtype.val '' (k ⁻¹' S) := by rw [heq]; exact y.2
    exact val_mem_img.1 this
  rcases le_total (k ⟨b, hE.2.2.1⟩) t with hb | hb
  · have := key (Iic t) isClosed_Iic isPreconnected_Iic (mem_Iic.2 le_rfl) hb
    have h1' : (1 : unitInterval) ∈ Iic t := this ▸ mem_univ _
    exact absurd (h1'.trans_lt' h1) (lt_irrefl _)
  · have := key (Ici t) isClosed_Ici isPreconnected_Ici (mem_Ici.2 le_rfl) hb
    have h0' : (0 : unitInterval) ∈ Ici t := this ▸ mem_univ _
    exact absurd (lt_of_lt_of_le h0 h0') (lt_irrefl _)

/-- The two ends of an irreducible continuum lie in different end layers. -/
theorem end_layers {a b : X} (hE : IsIrreducibleBetween E a b) (hk : IsAdmissibleMap E k) :
    (k ⟨a, hE.2.1⟩ = 0 ∧ k ⟨b, hE.2.2.1⟩ = 1) ∨ (k ⟨a, hE.2.1⟩ = 1 ∧ k ⟨b, hE.2.2.1⟩ = 0) := by
  have hEc := hE.1.1
  have key : ∀ s : unitInterval, k ⟨a, hE.2.1⟩ = s → k ⟨b, hE.2.2.1⟩ = s → False := by
    intro s has hbs
    have hc := isContinuum_layer hEc hk s
    have heq := hE.2.2.2 _ hc (img_subset _) ((val_mem_img (y := ⟨a, hE.2.1⟩)).2 has)
      ((val_mem_img (y := ⟨b, hE.2.2.1⟩)).2 hbs)
    -- some point has a different value
    obtain ⟨y, hy⟩ := hk.2.1 (if s = 0 then 1 else 0)
    have : (y : X) ∈ layer k s := by rw [heq]; exact y.2
    have hys : k y = s := val_mem_img.1 this
    rw [hys] at hy
    split_ifs at hy with h
    · rw [h] at hy; exact zero_ne_one hy
    · exact h hy
  rcases end_layer hE hk with ha | ha <;> rcases end_layer (IsIrreducibleBetween.symm' hE) hk with hb | hb
  · exact absurd (key 0 ha hb) id
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd (key 1 ha hb) id

/-- **The interval lemma** (both orientations of the ends). A subcontinuum of an irreducible `E`
meeting the layers over `d` and `e` contains every layer strictly between. -/
theorem layer_subset_of_meets' {a b : X} (hE : IsIrreducibleBetween E a b)
    (hk : IsAdmissibleMap E k) {K : Set X} (hKE : K ⊆ E) (hK : Fold.Q78.IsContinuum K)
    {d e u : unitInterval} (hd : (K ∩ layer k d).Nonempty) (he : (K ∩ layer k e).Nonempty)
    (hdu : d < u) (hue : u < e) : layer k u ⊆ K := by
  have hEc := hE.1.1
  -- `P = K ∪ k⁻¹[0, d] ∪ k⁻¹[e, 1]` is a continuum containing both ends
  set L := Subtype.val '' (k ⁻¹' Iic d) with hL
  set R := Subtype.val '' (k ⁻¹' Ici e) with hR
  have hLc := isContinuum_img (S := Iic d) hEc hk isClosed_Iic isPreconnected_Iic nonempty_Iic
  have hRc := isContinuum_img (S := Ici e) hEc hk isClosed_Ici isPreconnected_Ici nonempty_Ici
  obtain ⟨p, hpK, hpd⟩ := hd
  obtain ⟨q, hqK, hqe⟩ := he
  have hpL : p ∈ L := by
    obtain ⟨y, hy, rfl⟩ := hpd; exact ⟨y, show k y ≤ d from (mem_singleton_iff.1 hy).le, rfl⟩
  have hqR : q ∈ R := by
    obtain ⟨y, hy, rfl⟩ := hqe; exact ⟨y, show e ≤ k y from (mem_singleton_iff.1 hy).ge, rfl⟩
  have hPc : Fold.Q78.IsContinuum (K ∪ L ∪ R) := by
    refine ⟨(hK.1.union hLc.1).union hRc.1, hK.2.nonempty.mono (subset_union_left.trans
      subset_union_left), ?_⟩
    refine IsPreconnected.union' ?_ (hK.2.isPreconnected.union' ⟨p, hpK, hpL⟩
      hLc.2.isPreconnected) hRc.2.isPreconnected
    exact ⟨q, Or.inl hqK, hqR⟩
  have hPE : K ∪ L ∪ R ⊆ E := union_subset (union_subset hKE (img_subset _)) (img_subset _)
  have hends : ∀ z ∈ ({a, b} : Set X), z ∈ K ∪ L ∪ R := by
    intro z hz
    rcases end_layers hE hk with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hz with rfl | rfl
      · exact Or.inl (Or.inr ⟨_, show k _ ≤ d by rw [ha]; exact d.2.1, rfl⟩)
      · exact Or.inr ⟨_, show e ≤ k _ by rw [hb]; exact e.2.2, rfl⟩
    · rcases hz with rfl | rfl
      · exact Or.inr ⟨_, show e ≤ k _ by rw [ha]; exact e.2.2, rfl⟩
      · exact Or.inl (Or.inr ⟨_, show k _ ≤ d by rw [hb]; exact d.2.1, rfl⟩)
  have hPeq := hE.2.2.2 _ hPc hPE (hends a (Or.inl rfl)) (hends b (Or.inr rfl))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyu : k y = u := mem_singleton_iff.1 hy
  have : (y : X) ∈ K ∪ L ∪ R := by rw [hPeq]; exact y.2
  rcases this with (h | h) | h
  · exact h
  · have := val_mem_img.1 h; rw [mem_Iic, hyu] at this
    exact absurd (lt_of_lt_of_le hdu this) (lt_irrefl _)
  · have := val_mem_img.1 h; rw [mem_Ici, hyu] at this
    exact absurd (lt_of_lt_of_le hue this) (lt_irrefl _)

/-- The interior of a union of two closed sets with empty interiors is empty. -/
theorem interior_union_eq_empty {Y : Type*} [TopologicalSpace Y] {F₀ F₁ : Set Y}
    (h₀ : IsClosed F₀) (hi₀ : interior F₀ = ∅)
    (hi₁ : interior F₁ = ∅) : interior (F₀ ∪ F₁) = ∅ := by
  have hsub1 : interior (F₀ ∪ F₁) ∩ F₀ᶜ ⊆ interior F₁ :=
    interior_maximal (fun x hx => (interior_subset hx.1).resolve_left hx.2)
      (isOpen_interior.inter h₀.isOpen_compl)
  rw [hi₁, subset_empty_iff] at hsub1
  have hsub0 : interior (F₀ ∪ F₁) ⊆ interior F₀ := by
    refine interior_maximal (fun x hx => ?_) isOpen_interior
    by_contra hx0
    have : x ∈ interior (F₀ ∪ F₁) ∩ F₀ᶜ := ⟨hx, hx0⟩
    rw [hsub1] at this; exact this
  rw [hi₀] at hsub0
  exact subset_empty_iff.1 hsub0

/-- For a type A′ map (layers with empty interior), the open middle `k⁻¹(0, 1)` is dense. -/
theorem dense_middle (hk : IsAdmissibleMap E k) (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) :
    Dense (k ⁻¹' Ioo 0 1) := by
  rw [← compl_compl (k ⁻¹' Ioo 0 1), ← interior_eq_empty_iff_dense_compl]
  have : (k ⁻¹' Ioo 0 1)ᶜ = k ⁻¹' {0} ∪ k ⁻¹' {1} := by
    ext x
    simp only [mem_compl_iff, mem_preimage, mem_Ioo, mem_union, mem_singleton_iff, not_and_or,
      not_lt]
    constructor
    · rintro (h | h)
      · exact Or.inl (le_antisymm h (k x).2.1)
      · exact Or.inr (le_antisymm (k x).2.2 h)
    · rintro (h | h)
      · exact Or.inl h.le
      · exact Or.inr h.ge
  rw [this]
  exact interior_union_eq_empty (isClosed_singleton.preimage hk.1) (hk0 0) (hk0 1)

/-- **End sets with type A′ layers.** A subcontinuum meeting both end layers is everything. -/
theorem eq_of_meets_ends {a b : X} (hE : IsIrreducibleBetween E a b) (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {K : Set X} (hKE : K ⊆ E)
    (hK : Fold.Q78.IsContinuum K) (h0 : (K ∩ layer k 0).Nonempty)
    (h1 : (K ∩ layer k 1).Nonempty) : K = E := by
  refine Subset.antisymm hKE ?_
  have hmid : Subtype.val '' (k ⁻¹' Ioo 0 1) ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact layer_subset_of_meets' hE hk hKE hK h0 h1 hy.1 hy.2 ⟨y, rfl, rfl⟩
  have hcl : IsClosed (Subtype.val ⁻¹' K : Set E) := hK.1.isClosed.preimage continuous_subtype_val
  have hsub : k ⁻¹' Ioo 0 1 ⊆ Subtype.val ⁻¹' K := fun y hy => hmid ⟨y, hy, rfl⟩
  have := (dense_middle hk hk0).closure_eq ▸ closure_minimal hsub hcl
  intro x hx
  exact this (mem_univ (⟨x, hx⟩ : E))

/-- **Lemma 3, the type A′ case** (Kuratowski §48 VII, proof of Theorem 4): a layer of a type A′
map `k` (a nowhere dense continuum) lies in a single layer of any admissible map `k'`. If `k'` took
two values `d < e` on the layer, then by the interval lemma (for `k'`) the open set `k'⁻¹(d, e)`
would lie in the layer. -/
theorem fibre_subset_fibre {a b : X} (hE : IsIrreducibleBetween E a b) (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {k' : E → unitInterval} (hk' : IsAdmissibleMap E k')
    (t : unitInterval) : ∃ t', k ⁻¹' {t} ⊆ k' ⁻¹' {t'} := by
  obtain ⟨y₀, hy₀⟩ := hk.2.1 t
  refine ⟨k' y₀, fun y hy => ?_⟩
  by_contra hne
  have hne' : k' y ≠ k' y₀ := hne
  have hEc := hE.1.1
  have hLc := isContinuum_layer hEc hk t
  -- the layer contains `k'⁻¹(d, e)` for `d < e` the two values
  have key : ∀ y₁ y₂ : E, k y₁ = t → k y₂ = t → k' y₁ < k' y₂ → False := by
    intro y₁ y₂ h₁ h₂ hlt
    have hsub : k' ⁻¹' Ioo (k' y₁) (k' y₂) ⊆ k ⁻¹' {t} := by
      intro z hz
      have := layer_subset_of_meets' (k := k') hE hk' (img_subset _) hLc
        ⟨y₁, ⟨y₁, h₁, rfl⟩, y₁, rfl, rfl⟩ ⟨y₂, ⟨y₂, h₂, rfl⟩, y₂, rfl, rfl⟩ hz.1 hz.2
        (⟨z, rfl, rfl⟩ : (z : X) ∈ layer k' (k' z))
      exact val_mem_img.1 this
    have hopen : IsOpen (k' ⁻¹' Ioo (k' y₁) (k' y₂)) := isOpen_Ioo.preimage hk'.1
    obtain ⟨m, hm1, hm2⟩ := exists_between hlt
    obtain ⟨z, hz⟩ := hk'.2.1 m
    have := interior_maximal hsub hopen (show z ∈ _ from by rw [mem_preimage, hz]; exact ⟨hm1, hm2⟩)
    rw [hk0 t] at this; exact this
  rcases lt_or_gt_of_ne hne' with h | h
  · exact key y y₀ hy hy₀ h
  · exact key y₀ y hy₀ hy h

/-- **Uniqueness of the type A′ decomposition.** -/
theorem fibre_eq_iff {a b : X} (hE : IsIrreducibleBetween E a b) (hk : IsAdmissibleMap E k)
    (hk0 : ∀ t, interior (k ⁻¹' {t}) = ∅) {k' : E → unitInterval} (hk' : IsAdmissibleMap E k')
    (hk'0 : ∀ t, interior (k' ⁻¹' {t}) = ∅) (x y : E) : k x = k y ↔ k' x = k' y := by
  constructor
  · intro h
    obtain ⟨t', ht'⟩ := fibre_subset_fibre hE hk hk0 hk' (k x)
    exact (ht' (rfl : k x = k x)).trans (ht' h.symm).symm
  · intro h
    obtain ⟨t', ht'⟩ := fibre_subset_fibre hE hk' hk'0 hk (k' x)
    exact (ht' (rfl : k' x = k' x)).trans (ht' h.symm).symm

end Admissible

end HPC.Hagopian
