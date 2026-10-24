import HPC.Plane.PA51Pre

/-!
# Batch 88: passing between a compact continuum `M ⊆ X` and the compact space `M`

* `subChain`: a chain of `X` covering a preconnected set `M`, every link meeting `M`, restricts to
  a chain of the subspace `M` (consecutive links still meet inside `M`, by connectedness).
* hereditary indecomposability, chainability and composants pass from `M ⊆ X` to the space `M`.
* `ext M r U`: an open set of `X` extending a relatively open `U ⊆ M`, inside the `r`-neighbourhood
  of `M`: the points nearer to `U` than to `M \ U`. It meets `M` in `U`, preserves inclusion and
  disjointness, and (for small `r`) closure-inclusion.
* `lift_description`: a description of the space `M` from `p` to `q` with continuum all of `M`
  lifts to a description in `X` from `p` to `q` with continuum `M`.
-/

namespace HPC.Plane

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace PA51

/-! ### Restricting chains to a subspace -/

/-- Consecutive links of a chain covering a preconnected set `M`, all links meeting `M`, meet
inside `M`. -/
theorem inter_inter_nonempty {n : ℕ} (C : Chain X n) {M : Set X} (hconn : IsPreconnected M)
    (hcov : M ⊆ C.union) (hmeet : ∀ i, (C.link i ∩ M).Nonempty) (i j : Fin n)
    (hij : j.val = i.val + 1) : (C.link i ∩ C.link j ∩ M).Nonempty := by
  have hsub : M ⊆ lowU C (i.val + 1) ∪ highU C i.val := by
    intro x hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov hx)
    rcases Nat.lt_or_ge l.val (i.val + 1) with h | h
    · exact Or.inl (mem_iUnion₂.mpr ⟨l, h, hl⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨l, by omega, hl⟩)
  obtain ⟨a, haC, haM⟩ := hmeet i
  obtain ⟨b, hbC, hbM⟩ := hmeet j
  obtain ⟨z, hzM, hzu, hzv⟩ := hconn _ _ (isOpen_lowU C _) (isOpen_highU C _) hsub
    ⟨a, haM, mem_iUnion₂.mpr ⟨i, by omega, haC⟩⟩ ⟨b, hbM, mem_iUnion₂.mpr ⟨j, by omega, hbC⟩⟩
  obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hzu
  obtain ⟨l', hl', hzl'⟩ := mem_iUnion₂.mp hzv
  have := (C.adjacent_iff l l').mp ⟨z, hzl, hzl'⟩
  have e1 : l = i := Fin.ext (by omega)
  have e2 : l' = j := Fin.ext (by omega)
  subst e1 e2
  exact ⟨z, ⟨hzl, hzl'⟩, hzM⟩

/-- The restriction of a chain covering a preconnected set `M`, every link meeting `M`, to the
subspace `M`. -/
def subChain {n : ℕ} (C : Chain X n) (M : Set X) (hconn : IsPreconnected M)
    (hcov : M ⊆ C.union) (hmeet : ∀ i, (C.link i ∩ M).Nonempty) : Chain M n where
  link i := Subtype.val ⁻¹' C.link i
  isOpen i := (C.isOpen i).preimage continuous_subtype_val
  adjacent i j := by
    constructor
    · rintro ⟨z, h1, h2⟩
      exact (C.adjacent i j).mp ⟨z.1, h1, h2⟩
    · intro h
      have h' : i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by omega
      rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
      · obtain ⟨z, ⟨h1, h2⟩, hz⟩ := inter_inter_nonempty C hconn hcov hmeet i j (by omega)
        exact ⟨⟨z, hz⟩, h1, h2⟩
      · have : i = j := Fin.ext heq
        subst this
        obtain ⟨z, h1, hz⟩ := hmeet i
        exact ⟨⟨z, hz⟩, h1, h1⟩
      · obtain ⟨z, ⟨h1, h2⟩, hz⟩ := inter_inter_nonempty C hconn hcov hmeet j i (by omega)
        exact ⟨⟨z, hz⟩, h2, h1⟩

theorem isBounded_preimage_val {M S : Set X} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (Subtype.val ⁻¹' S : Set M) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hS
  exact Metric.isBounded_iff.mpr ⟨C, fun a ha b hb => hC ha hb⟩

theorem diam_preimage_val_le {M S : Set X} (hS : Bornology.IsBounded S) :
    diam (Subtype.val ⁻¹' S : Set M) ≤ diam S := by
  rw [← isometry_subtype_coe.diam_image]
  exact diam_mono (image_preimage_subset _ _) hS

theorem isContinuum_image_val {M : Set X} {K : Set M} (hK : Fold.Q78.IsContinuum K) :
    Fold.Q78.IsContinuum (Subtype.val '' K) :=
  ⟨hK.1.image continuous_subtype_val, hK.2.image _ continuous_subtype_val.continuousOn⟩

/-- Hereditary indecomposability passes to the subspace. -/
theorem hI_sub {M : Set X} (hM : IsHereditarilyIndecomposable M) :
    ∀ K : Set M, Fold.Q78.IsContinuum K → Fold.Q78.IsIndecomposable K := by
  intro K hK
  refine ⟨hK, fun A B hA hB hAK hBK hAB => ?_⟩
  have hinj : Function.Injective (fun S : Set M => Subtype.val '' S) :=
    Set.image_injective.mpr Subtype.val_injective
  have hKM : Subtype.val '' K ⊆ M := by rintro _ ⟨z, -, rfl⟩; exact z.2
  have := (hM _ hKM (isContinuum_image_val hK)).2 _ _
    (isContinuum_image_val hA) (isContinuum_image_val hB) (image_mono hAK) (image_mono hBK)
    (by rw [← image_union, hAB])
  rcases this with h | h
  · exact Or.inl (hinj h)
  · exact Or.inr (hinj h)

/-- Chainability passes to the subspace. -/
theorem snake_sub {M : Set X} (hM : IsSnakeLike M) (hne : M.Nonempty) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (D : Chain M n), IsEpsChain D ε ∧ univ ⊆ D.union := by
  intro ε hε
  obtain ⟨n, C, hCε, hcov, hmeet⟩ := exists_cover_meeting hM.1.2.isPreconnected hne hM.2 hε
  refine ⟨n, subChain C M hM.1.2.isPreconnected hcov hmeet, fun i => ?_, fun z _ => ?_⟩
  · exact ⟨isBounded_preimage_val (hCε i).1,
      (diam_preimage_val_le (hCε i).1).trans_lt (hCε i).2⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov z.2)
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- Composants: a point outside the composant of `p` in `M` is outside the composant of `p` in
the space `M`. -/
theorem not_mem_composant_sub {M : Set X} {p q : X} (hp : p ∈ M) (hq : q ∈ M)
    (hpq : q ∉ composant M p) :
    (⟨q, hq⟩ : M) ∉ composant (univ : Set M) ⟨p, hp⟩ := by
  intro h
  obtain ⟨K, ⟨hK, -, hKne, hpK⟩, hqK⟩ := mem_sUnion.mp h
  apply hpq
  have hKM : Subtype.val '' K ⊆ M := by rintro _ ⟨z, -, rfl⟩; exact z.2
  refine mem_sUnion.mpr ⟨Subtype.val '' K, ⟨isContinuum_image_val hK,
    hKM, ?_, ⟨_, hpK, rfl⟩⟩, ⟨_, hqK, rfl⟩⟩
  intro heq
  apply hKne
  refine eq_univ_of_forall fun z => ?_
  have : (z : X) ∈ Subtype.val '' K := by rw [heq]; exact z.2
  obtain ⟨w, hw, hwz⟩ := this
  exact Subtype.val_injective hwz ▸ hw

/-- Points in different composants of a nontrivial set are distinct. -/
theorem ne_of_not_mem_composant {M : Set X} (hnd : M.Nontrivial) {p q : X} (hp : p ∈ M)
    (hpq : q ∉ composant M p) : p ≠ q := by
  rintro rfl
  apply hpq
  refine mem_sUnion.mpr ⟨{p}, ⟨⟨isCompact_singleton, isConnected_singleton⟩,
    singleton_subset_iff.mpr hp, ?_, rfl⟩, rfl⟩
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := hnd
  rw [← h] at ha hb
  exact hab ((mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm)

/-- **The description of the subspace** (Bing 1951, Theorem 1, body of the proof). -/
theorem exists_description_sub {M : Set X} (hMs : IsSnakeLike M)
    (hMh : IsHereditarilyIndecomposable M) (hnd : M.Nontrivial) {p q : X} (hp : p ∈ M)
    (hq : q ∈ M) (hpq : q ∉ composant M p) :
    ∃ Δ : Description M ⟨p, hp⟩ ⟨q, hq⟩, Δ.M = univ := by
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hMs.1.1
  refine exists_description_univ (hI_sub hMh) (snake_sub hMs ⟨p, hp⟩) ?_
    (not_mem_composant_sub hp hq hpq)
  intro h
  exact ne_of_not_mem_composant hnd hp hpq (congrArg Subtype.val h)

/-! ### Extending relatively open sets -/

end PA51

end HPC.Plane
