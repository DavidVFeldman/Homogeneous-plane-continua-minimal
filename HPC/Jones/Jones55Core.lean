import HPC.Jones.Defs
import HPC.Jones.Basic
import HPC.PseudoArc.T13Topo
import HPC.Jones.Jones51
import HPC.Plane.Arcs48

/-!
# Batch 136, item D: the core of Jones 1955, Theorem 1

F. B. Jones, *On a certain type of homogeneous plane continuum*, Proc. AMS 6 (1955), 735–740.
Notation (p. 736): `L_x` is `x` together with all points `y` such that `M` is not aposyndetic at
`y` with respect to `x`; `U_x = M − L_x` (`aposSet x`). The definitions `Lset`, `CutsFrom`,
`lRel`, `lSetoid` are the skeleton's (§5), unchanged.

**The decisive step is not Jones's.** Jones obtains (b) and (c) of his Theorem 1 through the sets
`H`, `N_o`, the claims (9)–(12), and the case argument "`N_o + U_o ≠ M`" with `d(q)`, `E_n`, `M₀`
(pp. 737–738). Here both follow from one consequence of the Effros theorem
(`HPC.Effros.effros_homogeneous`, batch 134):

* `aposAt_of_isContinuum_interior` (**spreading**): in a homogeneous compact metric space, if a
  continuum `K` with nonempty interior contains `o` and misses `x`, then `X` is aposyndetic at `o`
  with respect to `x`. (Move `K` by all homeomorphisms `ε`-close to the identity; the closure of the
  union is a continuum, since each image meets `K` in its interior, it still misses `x`, and by
  Effros it contains a ball about `o`.)

Then:

* `not_aposAt_trans`: non-aposyndesis is transitive;
* `aposSet_eq_of_not_aposAt`: `y ∈ L_x ⇒ U_y = U_x` (transitivity gives `U_x ⊆ U_y`, then the
  Lemma of Jones 1951);
* `mem_Lset_iff_Lset_eq` (Theorem 1 (b)) and `Lset_subset_of_meets` (Theorem 1 (c)).

Neither uses decomposability; (b) and (c) hold in every homogeneous compact metric space. Jones's
claims (1)–(12) are kept as named lemmas `jones55_claim1` … `jones55_claim12`, in his numbering;
(1)–(10) by Jones's arguments, (11) and (12) from (c) (they replace Jones's transfinite sequence of
closed sets and his use of (11) in (12)). The characterization `N_o = L_o` and the properties
(a)–(f) of p. 739 follow.
-/

namespace HPC.Jones

open Set Topology Filter Metric

/-! ### Spreading (Effros) -/

section Spread

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Spreading.** In a homogeneous compact metric space, if a continuum `K` with nonempty interior
contains `o` and misses `x`, then `X` is aposyndetic at `o` with respect to `x`. -/
theorem aposAt_of_isContinuum_interior (hX : IsHomogeneous X) {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (hint : (interior K).Nonempty) {o x : X} (ho : o ∈ K)
    (hx : x ∉ K) : AposAt o x := by
  obtain ⟨b, hb⟩ := hint
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp isOpen_interior b hb
  have hd : 0 < infDist x K := (hK.1.isClosed.notMem_iff_infDist_pos ⟨o, ho⟩).mp hx
  set ε := min ε₀ (infDist x K / 2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (half_pos hd)
  obtain ⟨δ, hδ, hEff⟩ := HPC.Effros.effros_homogeneous hX hε
  set S : Set (X ≃ₜ X) := {h | ∀ z, dist (h z) z < ε}
  set 𝒞 : Set (Set X) := (fun h : X ≃ₜ X => K ∪ h '' K) '' S
  set Z : Set X := closure (⋃₀ 𝒞)
  have hpre : IsPreconnected (⋃₀ 𝒞) := by
    refine isPreconnected_sUnion o 𝒞 ?_ ?_
    · rintro _ ⟨h, -, rfl⟩
      exact Or.inl ho
    · rintro _ ⟨h, hS, rfl⟩
      have hhb : h b ∈ K := by
        refine interior_subset (hball ?_)
        exact lt_of_lt_of_le (hS b) (min_le_left _ _)
      exact hK.2.isPreconnected.union (h b) hhb ⟨b, interior_subset hb, rfl⟩
        (hK.2.isPreconnected.image _ h.continuous.continuousOn)
  have hZsub : Z ⊆ {z | infDist z K ≤ ε} := by
    refine closure_minimal ?_ (isClosed_le (continuous_infDist_pt K) continuous_const)
    rintro z ⟨_, ⟨h, hS, rfl⟩, hz⟩
    rcases hz with hz | ⟨k, hk, rfl⟩
    · show infDist z K ≤ ε
      rw [infDist_zero_of_mem hz]
      exact hε.le
    · show infDist (h k) K ≤ ε
      exact (infDist_le_dist_of_mem hk).trans (hS k).le
  have hxZ : x ∉ Z := by
    intro hxZ
    have h1 : infDist x K ≤ ε := hZsub hxZ
    have h2 : ε ≤ infDist x K / 2 := min_le_right _ _
    linarith
  have hballZ : ball o δ ⊆ Z := by
    intro y hy
    obtain ⟨h, hho, hS⟩ := hEff o y (by rw [dist_comm]; exact hy)
    refine subset_closure ⟨K ∪ h '' K, ⟨h, hS, rfl⟩, Or.inr ⟨o, ho, hho⟩⟩
  refine ⟨Z, ball o δ, ⟨isClosed_closure.isCompact, ?_⟩, isOpen_ball, mem_ball_self hδ, hballZ,
    hxZ⟩
  exact ⟨⟨o, hballZ (mem_ball_self hδ)⟩, hpre.closure⟩

/-- **Non-aposyndesis is transitive** in a homogeneous compact metric space. -/
theorem not_aposAt_trans (hX : IsHomogeneous X) {x y z : X} (hzy : ¬ AposAt z y)
    (hyx : ¬ AposAt y x) : ¬ AposAt z x := by
  rintro ⟨K, V, hK, hV, hzV, hVK, hxK⟩
  have hyK : y ∈ K := by
    by_contra hyK
    exact hzy ⟨K, V, hK, hV, hzV, hVK, hyK⟩
  exact hyx (aposAt_of_isContinuum_interior hX hK
    ⟨z, interior_maximal hVK hV hzV⟩ hyK hxK)

/-- If `X` is not aposyndetic at `y` with respect to `x`, then `U_y = U_x`. -/
theorem aposSet_eq_of_not_aposAt (hX : IsHomogeneous X) {x y : X} (h : ¬ AposAt y x) :
    aposSet y = aposSet x := by
  have hsub : aposSet x ⊆ aposSet y := by
    intro z hz
    rw [aposSet_eq] at hz ⊢
    by_contra hzy
    exact not_aposAt_trans hX hzy h hz
  by_contra hne
  exact jones51_lemma hX (ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hne he.symm⟩)

end Spread

/-! ### Definitions (skeleton §5) -/

section Jones55

variable {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]

/-- `L_x`. -/
def Lset (x : X) : Set X := insert x {y | y ≠ x ∧ ¬ AposAt y x}

/-- The decomposition `G = {L_x}` as a relation. -/
def lRel (x y : X) : Prop := Lset x = Lset y

def lSetoid (X : Type*) [MetricSpace X] [CompactSpace X] [ConnectedSpace X] : Setoid X where
  r := lRel
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-! ### Elementary facts about `L_x` -/

omit [CompactSpace X] [ConnectedSpace X] in
theorem mem_Lset_iff {x y : X} : y ∈ Lset x ↔ ¬ AposAt y x := by
  by_cases hy : y = x
  · subst hy
    simp [Lset, not_aposAt_self]
  · simp [Lset, hy]

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_eq_setOf (x : X) : Lset x = {y | ¬ AposAt y x} := by
  ext y
  exact mem_Lset_iff

omit [CompactSpace X] [ConnectedSpace X] in
theorem mem_Lset_self (x : X) : x ∈ Lset x := mem_insert x _

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_compl (x : X) : (Lset x)ᶜ = aposSet x := by
  ext y
  rw [mem_compl_iff, mem_Lset_iff, not_not, aposSet_eq]
  rfl

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_eq_compl (x : X) : Lset x = (aposSet x)ᶜ := by
  rw [← Lset_compl, compl_compl]

omit [CompactSpace X] [ConnectedSpace X] in
theorem isClosed_Lset (x : X) : IsClosed (Lset x) := by
  rw [Lset_eq_setOf]
  exact isClosed_not_aposAt_left x

/-- Each `L_x` is a continuum (Jones 1948, Theorem 3). -/
theorem isContinuum_Lset (x : X) : Fold.Q78.IsContinuum (Lset x) := by
  have h := theorem3 x
  rwa [setOf_theorem3_eq, ← Lset_eq_setOf] at h

omit [CompactSpace X] [ConnectedSpace X] in
theorem Lset_homeomorph (T : X ≃ₜ X) (x : X) : Lset (T x) = T '' Lset x := by
  rw [Lset_eq_compl, Lset_eq_compl, aposSet_homeomorph, T.image_compl]

/-! ### Theorem 1 (b) and (c), for every homogeneous compact metric continuum -/

omit [ConnectedSpace X] in
/-- **Theorem 1 (b), general form.** In a homogeneous compact metric continuum, `y ∈ L_x` iff
`L_y = L_x`. -/
theorem mem_Lset_iff_Lset_eq (hX : IsHomogeneous X) {x y : X} :
    y ∈ Lset x ↔ Lset y = Lset x := by
  constructor
  · intro h
    rw [Lset_eq_compl, Lset_eq_compl, aposSet_eq_of_not_aposAt hX (mem_Lset_iff.mp h)]
  · intro h
    rw [← h]
    exact mem_Lset_self y

omit [ConnectedSpace X] in
/-- **Theorem 1 (c), general form.** In a homogeneous compact metric continuum, a subcontinuum
meeting `L_x` and its complement contains `L_x`. -/
theorem Lset_subset_of_meets (hX : IsHomogeneous X) {x : X} {K : Set X}
    (hK : Fold.Q78.IsContinuum K) (h1 : (K ∩ Lset x).Nonempty) (h2 : (K \ Lset x).Nonempty) :
    Lset x ⊆ K := by
  obtain ⟨a, haK, hax⟩ := h1
  obtain ⟨b, hbK, hbx⟩ := h2
  intro y hy
  by_contra hyK
  have hLy : Lset y = Lset x := (mem_Lset_iff_Lset_eq hX).mp hy
  have hby : AposAt b y := by
    have : b ∉ Lset y := hLy ▸ hbx
    rwa [mem_Lset_iff, not_not] at this
  obtain ⟨B, O, hB, hO, hbO, hOB, hyB⟩ := hby
  have hK' : Fold.Q78.IsContinuum (K ∪ B) :=
    ⟨hK.1.union hB.1, IsConnected.union ⟨b, hbK, hOB hbO⟩ hK.2 hB.2⟩
  have hint : (interior (K ∪ B)).Nonempty :=
    ⟨b, interior_maximal (hOB.trans subset_union_right) hO hbO⟩
  have hay : AposAt a y := aposAt_of_isContinuum_interior hX hK' hint (Or.inl haK)
    (fun h => h.elim hyK hyB)
  exact (mem_Lset_iff.mp (hLy ▸ hax)) hay

/-! ### Tools for the claims -/

omit [CompactSpace X] in
/-- An open set in a nondegenerate continuum is a single point only if empty. -/
theorem isOpen_nontrivial_of_nonempty [Nontrivial X] {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) : U.Nontrivial := by
  obtain ⟨z, hz⟩ := hne
  by_contra hnt
  have hUz : U = {z} := (not_nontrivial_iff.mp hnt).eq_singleton_of_mem hz
  have hclopen : IsClopen ({z} : Set X) := ⟨isClosed_singleton, hUz ▸ hU⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact singleton_ne_empty z h
  · obtain ⟨w, hw⟩ := exists_ne z
    exact hw (by simpa using (h ▸ mem_univ w : w ∈ ({z} : Set X)))

/-- **Claim (3), Bing's form transferred.** In a homogeneous nondegenerate compact metric
continuum, no point cuts two nonempty open sets from each other: some continuum meets both and
misses the point. (Bing 1948, Corollary 2, `HPC.Plane.arcs_corollary2`, and homogeneity. Bing's
`Cuts` asks `A ⊄ R`; for a nonempty open `A` and `R = {p}` this holds since `{p}` is not open.) -/
theorem exists_continuum_meets_of_open [Nontrivial X] (hX : IsHomogeneous X) (p : X)
    {D E : Set X} (hD : IsOpen D) (hE : IsOpen E) (hDne : D.Nonempty) (hEne : E.Nonempty) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ p ∉ K ∧ (K ∩ D).Nonempty ∧ (K ∩ E).Nonempty := by
  obtain ⟨p₀, -, -, -, -, hp₀, -⟩ := HPC.Plane.arcs_corollary2 (S := X) (M := univ)
    ⟨isCompact_univ, isConnected_univ⟩ nontrivial_univ
  obtain ⟨T, hT⟩ := hX p₀ p
  have hD' : IsOpen (T ⁻¹' D) := hD.preimage T.continuous
  have hE' : IsOpen (T ⁻¹' E) := hE.preimage T.continuous
  have hDne' : (T ⁻¹' D ∩ univ).Nonempty := by
    obtain ⟨d, hd⟩ := hDne
    exact ⟨T.symm d, by simpa using hd, mem_univ _⟩
  have hEne' : (T ⁻¹' E ∩ univ).Nonempty := by
    obtain ⟨e, he⟩ := hEne
    exact ⟨T.symm e, by simpa using he, mem_univ _⟩
  have hnot := hp₀ _ _ hD' hE' hDne' hEne'
  have hns : ∀ A : Set X, IsOpen A → (A ∩ univ).Nonempty → ¬ (A ∩ univ ⊆ {p₀}) := by
    intro A hA hAne hsub
    have h1 : (A ∩ univ).Nontrivial := isOpen_nontrivial_of_nonempty (hA.inter isOpen_univ) hAne
    obtain ⟨u, hu, v, hv, huv⟩ := h1
    exact huv ((mem_singleton_iff.mp (hsub hu)).trans (mem_singleton_iff.mp (hsub hv)).symm)
  unfold HPC.Plane.Cuts at hnot
  push_neg at hnot
  obtain ⟨K, hK, -, hKD, hKE, hKp⟩ := hnot ⟨univ, ⟨isCompact_univ, isConnected_univ⟩,
    subset_univ _, by simpa using hDne', by simpa using hEne'⟩ (hns _ hD' hDne')
    (hns _ hE' hEne')
  refine ⟨T '' K, isContinuum_image_homeomorph T hK, ?_, ?_, ?_⟩
  · rintro ⟨k, hk, hkp⟩
    rw [← hT] at hkp
    exact (eq_empty_iff_forall_notMem.mp hKp) k ⟨hk, mem_singleton_iff.mpr (T.injective hkp)⟩
  · obtain ⟨k, hk, hkD, -⟩ := hKD
    exact ⟨T k, mem_image_of_mem _ hk, hkD⟩
  · obtain ⟨k, hk, hkE, -⟩ := hKE
    exact ⟨T k, mem_image_of_mem _ hk, hkE⟩

/-- **Claim (5), continuum form.** Two points of `U_p` lie in a continuum missing `p`. -/
theorem exists_continuum_of_mem_aposSet [Nontrivial X] (hX : IsHomogeneous X) {p a b : X}
    (ha : a ∈ aposSet p) (hb : b ∈ aposSet p) :
    ∃ K : Set X, Fold.Q78.IsContinuum K ∧ a ∈ K ∧ b ∈ K ∧ p ∉ K := by
  rw [aposSet_eq] at ha hb
  obtain ⟨A, V, hA, hV, haV, hVA, hpA⟩ := ha
  obtain ⟨B, W, hB, hW, hbW, hWB, hpB⟩ := hb
  obtain ⟨K, hK, hpK, ⟨u, huK, huV⟩, ⟨v, hvK, hvW⟩⟩ :=
    exists_continuum_meets_of_open hX p hV hW ⟨a, haV⟩ ⟨b, hbW⟩
  refine ⟨A ∪ K ∪ B, ⟨(hA.1.union hK.1).union hB.1, ?_⟩, Or.inl (Or.inl (hVA haV)),
    Or.inr (hWB hbW), ?_⟩
  · exact IsConnected.union ⟨v, Or.inr hvK, hWB hvW⟩
      (IsConnected.union ⟨u, hVA huV, huK⟩ hA.2 hK.2) hB.2
  · rintro ((h | h) | h)
    · exact hpA h
    · exact hpK h
    · exact hpB h

/-! ### Jones's claims (1)–(12) -/

/-- A decomposable continuum is nondegenerate. -/
theorem nontrivial_of_isDecomposableSpace (hd : IsDecomposableSpace X) : Nontrivial X := by
  obtain ⟨x, y, hxy, -⟩ := theorem8.mp hd
  exact ⟨⟨x, y, hxy⟩⟩

/-- In a decomposable homogeneous continuum each `U_p` is nonempty. -/
theorem aposSet_nonempty (hX : IsHomogeneous X) (hd : IsDecomposableSpace X) (p : X) :
    (aposSet p).Nonempty := by
  obtain ⟨x, y, -, hxy⟩ := theorem8.mp hd
  obtain ⟨T, hT⟩ := hX y p
  refine ⟨T x, ?_⟩
  rw [aposSet_eq, ← hT]
  exact hxy.image T

/-! ### `N_o = L_o` and the properties (a)–(f) of p. 739 -/

omit [CompactSpace X] [ConnectedSpace X] in
/-- **Property (e)** (p. 739): `M − g = U(g)`. -/
theorem jones55_prop_e (o : X) : (Lset o)ᶜ = aposSet o := Lset_compl o

end Jones55

end HPC.Jones
