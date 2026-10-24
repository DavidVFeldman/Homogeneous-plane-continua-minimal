import HPC.PseudoArc.Theorem5
import HPC.PseudoArc.T13Topo

/-!
# Batch 81: chains between two points, and reaching both end links

* `Chain.span D a b`: the union of the links of `D` with index in `[a, b]`; it is `ε`-chained
  when every link has diameter at most `ε` (`Chain.chainedAt_span`).
* `Description.isConnected_M`: the described continuum is connected (the repository did not have
  this; it is the limit of the chained sets `(D i)^*`).
* `Chain.exists_isSubchainFrom`: two points in the union of a chain, lying in no common link, are
  joined by a subchain.
* `Description.exists_subchain_meets_ends'`: Bing's first paragraph of the proof of Theorem 13.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace Chain

variable {n : ℕ}

/-- The union of the links of `D` with index in `[a, b]`. -/
def span (D : Chain X n) (a b : Fin n) : Set X := ⋃ (t : Fin n) (_ : a ≤ t ∧ t ≤ b), D.link t

theorem mem_span {D : Chain X n} {a b : Fin n} {x : X} :
    x ∈ D.span a b ↔ ∃ t : Fin n, a ≤ t ∧ t ≤ b ∧ x ∈ D.link t := by
  simp only [span, mem_iUnion, exists_prop, and_assoc]

theorem union_eq_span (D : Chain X n) (hn : 0 < n) :
    D.union = D.span ⟨0, hn⟩ ⟨n - 1, by omega⟩ := by
  ext x
  simp only [union, mem_iUnion, mem_span]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Fin.le_def.mpr (Nat.zero_le _), Fin.le_def.mpr (by simp only; omega), ht⟩
  · rintro ⟨t, -, -, ht⟩
    exact ⟨t, ht⟩

/-- A span of a chain whose links have diameter at most `ε` is `ε`-chained. -/
theorem chainedAt_span (D : Chain X n) (a b : Fin n) {ε : ℝ}
    (hbdd : ∀ t, Bornology.IsBounded (D.link t)) (hdiam : ∀ t, diam (D.link t) ≤ ε) :
    T13.ChainedAt (D.span a b) ε := by
  intro U V hUV hsep
  have hε : 0 ≤ ε := le_trans diam_nonneg (hdiam a)
  -- each link of the span lies on one side
  have side : ∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ U ∨ D.link t ⊆ V := by
    intro t hat htb
    by_cases h : D.link t ⊆ U
    · exact Or.inl h
    · right
      obtain ⟨x, hxt, hxU⟩ := not_subset.mp h
      have hxV : x ∈ V := by
        rcases hUV (mem_span.mpr ⟨t, hat, htb, hxt⟩) with h' | h'
        · exact absurd h' hxU
        · exact h'
      intro y hyt
      rcases hUV (mem_span.mpr ⟨t, hat, htb, hyt⟩) with h' | h'
      · have h1 := hsep y h' x hxV
        have h2 := dist_le_diam_of_mem (hbdd t) hyt hxt
        linarith [hdiam t]
      · exact h'
  have hUV0 : ∀ z, z ∈ U → z ∉ V := fun z hzU hzV => by
    have := hsep z hzU z hzV
    simp at this
    linarith
  -- propagate the side of the first link along the span
  have prop : ∀ W W' : Set X, (∀ z, z ∈ W → z ∉ W') →
      (∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ W ∨ D.link t ⊆ W') →
      D.link a ⊆ W → ∀ t : Fin n, a ≤ t → t ≤ b → D.link t ⊆ W := by
    intro W W' hWW' hside ha
    have key : ∀ m : ℕ, ∀ ht : a.val + m < n, a.val + m ≤ b.val →
        D.link ⟨a.val + m, ht⟩ ⊆ W := by
      intro m
      induction m with
      | zero => intro ht _; simpa using ha
      | succ m ih =>
        intro ht hmb
        have ih' := ih (by omega) (by omega)
        rcases hside ⟨a.val + (m + 1), ht⟩ (Fin.le_def.mpr (by simp)) (Fin.le_def.mpr hmb)
          with h | h
        · exact h
        · exfalso
          obtain ⟨z, hz1, hz2⟩ := (D.adjacent_iff ⟨a.val + m, by omega⟩ ⟨a.val + (m + 1), ht⟩).mpr
            (by simp only; omega)
          exact hWW' z (ih' hz1) (h hz2)
    intro t hat htb
    have := key (t.val - a.val) (by omega) (by rw [Fin.le_def] at hat htb; omega)
    have heq : (⟨a.val + (t.val - a.val), by omega⟩ : Fin n) = t := by
      ext; simp only; rw [Fin.le_def] at hat; omega
    rwa [heq] at this
  by_cases hab : a ≤ b
  · rcases side a le_rfl hab with h | h
    · left
      intro x hx
      obtain ⟨t, hat, htb, hxt⟩ := mem_span.mp hx
      exact prop U V hUV0 side h t hat htb hxt
    · right
      intro x hx
      obtain ⟨t, hat, htb, hxt⟩ := mem_span.mp hx
      exact prop V U (fun z hzV hzU => hUV0 z hzU hzV)
        (fun t h1 h2 => (side t h1 h2).symm) h t hat htb hxt
  · left
    intro x hx
    obtain ⟨t, hat, htb, -⟩ := mem_span.mp hx
    exact absurd (le_trans hat htb) hab

/-- Two links containing the same point are adjacent. -/
theorem val_close_of_mem (D : Chain X n) {x : X} {s t : Fin n} (hs : x ∈ D.link s)
    (ht : x ∈ D.link t) : s.val ≤ t.val + 1 ∧ t.val ≤ s.val + 1 :=
  (D.adjacent_iff s t).mp ⟨x, hs, ht⟩

/-- Two points of the union of a chain lying in no common link are joined by a subchain. -/
theorem exists_isSubchainFrom (D : Chain X n) {R S : X} (hR : R ∈ D.union) (hS : S ∈ D.union)
    (hRS : ∀ t, R ∈ D.link t → S ∉ D.link t) : ∃ a b : Fin n, D.IsSubchainFrom a b R S := by
  classical
  obtain ⟨r0, hr0⟩ := mem_iUnion.mp hR
  obtain ⟨s0, hs0⟩ := mem_iUnion.mp hS
  set IR := Finset.univ.filter (fun t => R ∈ D.link t)
  set IS := Finset.univ.filter (fun t => S ∈ D.link t)
  have hIR : IR.Nonempty := ⟨r0, by simp [IR, hr0]⟩
  have hIS : IS.Nonempty := ⟨s0, by simp [IS, hs0]⟩
  have memR : ∀ t, t ∈ IR ↔ R ∈ D.link t := fun t => by simp [IR]
  have memS : ∀ t, t ∈ IS ↔ S ∈ D.link t := fun t => by simp [IS]
  -- the two index sets are separated
  have hsep : (∀ r ∈ IR, ∀ s ∈ IS, r < s) ∨ (∀ r ∈ IR, ∀ s ∈ IS, s < r) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨r1, hr1, s1, hs1, h1⟩, ⟨r2, hr2, s2, hs2, h2⟩⟩ := hcon
    rw [memR] at hr1 hr2
    rw [memS] at hs1 hs2
    have c1 := D.val_close_of_mem hr1 hr2
    have c2 := D.val_close_of_mem hs1 hs2
    have n11 : r1 ≠ s1 := fun h => hRS r1 hr1 (h ▸ hs1)
    have n12 : r1 ≠ s2 := fun h => hRS r1 hr1 (h ▸ hs2)
    have n21 : r2 ≠ s1 := fun h => hRS r2 hr2 (h ▸ hs1)
    have n22 : r2 ≠ s2 := fun h => hRS r2 hr2 (h ▸ hs2)
    rw [Fin.le_def] at h1 h2
    rw [Ne, Fin.ext_iff] at n11 n12 n21 n22
    omega
  rcases hsep with h | h
  · set a := IR.max' hIR
    set b := IS.min' hIS
    have ha : R ∈ D.link a := (memR a).mp (IR.max'_mem hIR)
    have hb : S ∈ D.link b := (memS b).mp (IS.min'_mem hIS)
    have hab : a < b := h a (IR.max'_mem hIR) b (IS.min'_mem hIS)
    refine ⟨a, b, hab.le, Or.inl ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
    · simpa [sub] using ha
    · have : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
        ext; simp only; rw [Fin.lt_def] at hab; omega
      simp only [sub]; rw [this]; exact hb
    · intro i hi
      simp only [sub] at hi
      have := IR.le_max' _ ((memR _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; omega
    · intro i hi
      simp only [sub] at hi
      have := IS.min'_le _ ((memS _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; have := i.isLt; omega
  · set a := IS.max' hIS
    set b := IR.min' hIR
    have ha : S ∈ D.link a := (memS a).mp (IS.max'_mem hIS)
    have hb : R ∈ D.link b := (memR b).mp (IR.min'_mem hIR)
    have hab : a < b := h b (IR.min'_mem hIR) a (IS.max'_mem hIS)
    refine ⟨a, b, hab.le, Or.inr ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
    · simpa [sub] using ha
    · have : (⟨a.val + (b.val - a.val + 1 - 1), by omega⟩ : Fin n) = b := by
        ext; simp only; rw [Fin.lt_def] at hab; omega
      simp only [sub]; rw [this]; exact hb
    · intro i hi
      simp only [sub] at hi
      have := IS.le_max' _ ((memS _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; omega
    · intro i hi
      simp only [sub] at hi
      have := IR.min'_le _ ((memR _).mpr hi)
      rw [Fin.le_def] at this
      ext; simp only at this ⊢; have := i.isLt; omega

/-- The span of a subchain from `R` to `S` contains `R` and `S`. -/
theorem IsSubchainFrom.mem_span {D : Chain X n} {a b : Fin n} {R S : X}
    (h : D.IsSubchainFrom a b R S) : R ∈ D.span a b ∧ S ∈ D.span a b := by
  obtain ⟨hab, h | h⟩ := h
  · obtain ⟨hn, hR, hS, -, -⟩ := h
    refine ⟨HPC.Chain.mem_span.mpr ⟨_, le_rfl, hab, hR⟩, HPC.Chain.mem_span.mpr ⟨⟨a.val + (b.val - a.val + 1 - 1),
      by omega⟩, Fin.le_def.mpr (by simp), Fin.le_def.mpr (by simp only; omega), hS⟩⟩
  · obtain ⟨hn, hS, hR, -, -⟩ := h
    refine ⟨HPC.Chain.mem_span.mpr ⟨⟨a.val + (b.val - a.val + 1 - 1),
      by omega⟩, Fin.le_def.mpr (by simp), Fin.le_def.mpr (by simp only; omega), hR⟩,
      HPC.Chain.mem_span.mpr ⟨_, le_rfl, hab, hS⟩⟩

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q)

theorem M_eq_iInter_closure : Δ.M = ⋂ i, closure (Δ.D i).union := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    simp only [M, mem_iInter] at hz ⊢
    exact fun i => subset_closure (hz i)
  · intro z hz
    simp only [M, mem_iInter] at hz ⊢
    exact fun i => Δ.closure_union_subset (Nat.lt_succ_self i) (hz (i + 1))

theorem chainedAt_union (i : ℕ) : T13.ChainedAt (Δ.D i).union (Δ.ε i) := by
  rw [(Δ.D i).union_eq_span (Δ.isFrom i).1]
  exact Chain.chainedAt_span _ _ _ (Δ.bdd i) (Δ.diam_le i)

theorem P_mem_union (i : ℕ) : P ∈ (Δ.D i).union := by
  obtain ⟨hn, hP, -⟩ := Δ.isFrom i
  exact mem_iUnion.mpr ⟨_, hP⟩

/-- **The described continuum is connected.** -/
theorem isConnected_M [CompactSpace X] : IsConnected Δ.M := by
  refine ⟨⟨P, Δ.P_mem_M⟩, ?_⟩
  have heq : Δ.M = T13.limSup univ (fun i => (Δ.D i).union) := by
    rw [M_eq_iInter_closure]
    simp only [T13.limSup]
    congr 1
    ext N : 1
    congr 1
    ext z
    simp only [mem_univ, mem_iUnion, exists_prop, true_and]
    constructor
    · intro hz; exact ⟨N, le_rfl, hz⟩
    · rintro ⟨k, hk, hz⟩
      exact Chain.union_subset_of_refines (Δ.refines_of_le hk) hz
  rw [heq]
  exact T13.isPreconnected_limSup Δ.ε_tendsto (fun i _ => Δ.chainedAt_union i)
    (fun i _ => Δ.P_mem_union i) infinite_univ

theorem isContinuum_M [CompactSpace X] : Fold.Q78.IsContinuum Δ.M :=
  ⟨Δ.isCompact_M, Δ.isConnected_M⟩

end Description

end HPC
