import HPC.BJ59.Zigzag

/-!
# Batch 200, §3: private points

The skeleton's `exists_privatePoint_interior` and `exists_privatePoint_shrink` (statements
verbatim), and the certificate `bj_theorem7_proof_n3` of §6. Route: commission 200 §§3, 6.

A *private point* of a link is a point of the covered set outside the closures of the other links.
-/

namespace HPC.BJ59

open Set Topology Metric Filter

section Private

variable {X : Type*} [MetricSpace X]

/-- A preconnected non-degenerate set has no isolated points: an open set meeting it meets it
outside any given finite set. -/
theorem exists_mem_inter_notMem_finite {K : Set X} (hK : IsPreconnected K) (hKn : K.Nontrivial)
    {U : Set X} (hU : IsOpen U) (hUK : (K ∩ U).Nonempty) {F : Set X} (hF : F.Finite) :
    ∃ w ∈ K ∩ U, w ∉ F := by
  obtain ⟨z, hzK, hzU⟩ := hUK
  by_cases hzF : z ∉ F
  · exact ⟨z, ⟨hzK, hzU⟩, hzF⟩
  push_neg at hzF
  set U' : Set X := U \ (F \ {z})
  have hU' : IsOpen U' := hU.sdiff (hF.diff.isClosed)
  by_contra hno
  push_neg at hno
  have hsub : K ∩ U' ⊆ {z} := by
    rintro w ⟨hwK, hwU, hwF⟩
    by_contra hwz
    exact hwF ⟨hno w ⟨hwK, hwU⟩, hwz⟩
  have hcov : K ⊆ {z} ∪ U'ᶜ := fun w hw => by
    by_cases h : w ∈ U'
    · exact Or.inl (hsub ⟨hw, h⟩)
    · exact Or.inr h
  have hK2 : (K ∩ U'ᶜ).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    obtain ⟨a, ha, b, hb, hab⟩ := hKn
    have hsub' : K ⊆ {z} := fun w hw => by
      rcases hcov hw with h' | h'
      · exact h'
      · exact absurd (show w ∈ K ∩ U'ᶜ from ⟨hw, h'⟩) (h ▸ notMem_empty w)
    exact hab ((hsub' ha).trans (hsub' hb).symm)
  obtain ⟨w, -, hwz, hwU'⟩ := isPreconnected_closed_iff.1 hK {z} U'ᶜ isClosed_singleton
    hU'.isClosed_compl hcov ⟨z, hzK, rfl⟩ hK2
  rw [mem_singleton_iff.1 hwz] at hwU'
  exact hwU' ⟨hzU, fun h => h.2 rfl⟩

/-- Distinct points chosen from open sets meeting a preconnected non-degenerate set. -/
theorem exists_injective_choice {K : Set X} (hK : IsPreconnected K) (hKn : K.Nontrivial) {n : ℕ}
    (U : Fin n → Set X) (hU : ∀ i, IsOpen (U i)) (hUK : ∀ i, (K ∩ U i).Nonempty) :
    ∃ z : Fin n → X, Function.Injective z ∧ ∀ i, z i ∈ K ∩ U i := by
  classical
  set V : ℕ → Set X := fun t => if h : t < n then U ⟨t, h⟩ else univ
  have hV : ∀ t, IsOpen (V t) := fun t => by
    simp only [V]; split_ifs; exacts [hU _, isOpen_univ]
  have hVK : ∀ t, (K ∩ V t).Nonempty := fun t => by
    simp only [V]; split_ifs
    · exact hUK _
    · obtain ⟨a, ha, -⟩ := hKn; exact ⟨a, ha, mem_univ _⟩
  have key : ∀ k : ℕ, ∃ z : ℕ → X, (∀ t < k, z t ∈ K ∩ V t) ∧ InjOn z (Iio k) := by
    intro k
    induction k with
    | zero => exact ⟨fun _ => hKn.nonempty.some, fun t ht => absurd ht (Nat.not_lt_zero _),
        fun a ha => absurd ha (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨z, hz, hzi⟩ := ih
      obtain ⟨w, hw, hwF⟩ := exists_mem_inter_notMem_finite hK hKn (hV k) (hVK k)
        ((finite_Iio k).image z)
      refine ⟨Function.update z k w, fun t ht => ?_, fun a ha b hb hab => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
        · rw [Function.update_of_ne (by omega)]; exact hz t h
        · subst h; rw [Function.update_self]; exact hw
      · simp only [mem_Iio] at ha hb
        by_cases hak : a = k <;> by_cases hbk : b = k
        · rw [hak, hbk]
        · rw [hak, Function.update_self, Function.update_of_ne hbk] at hab
          exact absurd ⟨b, (show b < k by omega), hab.symm⟩ hwF
        · rw [hbk, Function.update_self, Function.update_of_ne hak] at hab
          exact absurd ⟨a, (show a < k by omega), hab⟩ hwF
        · rw [Function.update_of_ne hak, Function.update_of_ne hbk] at hab
          exact hzi (show a < k by omega) (show b < k by omega) hab
  obtain ⟨z, hz, hzi⟩ := key n
  refine ⟨fun i => z i, fun a b hab => Fin.ext (hzi a.isLt b.isLt hab), fun i => ?_⟩
  have := hz i i.isLt
  simpa [V, i.isLt] using this

/-- A positive lower bound for finitely many positive numbers. -/
theorem exists_pos_forall_le {ι : Type*} [Finite ι] (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ r > 0, ∀ i, r ≤ g i := by
  have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i, r ≤ g i := eventually_all.2 fun i =>
    Filter.eventually_of_mem (Ioo_mem_nhdsGT (hg i)) fun _ h => h.2.le
  have h0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, h⟩ := (h0.and h1).exists
  exact ⟨r, hr, h⟩

/-- **Private points.** A chain in Bing–Jones's sense properly covering a non-degenerate continuum
can be shrunk, link by link, so that each link contains a point of the continuum outside the
closures of the other links. (Compactness is not used; the hypothesis may be weakened.) -/
theorem exists_privatePoint_shrink {K : Set X} (hK : Fold.Q78.IsContinuum K) (hKn : K.Nontrivial)
    {n : ℕ} (D : Chain X n) (hD : IsBJChain D) (hKD : K ⊆ D.union)
    (hDK : ∀ i, (D.link i ∩ K).Nonempty) :
    ∃ D' : Chain X n, IsBJChain D' ∧ K ⊆ D'.union ∧ (∀ i, D'.link i ⊆ D.link i) ∧
      ∀ i, ∃ p ∈ K ∩ D'.link i, ∀ j, j ≠ i → p ∉ closure (D'.link j) := by
  classical
  have hKc : IsPreconnected K := hK.2.2
  obtain ⟨z, hzi, hz⟩ := exists_injective_choice hKc hKn D.link D.isOpen
    fun i => (hDK i).mono fun x hx => ⟨hx.2, hx.1⟩
  choose s hs hsD using fun i => Metric.isOpen_iff.1 (D.isOpen i) (z i) (hz i).2
  obtain ⟨r₁, hr₁, hr₁le⟩ := exists_pos_forall_le (fun i => s i / 2) fun i => by linarith [hs i]
  obtain ⟨r₂, hr₂, hr₂le⟩ := exists_pos_forall_le
    (fun p : Fin n × Fin n => if p.1 = p.2 then 1 else dist (z p.1) (z p.2) / 3) fun p => by
      simp only
      split_ifs with h
      · exact one_pos
      · have : 0 < dist (z p.1) (z p.2) := dist_pos.2 fun e => h (hzi e)
        linarith
  set r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hball : ∀ i, closedBall (z i) r ⊆ D.link i := fun i x hx => by
    have h1 : r₁ ≤ s i / 2 := hr₁le i
    have h2 := hs i
    exact hsD i (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx)
      (by linarith [min_le_left r₁ r₂])))
  have hsep : ∀ i j, i ≠ j → 3 * r ≤ dist (z i) (z j) := fun i j hij => by
    have := hr₂le (i, j)
    simp only [hij, if_false] at this
    linarith [min_le_right r₁ r₂]
  have hdisj : ∀ i j x, x ∈ closedBall (z i) r → x ∈ closedBall (z j) r → i = j := by
    intro i j x hi hj
    by_contra hij
    have := hsep i j hij
    have h1 : dist x (z i) ≤ r := mem_closedBall.1 hi
    have h2 : dist x (z j) ≤ r := mem_closedBall.1 hj
    linarith [dist_triangle_right (z i) (z j) x, dist_comm x (z i), dist_comm x (z j)]
  set Rm : Fin n → Set X := fun j => ⋃ i : {i : Fin n // i ≠ j}, closedBall (z i) r
  have hRm : ∀ j, IsClosed (Rm j) := fun j => isClosed_iUnion_of_finite fun _ => isClosed_closedBall
  set L : Fin n → Set X := fun j => D.link j \ Rm j
  have hLo : ∀ j, IsOpen (L j) := fun j => (D.isOpen j).sdiff (hRm j)
  have hLD : ∀ j, L j ⊆ D.link j := fun j => diff_subset
  have hzL : ∀ j, z j ∈ L j := by
    intro j
    refine ⟨(hz j).2, fun h => ?_⟩
    obtain ⟨⟨i, hij⟩, hi⟩ := mem_iUnion.1 h
    exact hij (hdisj i j (z j) hi (mem_closedBall_self hr.le))
  have hKL : K ⊆ ⋃ j, L j := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKD hx)
    by_cases hxR : x ∈ Rm j
    · obtain ⟨⟨i, hij⟩, hi⟩ := mem_iUnion.1 hxR
      refine mem_iUnion.2 ⟨i, hball i hi, fun h => ?_⟩
      obtain ⟨⟨k, hki⟩, hk⟩ := mem_iUnion.1 h
      exact hki (hdisj k i x hk hi)
    · exact mem_iUnion.2 ⟨j, hj, hxR⟩
  have hLK : ∀ j, (L j ∩ K).Nonempty := fun j => ⟨z j, hzL j, (hz j).1⟩
  have hLdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs → L i ∩ L j = ∅ := by
    intro i j hij
    refine eq_empty_of_forall_notMem fun x ⟨hxi, hxj⟩ => ?_
    have := (D.adjacent i j).1 ⟨x, hLD i hxi, hLD j hxj⟩
    omega
  let D' : Chain X n :=
    { link := L
      isOpen := hLo
      adjacent := fun i j => by
        constructor
        · intro h
          by_contra h'
          push_neg at h'
          rw [hLdisj i j h'] at h
          exact not_nonempty_empty h
        · intro h
          rcases lt_trichotomy i.val j.val with hlt | heq | hgt
          · exact adjacent_meet_of_cover hKc L hLo hKL hLK hLdisj i j (by omega)
          · have : i = j := Fin.ext heq
            subst this
            exact ⟨z i, hzL i, hzL i⟩
          · rw [inter_comm]
            exact adjacent_meet_of_cover hKc L hLo hKL hLK hLdisj j i (by omega) }
  refine ⟨D', fun i j hij => ?_, hKL, hLD, fun i => ⟨z i, ⟨(hz i).1, hzL i⟩, fun j hji => ?_⟩⟩
  · obtain ⟨δ, hδ, hd⟩ := hD i j hij
    exact ⟨δ, hδ, fun x hx y hy => hd x (hLD i hx) y (hLD j hy)⟩
  · intro hcl
    obtain ⟨b, hb, hdb⟩ := Metric.mem_closure_iff.1 hcl r hr
    exact hb.2 (mem_iUnion.2 ⟨⟨i, fun h => hji h.symm⟩, mem_closedBall'.2 hdb.le⟩)

end Private

end HPC.BJ59
