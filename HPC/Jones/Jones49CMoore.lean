import HPC.Jones.Jones49CAnn
import HPC.Jones.Moore22T4

/-!
# Batch 151, items B and C: Moore's sufficiency in local form; Moore 1922 Theorem 4

With the cyclic order of crossing continua (`sector_cyclic`, `HPC/Jones/Jones49CAnn.lean`):

* `exists_crossing_continua_closed`: the PNAS step of batch 150 (`exists_crossing_continua`) for a
  *closed* connected set (the boundary of an unbounded domain need not be compact);
* `exists_cross_sub`: a continuum crossing an annulus inside a closed connected set joining the inner
  disc to the outside, lying in a connected piece through the given inner point (boundary bumping
  twice);
* `cikAt_of_locallyConnectedSpace`: a locally connected set is connected im kleinen at each point;
* `sphere_walk`: walking along the middle square from a point off a closed set `K` to the first
  point of `K`;
* `sufficiency_local`: **Moore's p. 236 argument with Whyburn's local condition** — the boundary of
  an open plane set is locally connected if it is connected and no boundary point is the limit of
  points of `R` no two of which lie in a small connected subset of `R`;
* `propertyS_of_locallyConnected`: **necessity** — a bounded connected open plane set with locally
  connected boundary has property S (no simple connectivity needed);
* `hloc_of_propertyS`: property S gives the local condition (pigeonhole).
-/

namespace HPC.Jones.Sector

open Set Topology Metric Filter HPC.Plane

/-- **The PNAS step for closed sets.** `exists_crossing_continua` (batch 150) with `IsClosed M` in
place of `IsCompact M`; the proof is the same, with `M ∩ B̄(P, r₂)` compact as a closed subset of a
closed ball. -/
theorem exists_crossing_continua_closed {M : Set Pt} (hMcl : IsClosed M) (hMconn : IsConnected M)
    {P : Pt} (hP : P ∈ M) (hnot : ¬ CikAt M P) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ ∃ t : ℕ → Set Pt, Pairwise (fun m n => Disjoint (t m) (t n)) ∧
      ∀ n, IsConnected (t n) ∧ IsCompact (t n) ∧ t n ⊆ M ∧
        (∀ z ∈ t n, r₁ ≤ dist z P ∧ dist z P ≤ r₂) ∧ (∃ z ∈ t n, dist z P = r₁) ∧
        (∃ z ∈ t n, dist z P = r₂) := by
  classical
  simp only [CikAt, not_forall, not_exists, not_and, exists_prop] at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  set r₂ := ε / 3
  set r₁ := ε / 6
  have hr₁ : 0 < r₁ := by positivity
  have hr₁₂ : r₁ < r₂ := by simp only [r₁, r₂]; linarith
  set K := M ∩ closedBall P r₂
  have hKc : IsCompact K := (isCompact_closedBall P r₂).inter_left hMcl
  have hKcl : IsClosed K := hKc.isClosed
  have hPK : P ∈ K := ⟨hP, mem_closedBall_self (by positivity)⟩
  set Γ := connectedComponentIn K P
  -- a point `X` given by the failure is not in `Γ`
  have hXΓ : ∀ {X}, (∀ C ⊆ M, IsPreconnected C → X ∈ C → P ∈ C → Bornology.IsBounded C →
      ¬ diam C < ε) → X ∉ Γ := by
    intro X hX hXG
    have hΓK : Γ ⊆ K := connectedComponentIn_subset _ _
    have hΓb : Γ ⊆ closedBall P r₂ := hΓK.trans inter_subset_right
    refine hX Γ (hΓK.trans inter_subset_left) isPreconnected_connectedComponentIn hXG
      (mem_connectedComponentIn hPK) (isBounded_closedBall.subset hΓb) ?_
    calc diam Γ ≤ 2 * r₂ := diam_le_of_subset_closedBall' (by positivity) hΓb
      _ < ε := by simp only [r₂]; linarith
  set 𝒞 : Set (Set Pt) := {S | ∃ X ∈ M, dist X P < r₁ ∧ X ∉ Γ ∧ S = connectedComponentIn K X}
  have hcomp_eq : ∀ {X z}, z ∈ connectedComponentIn K X →
      connectedComponentIn K X = connectedComponentIn K z := fun hz => connectedComponentIn_eq hz
  have hPnot : ∀ S ∈ 𝒞, P ∉ S := by
    rintro S ⟨X, -, -, hXG, rfl⟩ hPS
    have := hcomp_eq hPS
    have hXK : X ∈ connectedComponentIn K X := by
      by_contra hn
      rw [connectedComponentIn_eq_empty (fun h => hn (mem_connectedComponentIn h))] at hPS
      exact hPS
    rw [this] at hXK
    exact hXG hXK
  have hinf : 𝒞.Infinite := by
    intro hfin
    have hUcl : IsClosed (⋃₀ 𝒞) := sUnion_eq_biUnion ▸ Set.Finite.isClosed_biUnion (s := 𝒞)
      (f := id) hfin fun S hS => by
      obtain ⟨X, -, -, -, rfl⟩ := hS
      exact isClosed_connectedComponentIn_of_isClosed hKcl X
    have hPU : P ∉ ⋃₀ 𝒞 := fun ⟨S, hS, hPS⟩ => hPnot S hS hPS
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hUcl.isOpen_compl P hPU
    obtain ⟨X, hXM, hXd, hX⟩ := hbad (min δ r₁) (lt_min hδ hr₁)
    have hXd1 : dist X P < r₁ := hXd.trans_le (min_le_right _ _)
    have hXK : X ∈ K := ⟨hXM, le_of_lt (hXd1.trans hr₁₂)⟩
    have hmem : connectedComponentIn K X ∈ 𝒞 := ⟨X, hXM, hXd1, hXΓ hX, rfl⟩
    exact hδU (mem_ball.2 (hXd.trans_le (min_le_left _ _)))
      ⟨_, hmem, mem_connectedComponentIn hXK⟩
  set f := hinf.natEmbedding
  have hKM : K ≠ M := by
    intro hKM
    obtain ⟨X, hXM, -, hX⟩ := hbad r₁ hr₁
    apply hXΓ hX
    have : Γ = connectedComponentIn M P := by simp only [Γ, hKM]
    rw [this]
    exact hMconn.isPreconnected.subset_connectedComponentIn hP subset_rfl hXM
  have hstep : ∀ n, ∃ T : Set Pt, IsConnected T ∧ IsCompact T ∧ T ⊆ (f n : Set Pt) ∧
      (∀ z ∈ T, r₁ ≤ dist z P ∧ dist z P ≤ r₂) ∧ (∃ z ∈ T, dist z P = r₁) ∧
      (∃ z ∈ T, dist z P = r₂) := by
    intro n
    obtain ⟨X, hXM, hXd, -, hSX⟩ := (f n).2
    set S := (f n : Set Pt)
    have hXK : X ∈ K := ⟨hXM, le_of_lt (hXd.trans hr₁₂)⟩
    have hSK : S ⊆ K := by rw [hSX]; exact connectedComponentIn_subset _ _
    have hXS : X ∈ S := by rw [hSX]; exact mem_connectedComponentIn hXK
    have hSconn : IsPreconnected S := by rw [hSX]; exact isPreconnected_connectedComponentIn
    have hScl : IsClosed S := by rw [hSX]; exact isClosed_connectedComponentIn_of_isClosed hKcl X
    have hSc : IsCompact S := hKc.of_isClosed_subset hScl hSK
    -- first bumping: `S` meets the outer square
    obtain ⟨K0, -, hK0c, hK0K, hXK0, w, hwK0, hwcl⟩ :=
      exists_continuum_bump_compact hMconn.isPreconnected hKc inter_subset_left hKM hXK
    have hK0S : K0 ⊆ S := by
      rw [hSX]; exact hK0c.isPreconnected.subset_connectedComponentIn hXK0 hK0K
    have hwS : w ∈ S := hK0S hwK0
    have hwd : dist w P = r₂ := by
      have h1 : dist w P ≤ r₂ := (hSK hwS).2
      have h2 : r₂ ≤ dist w P := by
        have hsub : M \ K ⊆ {z | r₂ ≤ dist z P} := fun z hz => by
          by_contra h
          exact hz.2 ⟨hz.1, mem_closedBall.2 (le_of_lt (not_le.1 h))⟩
        exact closure_minimal hsub (isClosed_le continuous_const
          (continuous_id.dist continuous_const)) hwcl
      linarith
    -- second bumping, inside `S`, outside the inner square
    set F := S ∩ {z | r₁ ≤ dist z P}
    have hFcl : IsClosed F := hScl.inter (isClosed_le continuous_const
      (continuous_id.dist continuous_const))
    have hFc : IsCompact F := hSc.of_isClosed_subset hFcl inter_subset_left
    have hFS : F ≠ S := fun h => by
      have : X ∈ F := by rw [h]; exact hXS
      exact absurd this.2 (not_le.2 hXd)
    have hwF : w ∈ F := ⟨hwS, show r₁ ≤ dist w P by rw [hwd]; exact hr₁₂.le⟩
    obtain ⟨T, hTc, hTconn, hTF, hwT, u, huT, hucl⟩ :=
      exists_continuum_bump_compact hSconn hFc inter_subset_left hFS hwF
    refine ⟨T, hTconn, hTc, hTF.trans inter_subset_left,
      fun z hz => ⟨(hTF hz).2, (hSK (hTF hz).1).2⟩, ⟨u, huT, ?_⟩, ⟨w, hwT, hwd⟩⟩
    have h1 : r₁ ≤ dist u P := (hTF huT).2
    have h2 : dist u P ≤ r₁ := by
      have hsub : S \ F ⊆ {z | dist z P ≤ r₁} := fun z hz => by
        by_contra h
        exact hz.2 ⟨hz.1, show r₁ ≤ dist z P from le_of_lt (not_le.1 h)⟩
      exact closure_minimal hsub (isClosed_le (continuous_id.dist continuous_const)
        continuous_const) hucl
    linarith
  choose t ht using hstep
  refine ⟨r₁, r₂, hr₁, hr₁₂, t, ?_, fun n => ?_⟩
  · intro m n hmn
    refine disjoint_left.2 fun z hzm hzn => hmn ?_
    have h1 := (ht m).2.2.1 hzm
    have h2 := (ht n).2.2.1 hzn
    obtain ⟨X, -, -, -, hSX⟩ := (f m).2
    obtain ⟨Y, -, -, -, hSY⟩ := (f n).2
    have : (f m : Set Pt) = f n := by
      rw [hSX] at h1 ⊢; rw [hSY] at h2 ⊢
      rw [hcomp_eq h1, hcomp_eq h2]
    exact f.injective (Subtype.ext this)
  · obtain ⟨hc, hk, hsub, hd, h1, h2⟩ := ht n
    obtain ⟨X, -, -, -, hSX⟩ := (f n).2
    refine ⟨hc, hk, ?_, hd, h1, h2⟩
    intro z hz
    have := hsub hz
    rw [hSX] at this
    exact (connectedComponentIn_subset _ _ this).1
/-- A crossing continuum meets every intermediate square (intermediate value theorem). -/
theorem IsCrossA.exists_dist_eq {P : ℝ × ℝ} {r₁ r₂ ρ : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCrossA P r₁ r₂ K) (h1 : r₁ ≤ ρ) (h2 : ρ ≤ r₂) : ∃ z ∈ K, dist z P = ρ := by
  obtain ⟨a, ha, hda⟩ := hK.inner
  obtain ⟨b, hb, hdb⟩ := hK.outer
  obtain ⟨z, hz, hzd⟩ := hK.conn.isPreconnected.intermediate_value ha hb
    (continuous_id.dist continuous_const).continuousOn
    ⟨show dist a P ≤ ρ by linarith, show ρ ≤ dist b P by linarith⟩
  exact ⟨z, hz, hzd⟩

end HPC.Jones.Sector
