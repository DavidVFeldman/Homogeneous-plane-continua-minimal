import HPC.Jones.Jones75Rev

/-!
# Jones 1975 I (batch 189), part 5: (L), no backtracking near an arc of a line

Commission 189 §5. The argument of the commission (Effros, (O), and the intermediate value theorem)
uses only a coordinate `X` that is continuous near the base arc `ℓ[0, 1]` and equal to the
parameter on it. It is therefore proved first for a `JonesSetting` and an abstract coordinate
(`JonesSetting.no_backtrack`), with the strip measured metrically: `ℓ v` lies within `η` of the base
point `ℓ (X (ℓ v))`. The collar form (`no_backtrack_in_collar`) follows, for a plane continuum and a
collar `F` of the base arc (`IsCollar`), with `X` the first collar coordinate and the strip
`F([κ, 1 − κ] × (−η, η))` of the commission.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section General

variable {Y : Type*} [MetricSpace Y]

/-- A function continuous on a neighbourhood `W` of a compact set `K` is uniformly continuous near
`K`: points within `ε` of `K` lie in `W`, with values close to those at the nearby point of `K`. -/
theorem uniform_near_compact {K W : Set Y} {X : Y → ℝ} (hK : IsCompact K)
    (hKW : ∀ p ∈ K, W ∈ 𝓝 p) (hX : ContinuousOn X W) {c : ℝ} (hc : 0 < c) :
    ∃ ε > 0, ∀ p ∈ K, ∀ p', dist p p' < ε → p' ∈ W ∧ |X p' - X p| < c := by
  have hloc : ∀ p : K, ∃ r > 0, ball (p : Y) r ⊆ W ∧ ∀ y ∈ ball (p : Y) r, |X y - X p| < c / 2 := by
    rintro ⟨p, hp⟩
    have hW := hKW p hp
    have hcont : ContinuousAt X p := hX.continuousAt hW
    obtain ⟨r₁, hr₁, hr₁W⟩ := Metric.mem_nhds_iff.1 hW
    obtain ⟨r₂, hr₂, hr₂X⟩ := Metric.continuousAt_iff.1 hcont (c / 2) (half_pos hc)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁W,
      fun y hy => ?_⟩
    have := hr₂X (lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _))
    rwa [Real.dist_eq] at this
  choose r hr hrW hrX using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (c := fun p : K => ball (p : Y) (r p))
    (fun _ => isOpen_ball) (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun p hp p' hpp' => ?_⟩
  obtain ⟨i, hi⟩ := hleb p hp
  have h1 : p ∈ ball (i : Y) (r i) := hi (mem_ball_self hδ)
  have h2 : p' ∈ ball (i : Y) (r i) := hi (by rw [mem_ball, dist_comm]; exact hpp')
  refine ⟨hrW i h2, ?_⟩
  have e1 := hrX i p' h2
  have e2 := hrX i p h1
  calc |X p' - X p| ≤ |X p' - X i| + |X p - X i| := by
        rw [abs_sub_comm (X p) (X i)]; exact abs_sub_le _ _ _
    _ < c / 2 + c / 2 := add_lt_add e1 e2
    _ = c := add_halves c

variable [CompactSpace Y]

end General

section Plane

variable {M : Set Pt} [CompactSpace M]

end Plane

end HPC.Hagopian
