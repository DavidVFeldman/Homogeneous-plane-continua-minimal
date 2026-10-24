import HPC.Hagopian.H76HalfRay
import HPC.Hagopian.H76Adapt
import HPC.Moore.M25Plane
import HPC.Plane.Surgery91
import HPC.Jones.Jones49EArc

/-!
# Batch 165, item A.4: T7 by the crossing argument

`hagopian76_T7_aux` (commission 165 §1, step 4): a thin collar rectangle over `[a, b]` lies in
`π[U]` (`U` open, `U ⊇ E`, so `U` is saturated and `π[U]` is open), and in every thinner rectangle
the crossing lemma, applied to `K = {z : F(z) ∈ π[M]}`, gives `I₂`. A connected part of `K` from the
bottom to the top would pull back (`preimage_pi_isContinuum_aux`) to a continuum of `M` meeting `E`
and missing both end sets, hence inside `E` (`no_hair_aux`), whereas it reaches the top edge.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section T7

variable {M : Set Pt}

/-- A positive height below a compact set of the closed upper half plane missing the axis. -/
theorem exists_height_below {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q) (hQ0 : ∀ z ∈ Q, 0 < z.2) :
    ∃ c > 0, c ≤ 1 ∧ ∀ z ∈ Q, c < z.2 := by
  rcases Q.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, le_rfl, fun z hz => by rw [h] at hz; exact hz.elim⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hQ.exists_isMinOn h continuous_snd.continuousOn
    have h0 := hQ0 z₀ hz₀
    refine ⟨min 1 (z₀.2 / 2), lt_min one_pos (by linarith), min_le_left _ _, fun z hz => ?_⟩
    have := isMinOn_iff.1 hmin z hz
    have := min_le_right 1 (z₀.2 / 2)
    linarith

variable [CompactSpace M] [ConnectedSpace M]

end T7

end HPC.Hagopian
