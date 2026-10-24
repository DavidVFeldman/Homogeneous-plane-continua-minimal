import HPC.PseudoArc.Theorem13
import HPC.PseudoArc.T13Step

/-!
# Batch 83: nested intersections of continua

Topological support for `exists_irreducible` (`Theorem14.lean`): the intersection of a nonempty
chain (under inclusion) of compact connected sets in a compact metric space is compact and
connected.
-/

namespace HPC

open Set Metric Filter Topology

variable {X : Type*} [MetricSpace X]

namespace T14

/-- The intersection of a nonempty chain of compact preconnected sets is preconnected. -/
theorem isPreconnected_sInter_chain [CompactSpace X] {c : Set (Set X)} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) c) (hcpt : ∀ W ∈ c, IsCompact W) (hconn : ∀ W ∈ c, IsPreconnected W) :
    IsPreconnected (⋂₀ c) := by
  have hclosed : IsClosed (⋂₀ c) := isClosed_sInter fun W hW => (hcpt W hW).isClosed
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro u v hu hv hsub hdisj
  obtain ⟨δ, hδ, hδd⟩ := hdisj.exists_thickenings hu.isCompact hv
  have hopen : IsOpen (thickening δ u ∪ thickening δ v) :=
    isOpen_thickening.union isOpen_thickening
  haveI : Nonempty c := hne.to_subtype
  obtain ⟨⟨W, hWc⟩, hW⟩ : ∃ i : c, (i : Set X) ⊆ thickening δ u ∪ thickening δ v := by
    refine exists_subset_nhds_of_isCompact' (V := fun i : c => (i : Set X)) ?_
      (fun i => hcpt _ i.2) (fun i => (hcpt _ i.2).isClosed) ?_
    · intro i j
      rcases hch.total i.2 j.2 with h | h
      · exact ⟨i, le_rfl, h⟩
      · exact ⟨j, h, le_rfl⟩
    · intro x hx
      refine hopen.mem_nhds ?_
      have hx' : x ∈ ⋂₀ c := by
        rw [sInter_eq_iInter]; simpa using hx
      rcases hsub hx' with h | h
      · exact Or.inl (self_subset_thickening hδ _ h)
      · exact Or.inr (self_subset_thickening hδ _ h)
  have hLW : ⋂₀ c ⊆ W := sInter_subset_of_mem hWc
  rcases isPreconnected_iff_subset_of_disjoint.mp (hconn W hWc) _ _ isOpen_thickening
      isOpen_thickening hW (by
        rw [hδd.inter_eq]; exact inter_empty _) with h | h
  · left
    intro z hz
    rcases hsub hz with h' | h'
    · exact h'
    · exact absurd ⟨h (hLW hz), self_subset_thickening hδ _ h'⟩ (fun h2 => hδd.le_bot h2)
  · right
    intro z hz
    rcases hsub hz with h' | h'
    · exact absurd ⟨self_subset_thickening hδ _ h', h (hLW hz)⟩ (fun h2 => hδd.le_bot h2)
    · exact h'

/-! ## Transport of subsets of `M` by a self-homeomorphism of `M` -/

end T14

namespace Chain

variable {n : ℕ}

end Chain

namespace Description

variable {P Q : X} (Δ : Description X P Q)

end Description

end HPC
