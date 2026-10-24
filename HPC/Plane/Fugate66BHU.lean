import HPC.Plane.Fugate66

/-!
# Batch 101: the union of two hereditarily unicoherent continua along a continuum

The consequence of Miller's theorem that Fugate's Theorem 1 uses (`hu_union_of_snakeLike` in
`Fugate66B.lean`), proved directly: if `A`, `B` are hereditarily unicoherent continua and `A ∩ B`
is connected, then `A ∪ B` is hereditarily unicoherent. The key step
(`isPreconnected_inter_of_hu`) is that every subcontinuum `H` of `A ∪ B` meets `A` in a connected
set; it needs only that `B` is hereditarily unicoherent, and uses the separation theorem for
compact sets (`exists_closed_split_of_no_connected`, Moore's Theorem 44 form).
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- **Separation of two closed sets in a compact set** (Moore, Theorem 44): if no preconnected
subset of the compact set `K` meets both of the closed sets `P, Q ⊆ K`, then `K` is the union of
two disjoint closed sets, one containing `P` and the other containing `Q`. -/
theorem exists_closed_split_of_no_connected {K P Q : Set S} (hK : IsCompact K)
    (hP : IsClosed P) (hQ : IsClosed Q) (hPK : P ⊆ K) (hQK : Q ⊆ K)
    (hno : ∀ Z ⊆ K, IsPreconnected Z → (Z ∩ P).Nonempty → (Z ∩ Q).Nonempty → False) :
    ∃ H L : Set S, IsClosed H ∧ IsClosed L ∧ H ∪ L = K ∧ Disjoint H L ∧ P ⊆ H ∧ Q ⊆ L := by
  classical
  have hsplit : ∀ p ∈ P, ∃ H L : Set S, IsCompact H ∧ IsCompact L ∧ H ∪ L = K ∧ Disjoint H L ∧
      p ∈ H ∧ H ⊆ Qᶜ := fun p hp =>
    exists_clopen_split hK (hPK hp) hQ.isOpen_compl fun Z hZ hZK hpZ z hzZ hzQ =>
      hno Z hZK hZ ⟨p, hpZ, hp⟩ ⟨z, hzZ, hzQ⟩
  choose! Hp Lp hHc hLc hHL hdisj hpH hHQ using hsplit
  obtain ⟨t, hcov⟩ := (hP.isCompact).elim_finite_subcover (fun p : P => (Lp p)ᶜ)
    (fun p => (hLc p p.2).isClosed.isOpen_compl)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, fun h => Set.disjoint_left.mp (hdisj p hp) (hpH p hp) h⟩)
  refine ⟨⋃ p ∈ t, Hp p, K ∩ ⋂ p ∈ t, Lp p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact t.finite_toSet.isClosed_biUnion fun p _ => (hHc p p.2).isClosed
  · exact hK.isClosed.inter (isClosed_biInter fun p _ => (hLc p p.2).isClosed)
  · apply Subset.antisymm
    · refine union_subset (iUnion₂_subset fun p _ => ?_) inter_subset_left
      rw [← hHL p p.2]; exact subset_union_left
    · intro x hxK
      by_cases hx : ∃ p ∈ t, x ∈ Hp p
      · obtain ⟨p, hp, hx⟩ := hx
        exact Or.inl (mem_iUnion₂.mpr ⟨p, hp, hx⟩)
      · push_neg at hx
        refine Or.inr ⟨hxK, mem_iInter₂.mpr fun p hp => ?_⟩
        rw [← hHL p p.2] at hxK
        exact hxK.resolve_left (hx p hp)
  · rw [Set.disjoint_left]
    rintro x hx ⟨-, hx'⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    exact Set.disjoint_left.mp (hdisj p p.2) hxp (mem_iInter₂.mp hx' p hp)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hcov hx)
    refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    have hxK := hPK hx
    rw [← hHL p p.2] at hxK
    exact hxK.resolve_right hxp
  · intro x hx
    refine ⟨hQK hx, mem_iInter₂.mpr fun p _ => ?_⟩
    have hxK := hQK hx
    rw [← hHL p p.2] at hxK
    exact hxK.resolve_left fun h => hHQ p p.2 h hx

omit [CompactSpace S] in
/-- A closed set that is not preconnected splits into two disjoint nonempty closed pieces. -/
theorem exists_closed_pieces_of_not_isPreconnected {X : Set S} (hX : IsClosed X)
    (h : ¬ IsPreconnected X) :
    ∃ P Q : Set S, IsClosed P ∧ IsClosed Q ∧ P ∪ Q = X ∧ Disjoint P Q ∧ P.Nonempty ∧
      Q.Nonempty := by
  rw [isPreconnected_closed_iff] at h
  push_neg at h
  obtain ⟨t, t', ht, ht', hXt, h1, h2, h3⟩ := h
  refine ⟨X ∩ t, X ∩ t', hX.inter ht, hX.inter ht', ?_, ?_, h1, h2⟩
  · rw [← inter_union_distrib_left]; exact inter_eq_left.mpr hXt
  · rw [Set.disjoint_left]
    rintro x ⟨hxX, hxt⟩ ⟨-, hxt'⟩
    exact (eq_empty_iff_forall_notMem.mp h3) x ⟨hxX, hxt, hxt'⟩

end HPC.Plane
