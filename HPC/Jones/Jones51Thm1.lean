import HPC.Jones.Jones55Core

/-!
# Batch 136, item C: Jones 1951, Theorem 1

F. B. Jones, *Certain homogeneous unicoherent indecomposable continua*, Proc. AMS 2 (1951),
855–859, Theorem 1: a homogeneous, hereditarily unicoherent, compact metric continuum is
indecomposable.

**The proof is not Jones's.** Jones builds the sets `U`, `H`, `N_o`, shows that the translates of
`H` form an u.s.c. decomposition `G`, passes to the decomposition space `M′`, and applies Whyburn
(6.21) in `M′` together with the hereditary unicoherence of `M′`. Here the decomposition space is
not needed. By Jones 1955 Theorem 1 (b) (`mem_Lset_iff_Lset_eq`, proved in `Jones55Core` from the
Effros theorem) the sets `L_x` partition `X` into closed sets. If `X` is decomposable, there are
`a`, `b` with `L_a ≠ L_b`. Let `J` be a subcontinuum irreducible about `{a, b}`; by hereditary
unicoherence (on `M` itself) `J` lies in every continuum containing `a` and `b`. `J` is connected,
so it is not covered by the disjoint closed sets `L_a`, `L_b`: some `c ∈ J` lies in a third element.
Then `a`, `b ∈ M − L_c = U_c`, and claim (5) of Jones 1955 (no point cuts two points of `U_c`;
Bing's Corollary 2 and homogeneity) gives a continuum through `a`, `b` missing `c`. It contains
`J ∋ c`: a contradiction.
-/

namespace HPC.Jones

open Set Topology Filter Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- In a hereditarily unicoherent space, two subcontinua with a common point meet in a
subcontinuum. -/
theorem isContinuum_inter_of_hu (hhu : HPC.Plane.IsHereditarilyUnicoherent (univ : Set X))
    {A B : Set X} (hA : Fold.Q78.IsContinuum A) (hB : Fold.Q78.IsContinuum B)
    (hAB : (A ∩ B).Nonempty) : Fold.Q78.IsContinuum (A ∩ B) := by
  refine ⟨hA.1.inter_right hB.1.isClosed, ?_⟩
  have hU : Fold.Q78.IsContinuum (A ∪ B) :=
    ⟨hA.1.union hB.1, IsConnected.union hAB hA.2 hB.2⟩
  by_cases hnt : (A ∪ B).Nontrivial
  · exact hhu (A ∪ B) (subset_univ _) hU hnt A B hA hB rfl
  · obtain ⟨z, hz⟩ := hAB
    have hsub : (A ∪ B).Subsingleton := not_nontrivial_iff.mp hnt
    have he : A ∩ B = {z} := by
      refine eq_singleton_iff_unique_mem.mpr ⟨hz, fun w hw => ?_⟩
      exact hsub (Or.inl hw.1) (Or.inl hz.1)
    rw [he]
    exact isConnected_singleton

end HPC.Jones
