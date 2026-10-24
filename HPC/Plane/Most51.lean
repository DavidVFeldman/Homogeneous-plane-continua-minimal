import Mathlib
import HPC.Plane.PseudoArc51
import HPC.Plane.Monotone51

/-!
# Bing, *Concerning hereditarily indecomposable continua*, §3: most compact continua are pseudo-arcs

Skeleton for batch 90 (save as `HPC/Plane/Most51.lean`; add `import HPC.Plane.Most51` to the root
`HPC.lean`). Statements only; every proof is a `sorry` work item. Shapes may be adjusted with the
change recorded; `theorem2_HIC` keeps its conclusion (if `exists_tame_chain_near` stays open,
`theorem2_HIC` is proved from it and the dependence is recorded).

`IsPseudoArc`, `IsSnakeLike`, `IsEpsChain`, `IsHereditarilyIndecomposable` are from
`Snake51.lean`, `EndPoints51.lean`, `PseudoArc51.lean`.

**Batch 90 delivery.** All statements keep their skeleton shapes. Proved: `isClosed_cont`, the
`CompleteSpace` instance, `isClosed_notCoverable`, `isClosed_separated`, `isClosed_degenerate`,
`isGδ_pseudoArcs`, `exists_pseudoArc_in_tameChain`, `dense_pseudoArcs_of` and `theorem2_HIC_of`.
The hyperspace arguments use Mathlib's Vietoris description of the Hausdorff-metric topology on
`NonemptyCompacts` (`isOpen_subsets_of_isOpen`, `isOpen_inter_nonempty_of_isOpen`,
`isCompact_subsets_of_isCompact`, `isCompact_biUnion_coe_of_isCompact`). The pseudo-arc in a tame
chain is batch 84's planar construction started from `m` standard rectangles
(`HPC/Plane/DescrM.lean`), placed in the `(e₁, e₂)`-plane of `E` and carried by the homeomorphism
of the tame chain (the plane route of COMMISSION-batch90.md §3.6, not a generalisation of
`real_step`). Completeness of `E` is not used by any of the proofs.

**What is now proved, and where (batch 111).** The batch-90 open geometric lemma
`exists_tame_chain_near` (a tame chain near every continuum, i.e. a *homeomorphism of `E`* carrying
the standard boxes onto the links) and its two consequences `dense_pseudoArcs`, `theorem2_HIC` of
this file were deleted in batch 111 (`LEDGER.md` §2): the homeomorphism is more than
`exists_pseudoArc_in_tameChain` uses, and the batch-90 obstruction was an obstruction to that
excess. `GeomLemma E` (that conclusion as a hypothesis), `dense_pseudoArcs_of` and
`theorem2_HIC_of` stay here, proved. The weaker threaded form `GeomLemma'` is in `Band.lean`
(batch 109, with `dense_pseudoArcs_of'`, `theorem2_HIC_of'`).
* *Plane*: `GeomLemma'` is proved for `finrank ℝ E = 2` (`geomLemma'_of_finrank_two`), hence
  Pacific Theorem 2 (`theorem2_HIC_plane`) and Duke Theorem 2 (`theorem2_1951_plane`) in the plane,
  all in `HPC/Plane/LatticeCycle.lean` (batches 109–110).
* *General `E`*: `geomLemma'_of_two_le_rank` (every real inner product space of dimension `≥ 2`)
  is proved in batch 113 in `HPC/Plane/CubeCycle.lean`, together with `dense_pseudoArcs`,
  `theorem2_HIC` (same statements as before) and `theorem2_1951`. (Batch 116 note: it was open
  from batch 111 to batch 113.)
Partial batch-90 results towards the former statement (tame chains in `E`, shears, the tube around
an unbent arc, the case of points and segments, Bing's broken line) are in the archive,
`HPC/Archive/Most51Geom.lean`.
-/

namespace HPC.Plane

open Set TopologicalSpace Metric Filter Topology

/-! ### The hyperspace of compact continua -/

variable {S : Type*} [MetricSpace S]

namespace Most

/-- A nonempty compact set that is not connected lies in the union of two disjoint open sets,
each meeting it. -/
theorem exists_open_separation {K : Set S} (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ¬ IsConnected K) :
    ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ K ⊆ U ∪ V ∧ (K ∩ U).Nonempty ∧
      (K ∩ V).Nonempty := by
  have hpc : ¬ IsPreconnected K := fun h => hc ⟨hne, h⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpc
  push_neg at hpc
  obtain ⟨u, v, hu, hv, hcov, hdisj, hnu, hnv⟩ := hpc
  have hd : Disjoint (K ∩ u) (K ∩ v) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← hdisj]
    ext z; simp only [mem_inter_iff]; tauto
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    normal_separation (hK.isClosed.inter hu) (hK.isClosed.inter hv) hd
  refine ⟨U, V, hU, hV, hUV, fun z hz => ?_, ?_, ?_⟩
  · rcases hcov hz with h | h
    · exact Or.inl (hKU ⟨hz, h⟩)
    · exact Or.inr (hKV ⟨hz, h⟩)
  · obtain ⟨z, hz, hzv⟩ := not_subset.mp hnv
    have hzu : z ∈ u := (hcov hz).resolve_right hzv
    exact ⟨z, hz, hKU ⟨hz, hzu⟩⟩
  · obtain ⟨z, hz, hzu⟩ := not_subset.mp hnu
    have hzv : z ∈ v := (hcov hz).resolve_left hzu
    exact ⟨z, hz, hKV ⟨hz, hzv⟩⟩

end Most

/-- The continua form a closed subset of the hyperspace (a Hausdorff limit of connected compacta
is connected); hence `Cont S` is complete when `S` is. -/
theorem isClosed_cont : IsClosed {K : NonemptyCompacts S | IsConnected (K : Set S)} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro K hK
  obtain ⟨U, V, hU, hV, hUV, hcov, hKU, hKV⟩ :=
    Most.exists_open_separation K.isCompact K.nonempty hK
  refine ⟨{L | (L : Set S) ⊆ U ∪ V} ∩ {L | ((L : Set S) ∩ U).Nonempty} ∩
    {L | ((L : Set S) ∩ V).Nonempty}, ?_, ?_, ⟨⟨hcov, hKU⟩, hKV⟩⟩
  · rintro L ⟨⟨hLcov, hLU⟩, hLV⟩ hLc
    obtain ⟨z, -, hzU, hzV⟩ := hLc.isPreconnected U V hU hV hLcov hLU hLV
    exact Set.disjoint_left.mp hUV hzU hzV
  · exact ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV)

namespace Most

/-- A Hausdorff limit of connected compacta is connected. -/
theorem isConnected_of_tendsto {P : ℕ → NonemptyCompacts S} {P₀ : NonemptyCompacts S}
    (hP : Tendsto P atTop (𝓝 P₀)) (h : ∀ n, IsConnected (P n : Set S)) :
    IsConnected (P₀ : Set S) :=
  isClosed_cont.mem_of_tendsto hP (Eventually.of_forall h)

/-- The distance from a point to a set is jointly continuous for the Hausdorff metric. -/
theorem tendsto_infDist {z : ℕ → S} {z₀ : S} {P : ℕ → NonemptyCompacts S}
    {P₀ : NonemptyCompacts S} (hz : Tendsto z atTop (𝓝 z₀)) (hP : Tendsto P atTop (𝓝 P₀)) :
    Tendsto (fun n => infDist (z n) (P n : Set S)) atTop (𝓝 (infDist z₀ (P₀ : Set S))) := by
  set F : S × NonemptyCompacts S → ℝ := fun p => infDist p.1 (p.2 : Set S) with hF
  have hc : Continuous F := lipschitz_infDist.continuous
  have h2 : Tendsto (fun n => (z n, P n)) atTop (𝓝 (z₀, P₀)) := hz.prodMk_nhds hP
  have h3 : Tendsto (F ∘ fun n => (z n, P n)) atTop (𝓝 (F (z₀, P₀))) :=
    (hc.tendsto (z₀, P₀)).comp h2
  exact h3

/-- A limit of points of converging compacta lies in the limit compactum. -/
theorem mem_of_tendsto {z : ℕ → S} {z₀ : S} {P : ℕ → NonemptyCompacts S}
    {P₀ : NonemptyCompacts S} (hz : Tendsto z atTop (𝓝 z₀)) (hP : Tendsto P atTop (𝓝 P₀))
    (h : ∀ n, z n ∈ (P n : Set S)) : z₀ ∈ (P₀ : Set S) := by
  have hc := tendsto_infDist hz hP
  have h0 : (fun n => infDist (z n) (P n : Set S)) = fun _ => 0 :=
    funext fun n => infDist_zero_of_mem (h n)
  rw [h0] at hc
  have : infDist z₀ (P₀ : Set S) = 0 := tendsto_nhds_unique hc tendsto_const_nhds
  rw [← P₀.isCompact.isClosed.closure_eq, mem_closure_iff_infDist_zero P₀.nonempty]
  exact this

end Most

namespace Most

end Most

/-! ### Density: a pseudo-arc near every continuum -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Most

end Most

end HPC.Plane
