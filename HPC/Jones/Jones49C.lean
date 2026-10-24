import HPC.Jones.Jones49B
import HPC.Jones.Jones49CMoore

/-!
# Batch 151 skeleton: crossing continua; Moore 1922 Theorem 4 (local form and both directions);
complementary domains of plane continua; Whyburn 1939 (6.22) in the §14 form

Save as `HPC/Jones/Jones49C.lean` (splitting under `HPC/Jones/` is expected); add
`import HPC.Jones.Jones49C` at the end of `HPC.lean`. Every `sorry` is a work item. Shapes may be
adjusted, each change recorded at the statement and in the report.

Sources (page images, 150–200 dpi): Moore 1922 pp. 235–237 (`doc/sources/moore1922.pdf`); Whyburn,
*Semi-locally-connected sets*, Amer. J. Math. 61 (1939), §14, pp. 747–749
(`doc/sources/whyburn1939.pdf`). Whyburn's §14 proof begins: "Let `R` be a complementary domain of
`M`. Clearly we may suppose `R` bounded, since an inversion of the plane can be used to throw `R`
into a bounded region complementary to the image of `M`. We shall show that `R` has property `S`
… If this is not so, there exists a sequence of points `p₁, p₂, …` of `R` converging to a point
`p ∈ M` and an `ε > 0` such that for no `i, j` can `pᵢ` and `pⱼ` be joined by a connected subset of
`R` of diameter `< 4ε`."
-/

namespace HPC.Jones

open Set Topology Metric Filter HPC.Plane

/-! ## Continua crossing an annulus -/

/-! ## Moore 1922 Theorem 4 -/

/-! ## Complementary domains of plane continua -/

/-- The boundary of every complementary domain of a plane continuum is a continuum (bounded or
unbounded domain). Immediate from Brouwer's boundary theorem `HPC.Moore.brouwer_boundary` (for closed
connected `M`, by unicoherence of the plane). -/
theorem isConnected_frontier_complDomain {M : Set Pt} (hM : IsCompact M) (hMc : IsConnected M)
    {x : Pt} (hx : x ∉ M) : IsConnected (frontier (connectedComponentIn Mᶜ x)) :=
  HPC.Moore.brouwer_boundary hM.isClosed hMc ⟨x, hx, rfl⟩

/-! ## Whyburn 1939 (6.22), in the form §14 uses -/

/-- **(6.22), §14 form** (p. 747: "Then by (6.22) there exists a `δ > 0` and a component `N` of
`M − M·V_δ(p)` which contains `M − M·V_ε(p)`"). For a compact semi-locally-connected continuum `M`
and a non-cut point `p`, stated in the subtype `M`. -/
theorem whyburn39_6_22_sec14 {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    (hS : ∀ z : X, SemiLocConnAt z) {p : X} (hp : IsConnected ({p}ᶜ : Set X)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ c ∈ (ball p δ)ᶜ,
      (ball p ε)ᶜ ⊆ connectedComponentIn (ball p δ)ᶜ c := by
  classical
  obtain ⟨q, hq⟩ := hp.nonempty
  have hqp : q ≠ p := hq
  have hap := isAposyndetic_of_semiLocConn hS
  -- for every `a ≠ p`: a continuum `L a ∋ q` missing `p`, and an open `U a ∋ a` inside it
  have hex : ∀ a : X, a ≠ p → ∃ L U : Set X, IsCompact L ∧ IsPreconnected L ∧ q ∈ L ∧ p ∉ L ∧
      IsOpen U ∧ a ∈ U ∧ U ⊆ L := by
    intro a ha
    have hcomp : connectedComponentIn ({p}ᶜ : Set X) q = {p}ᶜ :=
      hp.isPreconnected.connectedComponentIn hq
    obtain ⟨N, hN, hqN, haN, hpN⟩ := whyburn_6_2 hS hqp (b := a) (by rw [hcomp]; exact ha)
    obtain ⟨H, U, hH, hU, haU, hUH, hpH⟩ := hap a p ha
    exact ⟨N ∪ H, U, hN.1.union hH.1, hN.2.isPreconnected.union a haN (hUH haU)
      hH.2.isPreconnected, Or.inl hqN, fun h => h.elim hpN hpH, hU, haU, hUH.trans
      subset_union_right⟩
  choose! L U hLc hLp hqL hpL hUo haU hUL using hex
  have hSc : IsCompact (ball p ε)ᶜ := isOpen_ball.isClosed_compl.isCompact
  have hne : ∀ a ∈ (ball p ε)ᶜ, a ≠ p := fun a ha h => ha (h ▸ mem_ball_self hε)
  obtain ⟨F, hFcov⟩ := hSc.elim_nhds_subcover' (fun a ha => U a)
    (fun a ha => (hUo a (hne a ha)).mem_nhds (haU a (hne a ha)))
  set W := ⋃ a ∈ F, L a
  have hWc : IsClosed W := F.finite_toSet.isClosed_biUnion fun a _ =>
    (hLc a (hne a a.2)).isClosed
  have hpW : p ∉ W := by
    simp only [W, mem_iUnion, not_exists]
    exact fun a _ => hpL a (hne a a.2)
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWc.isOpen_compl p hpW
  have hqp' : 0 < dist q p := dist_pos.2 hqp
  set δ := min (min (ε / 2) r) (dist q p / 2)
  have hδ0 : 0 < δ := lt_min (lt_min (half_pos hε) hr) (half_pos hqp')
  have hδr : δ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ < ε := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  have hqδ : q ∈ (ball p δ)ᶜ := by
    simp only [mem_compl_iff, mem_ball, not_lt]
    exact (min_le_right _ _).trans (half_le_self hqp'.le)
  refine ⟨δ, hδ0, hδε, q, hqδ, fun z hz => ?_⟩
  have hz' := hFcov hz
  simp only [mem_iUnion] at hz'
  obtain ⟨a, ha, hza⟩ := hz'
  have hLW : L a ⊆ (ball p δ)ᶜ := fun w hw hwb => by
    have : w ∈ W := mem_biUnion ha hw
    exact hrW (ball_subset_ball hδr hwb) this
  exact (hLp a (hne a a.2)).subset_connectedComponentIn (hqL a (hne a a.2)) hLW
    (hUL a (hne a a.2) hza)

end HPC.Jones
