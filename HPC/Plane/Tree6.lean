import HPC.Plane.Tree6Trim
import HPC.Plane.PolygonalPoly

/-!
# Batch 118: Bing 1951 (Duke), Theorem 6 relative to `PlaneFacts`

Installed from the batch-118 skeleton (`doc/batches/skeletons/Tree6.lean`); every item is proved,
with the shape changes recorded in `doc/batches/REPORT-batch118.md`. Auxiliary material:
`Tree6Local` (local structure near a polygon), `Tree6Arcs` (polygonal paths, loop erasure, simple
arcs), `Tree6Thread` (chains of arcs), `Tree6Trim` (threading through a circular chain).

The second and third paragraphs of Bing's proof (COMMISSION-batch117.md §1), relative to the
interface `PlaneFacts` (with its compact form of Janiszewski, batch 117). Plan:

1. polygonal arcs in connected open sets, and simple ones by loop erasure;
2. a simple closed polygon threaded through a circular chain of connected open sets
   (`p_1 p_2 ⋯ p_m p_1`, `p_i p_{i+1} ⊆ h_i`, consecutive arcs trimmed to meet only at `p_{i+1}`);
3. from `jct`: a connected unbounded set missing a simple closed polygon misses its interior;
   the interior is two-sided along the polygon — the points of the interior near an arc `α ⊆ Γ`
   lying in an open `h ⊇ α` form a connected set with `α` in its closure (`sides`);
4. **the point `q`** (Bing: "a boundary point of `h_1`, a boundary point of `h_2`, and a boundary
   point of `h_1 · h_2`" inside the curve), from `jct` and `janiszewski` — the one real use of the
   interface beyond `enclose`;
5. Theorem 6.
-/

namespace HPC.Plane

open Set Metric

open scoped Classical

/-! ### Polygonal arcs -/

/-- A **polygonal arc** from `p` to `q` with vertex list `w` (`p = w.head`, `q = w.getLast`): the
union of the segments between consecutive vertices. -/
def polyPathOf (w : List Pt) : Set Pt :=
  ⋃ i ∈ Finset.range (w.length - 1), segment ℝ (w.getD i 0) (w.getD (i + 1) 0)

/-- A **simple polygonal arc** from `p` to `q`: a vertex list with distinct vertices, `p ≠ q`,
adjacent segments meeting only at their common vertex, non-adjacent ones disjoint. -/
def IsSimplePolyArc (α : Set Pt) (p q : Pt) : Prop :=
  ∃ w : List Pt, 2 ≤ w.length ∧ w.Nodup ∧ w.head? = some p ∧ w.getLast? = some q ∧
    α = polyPathOf w ∧
    ∀ i j, i < j → j < w.length - 1 →
      segment ℝ (w.getD i 0) (w.getD (i + 1) 0) ∩ segment ℝ (w.getD j 0) (w.getD (j + 1) 0) ⊆
        if j = i + 1 then {w.getD j 0} else ∅

/-- The list form of a polygonal path is the vertex-function form `vpath`. -/
theorem polyPathOf_eq_vpath (w : List Pt) : polyPathOf w = vpath (fun i => w.getD i 0) w.length :=
  rfl

theorem getD_ofFn (v : ℕ → Pt) {n i : ℕ} (hi : i < n) :
    (List.ofFn (fun j : Fin n => v j)).getD i 0 = v i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem polyPathOf_ofFn (v : ℕ → Pt) (n : ℕ) :
    polyPathOf (List.ofFn (fun j : Fin n => v j)) = vpath v n := by
  rw [polyPathOf_eq_vpath, List.length_ofFn]
  exact vpath_congr fun i hi => getD_ofFn v hi

theorem head?_ofFn (v : ℕ → Pt) {n : ℕ} (hn : 1 ≤ n) :
    (List.ofFn (fun j : Fin n => v j)).head? = some (v 0) := by
  rw [List.head?_eq_getElem?]; simp [show 0 < n by omega]

theorem getLast?_ofFn (v : ℕ → Pt) {n : ℕ} (hn : 1 ≤ n) :
    (List.ofFn (fun j : Fin n => v j)).getLast? = some (v (n - 1)) := by
  rw [List.getLast?_eq_getElem?]; simp [show n - 1 < n by omega]

theorem getD_of_head? {w : List Pt} {p : Pt} (h : w.head? = some p) :
    w.getD 0 0 = p ∧ 1 ≤ w.length := by
  rw [List.head?_eq_getElem?] at h
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨?_, by omega⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, h2]

theorem getD_of_getLast? {w : List Pt} {q : Pt} (h : w.getLast? = some q) :
    w.getD (w.length - 1) 0 = q := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getD_eq_getElem?_getD, h]
  rfl

/-- **The list form and the vertex-function form of simple polygonal arcs agree.** -/
theorem isSimplePolyArc_iff {α : Set Pt} {p q : Pt} :
    IsSimplePolyArc α p q ↔
      ∃ (v : ℕ → Pt) (n : ℕ), IsSArc v n ∧ v 0 = p ∧ v (n - 1) = q ∧ α = vpath v n := by
  constructor
  · rintro ⟨w, hlen, hnd, hp, hq, rfl, hseg⟩
    refine ⟨fun i => w.getD i 0, w.length, ⟨hlen, ?_, ?_, ?_⟩, (getD_of_head? hp).1,
      getD_of_getLast? hq, rfl⟩
    · intro i j hij hj heq
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < w.length by omega),
        List.getElem?_eq_getElem hj, Option.getD_some] at heq
      have := (hnd.getElem_inj_iff).1 heq
      omega
    · intro i hi
      have := hseg i (i + 1) (by omega) (by omega)
      simpa using this
    · intro i j hij hj
      have := hseg i j (by omega) (by omega)
      rw [if_neg (by omega)] at this
      exact Set.disjoint_iff.2 this
  · rintro ⟨v, n, ⟨hn, hd, hc, hnc⟩, rfl, rfl, rfl⟩
    refine ⟨List.ofFn (fun j : Fin n => v j), by simp; omega, ?_, head?_ofFn v (by omega),
      getLast?_ofFn v (by omega), (polyPathOf_ofFn v n).symm, ?_⟩
    · rw [List.nodup_ofFn]
      intro a b hab
      rcases lt_trichotomy a.val b.val with h | h | h
      · exact absurd hab (hd _ _ h b.isLt)
      · exact Fin.ext h
      · exact absurd hab.symm (hd _ _ h a.isLt)
    · intro i j hij hj
      simp only [List.length_ofFn] at hj
      rw [getD_ofFn v (by omega), getD_ofFn v (by omega), getD_ofFn v (by omega),
        getD_ofFn v (by omega)]
      by_cases hji : j = i + 1
      · subst hji
        rw [if_pos rfl]
        exact hc i (by omega)
      · rw [if_neg hji]
        exact Set.disjoint_iff.1 (hnc i j (by omega) (by omega))

/-- A connected open set of the plane is polygonally connected. -/
theorem exists_polyPath_of_isConnected {h : Set Pt} (ho : IsOpen h) (hc : IsConnected h)
    {p q : Pt} (hp : p ∈ h) (hq : q ∈ h) :
    ∃ w : List Pt, w.head? = some p ∧ w.getLast? = some q ∧ polyPathOf w ⊆ h := by
  obtain ⟨v, n, hn, h0, h1, hsub⟩ := exists_vpath_of_isConnected ho hc hp hq
  exact ⟨_, h0 ▸ head?_ofFn v hn, h1 ▸ getLast?_ofFn v hn, (polyPathOf_ofFn v n).symm ▸ hsub⟩

/-- **Loop erasure**: a polygonal path from `p` to `q ≠ p` contains a simple polygonal arc from
`p` to `q`. -/
theorem exists_simplePolyArc_of_polyPath {w : List Pt} {p q : Pt} (hp : w.head? = some p)
    (hq : w.getLast? = some q) (hpq : p ≠ q) :
    ∃ α, IsSimplePolyArc α p q ∧ α ⊆ polyPathOf w := by
  obtain ⟨h0, hn⟩ := getD_of_head? hp
  obtain ⟨u, k, hu, hu0, hu1, husub⟩ :=
    exists_sarc_of_vpath (v := fun i => w.getD i 0) hn h0 (getD_of_getLast? hq) hpq
  exact ⟨vpath u k, isSimplePolyArc_iff.2 ⟨u, k, hu, hu0, hu1, rfl⟩, husub⟩

/-- A simple polygonal arc is compact and connected. -/
theorem IsSimplePolyArc.isContinuum {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) :
    Fold.Q78.IsContinuum α := by
  obtain ⟨v, n, hv, -, -, rfl⟩ := isSimplePolyArc_iff.1 h
  exact ⟨isCompact_vpath v n, isConnected_vpath v hv.1⟩

/-- The initial part of a simple polygonal arc up to a point of it is a simple polygonal arc
(or the point itself), and the final part from it likewise. -/
theorem IsSimplePolyArc.split {α : Set Pt} {p q : Pt} (h : IsSimplePolyArc α p q) {x : Pt}
    (hx : x ∈ α) (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ α₁ α₂, IsSimplePolyArc α₁ p x ∧ IsSimplePolyArc α₂ x q ∧ α₁ ∪ α₂ = α ∧ α₁ ∩ α₂ = {x} := by
  obtain ⟨v, n, hv, rfl, rfl, rfl⟩ := isSimplePolyArc_iff.1 h
  obtain ⟨u₁, k₁, u₂, k₂, hu₁, h10, h11, hu₂, h20, h21, hU, hI⟩ := hv.split hx hxp hxq
  exact ⟨vpath u₁ k₁, vpath u₂ k₂, isSimplePolyArc_iff.2 ⟨u₁, k₁, hu₁, h10, h11, rfl⟩,
    isSimplePolyArc_iff.2 ⟨u₂, k₂, hu₂, h20, h21, rfl⟩, hU, hI⟩

/-! ### Threading a simple closed polygon through a circular chain -/

/-! ### Consequences of `jct` -/

/-- A connected unbounded set missing a compact `J` misses `polyInterior J` (it lies in one
component of `Jᶜ`, which is unbounded; the interior is the union of the bounded ones). No
Jordan curve theorem is needed. (Compactness of `J` is not needed either.) -/
theorem polyInterior_disjoint_of_unbounded {J W : Set Pt} (hW : IsConnected W)
    (hWu : ¬ Bornology.IsBounded W) (hWJ : Disjoint W J) : Disjoint W (polyInterior J) := by
  rw [Set.disjoint_left]
  rintro x hxW ⟨-, hb⟩
  exact hWu (hb.subset (hW.isPreconnected.subset_connectedComponentIn hxW
    hWJ.subset_compl_right))

/-- The split of `jct` in a usable form: `polyInterior Γ = U`, with `Γᶜ = U ∪ V` (`U`, `V` open and
disjoint) and every point of `Γ` in the closure of both. -/
theorem PlaneFacts.split (hPF : PlaneFacts) {Γ : Set Pt} (hΓ : IsSimpleClosedPolygon Γ) :
    ∃ V : Set Pt, IsOpen (polyInterior Γ) ∧ IsOpen V ∧ Γᶜ = polyInterior Γ ∪ V ∧
      Disjoint (polyInterior Γ) V ∧ Bornology.IsBounded (polyInterior Γ) ∧
      frontier (polyInterior Γ) = Γ ∧ (∀ w ∈ Γ, w ∈ closure (polyInterior Γ)) ∧
      (∀ w ∈ Γ, w ∈ closure V) ∧ IsConnected V ∧ ¬ Bornology.IsBounded V := by
  obtain ⟨U, V, hU, hV, hJ, hd, hUc, hVc, hUb, hVb, hfU, hfV⟩ := hPF.jct Γ hΓ
  rw [polyInterior_eq_of_split hU hV hJ hd hUc hVc hUb hVb]
  exact ⟨V, hU, hV, hJ, hd, hUb, hfU, fun w hw => frontier_subset_closure (hfU.symm ▸ hw),
    fun w hw => frontier_subset_closure (hfV.symm ▸ hw), hVc, hVb⟩

/-! ### The point `q` -/

/-- A point of an open set lying in the closure of a component of it lies in that component
(components of open plane sets are open). -/
theorem mem_connectedComponentIn_of_mem_closure {O : Set Pt} (hO : IsOpen O) {x z : Pt}
    (hz : z ∈ O) (hzc : z ∈ closure (connectedComponentIn O x)) :
    z ∈ connectedComponentIn O x := by
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzc _ (hO.connectedComponentIn)
    (mem_connectedComponentIn hz)
  rw [connectedComponentIn_eq hy2, ← connectedComponentIn_eq hy1]
  exact mem_connectedComponentIn hz

/- **The batch-118 statement**, which held for arbitrary open `h₁`, `h₂` under the compact form of
Janiszewski (the sets `A := closure C ∩ frontier h₁`, `B := closure C ∩ frontier h₂` are compact
but need not be polygonal). Kept for the record:

theorem PlaneFacts.exists_theta_point (hPF : PlaneFacts) {Γ α₁ α₂ β : Set Pt} {p₁ p₂ p₃ : Pt}
    (hΓ : IsSimpleClosedPolygon Γ) (hdec : α₁ ∪ α₂ ∪ β = Γ)
    (h₁c : IsConnected α₁) (h₂c : IsConnected α₂) (hβc : IsConnected β)
    (hp₂ : p₂ ∈ α₁ ∩ α₂) (hp₃ : p₃ ∈ α₂ ∩ β) (hp₁ : p₁ ∈ β ∩ α₁)
    {h₁ h₂ V : Set Pt} (ho₁ : IsOpen h₁) (ho₂ : IsOpen h₂) (hoV : IsOpen V)
    (hα₁ : α₁ ⊆ h₁) (hα₂ : α₂ ⊆ h₂) (hβ : β ⊆ V) (hV : V ∩ h₁ ∩ h₂ = ∅) :
    ∃ q ∈ polyInterior Γ, q ∈ frontier h₁ ∧ q ∈ frontier h₂ ∧ q ∈ closure (h₁ ∩ h₂)
-/

/-- **Bing's point `q`** (batch 129 form: `h₁`, `h₂` are interiors of simple closed polygons `Γ₁`,
`Γ₂`, so that Janiszewski is only applied to polygonal sets). Let `Γ` be a simple closed polygon
decomposed into three connected sets `α₁` (containing `p₁`, `p₂`), `α₂` (containing `p₂`, `p₃`)
and `β` (containing `p₃`, `p₁`) with `α₁ ∪ α₂ ∪ β = Γ`. Let `h₁ = polyInterior Γ₁ ⊇ α₁`,
`h₂ = polyInterior Γ₂ ⊇ α₂` and an open `V ⊇ β` with `V ∩ h₁ ∩ h₂ = ∅`. Then some point `q` of the
interior `U` of `Γ` is a frontier point of `h₁`, of `h₂`, and lies in the closure of `h₁ ∩ h₂`.

Proof from `jct` and `janiszewski`, as in batch 118, with the sets
`A := Γ₁ ∩ closure (U ∩ h₁ ∩ h₂)` and `B := Γ₂ ∩ closure (U ∩ h₁ ∩ h₂)` in place of
`closure C ∩ frontier hᵢ` (`frontier hᵢ = Γᵢ` by `split`). They are polygonal
(`isPolygonal_inter_closure_polyInterior₃`), and so are `A ∪ Γ`, `B ∪ Γ`. By `sides`, there are
connected `S₁ ⊆ U ∩ h₁`, `S₂ ⊆ U ∩ h₂`, `S_V ⊆ U ∩ V` with `x ∈ S₁ ∩ S₂`, `y ∈ S₂ ∩ S_V`,
`z ∈ S₁ ∩ S_V`; `C` is the component of `U ∩ h₁ ∩ h₂` containing `x`. Suppose no `q`. Then
`A ∩ B = ∅`: a common point is in `closure U = U ∪ Γ`; in `U` it would be a `q`; on `Γ` it lies in
`β ⊆ V` (not in `α₁ ∪ α₂ ⊆ h₁ ∪ h₂`, being a frontier point of both), and `V` is open missing
`h₁ ∩ h₂`. So `(A ∪ Γ) ∩ (B ∪ Γ) = Γ` is connected.
* `A ∪ B ∪ Γ` separates `x` from `y`: the component of `x` in the complement lies in `U`, and in
  `C ∪ (closure C)ᶜ` (a point of `U ∩ closure C` outside `h₁` would be in `frontier h₁ = Γ₁` and in
  `closure (U ∩ h₁ ∩ h₂)`, i.e. in `A`; likewise for `h₂`), so in `C`; and `y ∉ C` (`y ∈ V`).
* `B ∪ Γ` does not separate `x` from `y` (`S₂` misses `B ⊆ Γ₂ = frontier h₂` and `Γ`).
* `janiszewski`: so `A ∪ Γ` separates `x` from `y`.
* But `S₁ ∪ S_V` is connected, contains `x`, `z` and `y`, and misses `Γ` and `A` (`A ⊆ Γ₁ =
  frontier h₁`, and `A ⊆ closure (h₁ ∩ h₂)` while `V` is open missing `h₁ ∩ h₂`). Contradiction.

The commission proposed `A := Γ₁ ∩ closure (h₁ ∩ h₂)`; with it the step "no `q` ⇒ `A ∩ B ⊆ Γ`" does
not go through for common points of `Γ₁`, `Γ₂` and `closure (h₁ ∩ h₂)` outside `closure U` (such
points are not candidates for `q`). Intersecting with `U` inside the closure removes them; the
polygonality lemma covers the three-fold intersection. -/
theorem PlaneFacts.exists_theta_point (hPF : PlaneFacts) {Γ α₁ α₂ β : Set Pt} {p₁ p₂ p₃ : Pt}
    (hΓ : IsSimpleClosedPolygon Γ) (hdec : α₁ ∪ α₂ ∪ β = Γ)
    (h₁c : IsConnected α₁) (h₂c : IsConnected α₂) (hβc : IsConnected β)
    (hp₂ : p₂ ∈ α₁ ∩ α₂) (hp₃ : p₃ ∈ α₂ ∩ β) (hp₁ : p₁ ∈ β ∩ α₁)
    {Γ₁ Γ₂ : Set Pt} (hΓ₁ : IsSimpleClosedPolygon Γ₁) (hΓ₂ : IsSimpleClosedPolygon Γ₂)
    {h₁ h₂ V : Set Pt} (hh₁ : h₁ = polyInterior Γ₁) (hh₂ : h₂ = polyInterior Γ₂) (hoV : IsOpen V)
    (hα₁ : α₁ ⊆ h₁) (hα₂ : α₂ ⊆ h₂) (hβ : β ⊆ V) (hV : V ∩ h₁ ∩ h₂ = ∅) :
    ∃ q ∈ polyInterior Γ, q ∈ frontier h₁ ∧ q ∈ frontier h₂ ∧ q ∈ closure (h₁ ∩ h₂) := by
  obtain ⟨E, hU, hE, hJ, hd, hUb, hfr, hfU, hfE, -⟩ := hPF.split hΓ
  obtain ⟨ho₁, -, -, hf₁, -⟩ := hPF.polyInterior_eq hΓ₁
  obtain ⟨ho₂, -, -, hf₂, -⟩ := hPF.polyInterior_eq hΓ₂
  rw [← hh₁] at ho₁ hf₁
  rw [← hh₂] at ho₂ hf₂
  set U := polyInterior Γ with hUdef
  have hsub₁ : α₁ ⊆ Γ := hdec ▸ subset_union_left.trans subset_union_left
  have hsub₂ : α₂ ⊆ Γ := hdec ▸ subset_union_right.trans subset_union_left
  have hsubβ : β ⊆ Γ := hdec ▸ subset_union_right
  obtain ⟨S₁, hS₁c, hS₁, hl₁⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsub₁ h₁c.isPreconnected ho₁ hα₁
  obtain ⟨S₂, hS₂c, hS₂, hl₂⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsub₂ h₂c.isPreconnected ho₂ hα₂
  obtain ⟨S₃, hS₃c, hS₃, hl₃⟩ :=
    sides_of_split hΓ hU hE hJ hd hfU hfE hsubβ hβc.isPreconnected hoV hβ
  have hmeet : ∀ {S S' : Set Pt} {w : Pt}, w ∈ Γ → (∃ r > 0, U ∩ ball w r ⊆ S) →
      (∃ r > 0, U ∩ ball w r ⊆ S') → (S ∩ S').Nonempty := by
    rintro S S' w hw ⟨r, hr, hrS⟩ ⟨r', hr', hrS'⟩
    obtain ⟨y, hyU, hy⟩ := Metric.mem_closure_iff.1 (hfU w hw) _ (lt_min hr hr')
    rw [dist_comm] at hy
    exact ⟨y, hrS ⟨hyU, (lt_min_iff.1 hy).1⟩, hrS' ⟨hyU, (lt_min_iff.1 hy).2⟩⟩
  obtain ⟨x, hx₁, hx₂⟩ := hmeet (hsub₁ hp₂.1) (hl₁ p₂ hp₂.1) (hl₂ p₂ hp₂.2)
  obtain ⟨y, hy₂, hy₃⟩ := hmeet (hsub₂ hp₃.1) (hl₂ p₃ hp₃.1) (hl₃ p₃ hp₃.2)
  obtain ⟨z, hz₁, hz₃⟩ := hmeet (hsub₁ hp₁.2) (hl₁ p₁ hp₁.2) (hl₃ p₁ hp₁.1)
  by_contra hno
  push_neg at hno
  -- basic facts
  have hUΓ : Disjoint U Γ := by
    rw [Set.disjoint_left]; intro u hu huΓ
    have : u ∈ U ∪ E := Or.inl hu
    rw [← hJ] at this; exact this huΓ
  have hVcl : Disjoint V (closure (h₁ ∩ h₂)) := by
    refine Disjoint.closure_right ?_ hoV
    rw [Set.disjoint_left]; intro u hu hu'
    have : u ∈ V ∩ h₁ ∩ h₂ := ⟨⟨hu, hu'.1⟩, hu'.2⟩
    rw [hV] at this; exact this
  have hfr₁ : Disjoint h₁ (frontier h₁) := by
    rw [ho₁.frontier_eq]; exact disjoint_sdiff_right
  have hfr₂ : Disjoint h₂ (frontier h₂) := by
    rw [ho₂.frontier_eq]; exact disjoint_sdiff_right
  have hO : IsOpen (U ∩ h₁ ∩ h₂) := (hU.inter ho₁).inter ho₂
  have hxO : x ∈ U ∩ h₁ ∩ h₂ := ⟨⟨(hS₁ hx₁).1, (hS₁ hx₁).2⟩, (hS₂ hx₂).2⟩
  set C := connectedComponentIn (U ∩ h₁ ∩ h₂) x with hC
  have hCO : C ⊆ U ∩ h₁ ∩ h₂ := connectedComponentIn_subset _ _
  have hCo : IsOpen C := hO.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hxO
  have hclO : closure (U ∩ h₁ ∩ h₂) ⊆ closure (h₁ ∩ h₂) :=
    closure_mono fun u hu => ⟨hu.1.2, hu.2⟩
  have hclOU : closure (U ∩ h₁ ∩ h₂) ⊆ U ∪ Γ := by
    refine (closure_mono fun u hu => hu.1.1).trans ?_
    rw [closure_eq_self_union_frontier, hfr]
  set A := Γ₁ ∩ closure (U ∩ h₁ ∩ h₂) with hA
  set B := Γ₂ ∩ closure (U ∩ h₁ ∩ h₂) with hB
  have hAp : IsPolygonal (A ∪ Γ) := by
    refine IsPolygonal.union ?_ hΓ.isPolygonal
    rw [hA, hh₁, hh₂]
    exact isPolygonal_inter_closure_polyInterior₃ hΓ.isPolygonal hΓ₁.isPolygonal hΓ₂.isPolygonal
  have hBp : IsPolygonal (B ∪ Γ) := by
    refine IsPolygonal.union ?_ hΓ.isPolygonal
    rw [hB, hh₁, hh₂, inter_right_comm]
    exact isPolygonal_inter_closure_polyInterior₃ hΓ.isPolygonal hΓ₂.isPolygonal hΓ₁.isPolygonal
  have hAB : A ∩ B = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro a ⟨⟨haΓ₁, haC⟩, haΓ₂, -⟩
    have ha₁ : a ∈ frontier h₁ := hf₁ ▸ haΓ₁
    have ha₂ : a ∈ frontier h₂ := hf₂ ▸ haΓ₂
    rcases hclOU haC with haU | haΓ
    · exact hno a haU ha₁ ha₂ (hclO haC)
    · rw [← hdec] at haΓ
      rcases haΓ with (h | h) | h
      · exact hfr₁.notMem_of_mem_left (hα₁ h) ha₁
      · exact hfr₂.notMem_of_mem_left (hα₂ h) ha₂
      · exact hVcl.notMem_of_mem_left (hβ h) (hclO haC)
  have hΓconn : IsConnected Γ := by
    rw [← hdec]
    exact (h₁c.union ⟨p₂, hp₂⟩ h₂c).union ⟨p₃, Or.inr hp₃.1, hp₃.2⟩ hβc
  have hinter : IsConnected ((A ∪ Γ) ∩ (B ∪ Γ)) := by
    rw [← inter_union_distrib_right, hAB, empty_union]; exact hΓconn
  -- points avoid the sets
  have hS₁A : S₁ ⊆ (A ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hfr₁.notMem_of_mem_left (hS₁ hu).2 (hf₁ ▸ h.1)
    · exact hUΓ.notMem_of_mem_left (hS₁ hu).1 h
  have hS₃A : S₃ ⊆ (A ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hVcl.notMem_of_mem_left (hS₃ hu).2 (hclO h.2)
    · exact hUΓ.notMem_of_mem_left (hS₃ hu).1 h
  have hS₂B : S₂ ⊆ (B ∪ Γ)ᶜ := by
    intro u hu hu'
    rcases hu' with h | h
    · exact hfr₂.notMem_of_mem_left (hS₂ hu).2 (hf₂ ▸ h.1)
    · exact hUΓ.notMem_of_mem_left (hS₂ hu).1 h
  -- `B ∪ Γ` does not separate `x` from `y`
  have hnB : ¬ SeparatesPts (B ∪ Γ) x y := by
    rintro ⟨-, -, h⟩
    exact h (hS₂c.subset_connectedComponentIn hx₂ hS₂B hy₂)
  -- `A ∪ B ∪ Γ` separates `x` from `y`
  have hsepAB : SeparatesPts ((A ∪ Γ) ∪ (B ∪ Γ)) x y := by
    have hyV : y ∈ V := (hS₃ hy₃).2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact hS₁A hx₁ h
      · exact hS₂B hx₂ h
    · rcases h with h | h
      · exact hS₃A hy₃ h
      · exact hS₂B hy₂ h
    · set K := connectedComponentIn ((A ∪ Γ) ∪ (B ∪ Γ))ᶜ x with hK
      have hKc : IsPreconnected K := isPreconnected_connectedComponentIn
      have hKsub : K ⊆ ((A ∪ Γ) ∪ (B ∪ Γ))ᶜ := connectedComponentIn_subset _ _
      have hxK : x ∈ K := mem_connectedComponentIn (fun h => by
        rcases h with h | h
        · exact hS₁A hx₁ h
        · exact hS₂B hx₂ h)
      have hKU : K ⊆ U := by
        have hKUE : K ⊆ U ∪ E := by
          rw [← hJ]; intro u hu huΓ; exact hKsub hu (Or.inl (Or.inr huΓ))
        rcases isPreconnected_iff_subset_of_disjoint.1 hKc U E hU hE hKUE
          (by rw [hd.inter_eq, inter_empty]) with h | h
        · exact h
        · exact absurd (h hxK) (hd.notMem_of_mem_left (hS₁ hx₁).1)
      have hKC : K ⊆ C := by
        have hcov : K ⊆ C ∪ (closure C)ᶜ := by
          intro u hu
          by_cases huc : u ∈ closure C
          · left
            have huO : u ∈ closure (U ∩ h₁ ∩ h₂) := closure_mono hCO huc
            have huA : u ∉ frontier h₁ := fun h' =>
              hKsub hu (Or.inl (Or.inl ⟨hf₁ ▸ h', huO⟩))
            have huB : u ∉ frontier h₂ := fun h' =>
              hKsub hu (Or.inr (Or.inl ⟨hf₂ ▸ h', huO⟩))
            have hu₁ : u ∈ h₁ := by
              by_contra h'
              exact huA (by rw [ho₁.frontier_eq]; exact ⟨closure_mono
                (hCO.trans fun v hv => hv.1.2) huc, h'⟩)
            have hu₂ : u ∈ h₂ := by
              by_contra h'
              exact huB (by rw [ho₂.frontier_eq]; exact ⟨closure_mono
                (hCO.trans fun v hv => hv.2) huc, h'⟩)
            exact mem_connectedComponentIn_of_mem_closure hO ⟨⟨hKU hu, hu₁⟩, hu₂⟩ huc
          · exact Or.inr huc
        rcases isPreconnected_iff_subset_of_disjoint.1 hKc C (closure C)ᶜ hCo
          isClosed_closure.isOpen_compl hcov (by
            refine eq_empty_of_forall_notMem ?_
            rintro u ⟨-, hu1, hu2⟩; exact hu2 (subset_closure hu1)) with h | h
        · exact h
        · exact absurd (subset_closure hxC) (h hxK)
      exact hVcl.notMem_of_mem_left hyV (subset_closure ⟨(hCO (hKC h)).1.2, (hCO (hKC h)).2⟩)
  -- so `A ∪ Γ` separates `x` from `y`
  have hsepA : SeparatesPts (A ∪ Γ) x y := by
    by_contra hnA
    exact hPF.janiszewski _ _ hAp hBp (Or.inl hinter) x y hnA hnB hsepAB
  -- but `S₁ ∪ S₃` joins them off `A ∪ Γ`
  obtain ⟨-, -, hfin⟩ := hsepA
  exact hfin ((hS₁c.union z hz₁ hz₃ hS₃c).subset_connectedComponentIn (Or.inl hx₁)
    (union_subset hS₁A hS₃A) (Or.inr hy₃))

/-! ### Theorem 6 -/

/-- Components of `d₀ ∩ d` for `d` in the cover. -/
def compFamily (d₀ : Set Pt) (D : Finset (Set Pt)) : Set (Set Pt) :=
  {h | ∃ d ∈ D, ∃ x ∈ d₀ ∩ d, h = connectedComponentIn (d₀ ∩ d) x}

/-- Members of `compFamily` are open, connected, and lie in `d₀` and in a member of `D`. -/
theorem compFamily_props {d₀ : Set Pt} {D : Finset (Set Pt)} (hd₀ : IsOpen d₀)
    (hopen : ∀ d ∈ D, IsOpen d) {h : Set Pt} (hh : h ∈ compFamily d₀ D) :
    IsOpen h ∧ IsConnected h ∧ h ⊆ d₀ := by
  obtain ⟨d, hd, x, hx, rfl⟩ := hh
  exact ⟨(hd₀.inter (hopen d hd)).connectedComponentIn, isConnected_connectedComponentIn_iff.2 hx,
    (connectedComponentIn_subset _ _).trans inter_subset_left⟩

/-- Two members of `compFamily` that are components of the same `d₀ ∩ d` and meet are equal. -/
theorem connectedComponentIn_eq_of_meet {F : Set Pt} {x y : Pt}
    (h : (connectedComponentIn F x ∩ connectedComponentIn F y).Nonempty) :
    connectedComponentIn F x = connectedComponentIn F y := by
  obtain ⟨z, hz1, hz2⟩ := h
  rw [connectedComponentIn_eq hz1, connectedComponentIn_eq hz2]

/-- **No three members of `compFamily` share a point** (distinct components of one `d₀ ∩ d` are
disjoint; components of three distinct `d`'s would give a triple point of `D`). -/
theorem compFamily_no_triple {d₀ : Set Pt} {D : Finset (Set Pt)}
    (hD : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    {h₁ h₂ h₃ : Set Pt} (hh₁ : h₁ ∈ compFamily d₀ D) (hh₂ : h₂ ∈ compFamily d₀ D)
    (hh₃ : h₃ ∈ compFamily d₀ D) (h12 : h₁ ≠ h₂) (h23 : h₂ ≠ h₃) (h13 : h₁ ≠ h₃) :
    h₁ ∩ h₂ ∩ h₃ = ∅ := by
  obtain ⟨e₁, he₁, x₁, -, rfl⟩ := hh₁
  obtain ⟨e₂, he₂, x₂, -, rfl⟩ := hh₂
  obtain ⟨e₃, he₃, x₃, -, rfl⟩ := hh₃
  apply eq_empty_of_forall_notMem
  rintro z ⟨⟨hz₁, hz₂⟩, hz₃⟩
  by_cases e12 : e₁ = e₂
  · subst e12; exact h12 (connectedComponentIn_eq_of_meet ⟨z, hz₁, hz₂⟩)
  by_cases e23 : e₂ = e₃
  · subst e23; exact h23 (connectedComponentIn_eq_of_meet ⟨z, hz₂, hz₃⟩)
  by_cases e13 : e₁ = e₃
  · subst e13; exact h13 (connectedComponentIn_eq_of_meet ⟨z, hz₁, hz₃⟩)
  have := hD e₁ he₁ e₂ he₂ e₃ he₃ e12 e23 e13
  have hz : z ∈ e₁ ∩ e₂ ∩ e₃ := ⟨⟨(connectedComponentIn_subset _ _ hz₁).2,
    (connectedComponentIn_subset _ _ hz₂).2⟩, (connectedComponentIn_subset _ _ hz₃).2⟩
  rw [this] at hz
  exact hz

/-- **A simple closed polygon through three connected open sets** (the case `m = 3` of
`exists_threaded`, which is all the proof of Theorem 6 needs: Bing's `h_3, …, h_m` are merged into
`V = h_3 ∪ ⋯ ∪ h_m`). -/
theorem exists_theta_polygon {A₀ A₁ A₂ : Set Pt} (ho₀ : IsOpen A₀) (ho₁ : IsOpen A₁)
    (ho₂ : IsOpen A₂) (hc₀ : IsConnected A₀) (hc₁ : IsConnected A₁) (hc₂ : IsConnected A₂)
    (h₀₁ : (A₀ ∩ A₁).Nonempty) (h₁₂ : (A₁ ∩ A₂).Nonempty) (h₂₀ : (A₂ ∩ A₀).Nonempty)
    (ht : A₀ ∩ A₁ ∩ A₂ = ∅) :
    ∃ (Γ α₀ α₁ α₂ : Set Pt) (p₀ p₁ p₂ : Pt), IsSimpleClosedPolygon Γ ∧ α₀ ∪ α₁ ∪ α₂ = Γ ∧
      IsConnected α₀ ∧ IsConnected α₁ ∧ IsConnected α₂ ∧
      p₁ ∈ α₀ ∩ α₁ ∧ p₂ ∈ α₁ ∩ α₂ ∧ p₀ ∈ α₂ ∩ α₀ ∧ α₀ ⊆ A₀ ∧ α₁ ⊆ A₁ ∧ α₂ ⊆ A₂ :=
  theta_polygon_of_three ho₀ ho₁ ho₂ hc₀ hc₁ hc₂ h₀₁ h₁₂ h₂₀ ht

/-- The complement of the interior of a simple closed polygon is connected and unbounded. -/
theorem PlaneFacts.compl_polyInterior (hPF : PlaneFacts) {J : Set Pt}
    (hJ : IsSimpleClosedPolygon J) :
    IsConnected (polyInterior J)ᶜ ∧ ¬ Bornology.IsBounded (polyInterior J)ᶜ := by
  obtain ⟨V, -, -, hJV, hd, -, -, -, hfV, hVc, hVb⟩ := hPF.split hJ
  have heq : (polyInterior J)ᶜ = V ∪ J := by
    ext x
    constructor
    · intro hx
      by_cases hxJ : x ∈ J
      · exact Or.inr hxJ
      · have : x ∈ polyInterior J ∪ V := hJV ▸ hxJ
        rcases this with h | h
        · exact absurd h hx
        · exact Or.inl h
    · rintro (h | h)
      · exact hd.notMem_of_mem_right h
      · intro h'
        have : x ∈ polyInterior J ∪ V := Or.inl h'
        rw [← hJV] at this
        exact this h
  rw [heq]
  exact ⟨hVc.subset_closure subset_union_left (union_subset subset_closure hfV),
    fun hb => hVb (hb.subset subset_union_left)⟩

/-- **No circular chain in `compFamily`** (the third paragraph): a circular chain `h_1, …, h_m`
of members, threaded by a simple closed polygon `Γ` (`exists_threaded`; the members are connected
open sets), with `β := α₃ ∪ ⋯ ∪ α_m ⊆ V := h₃ ∪ ⋯ ∪ h_m`, `V ∩ h₁ ∩ h₂ = ∅` (no triple); the
interior of `Γ` lies in `d₀` (`polyInterior_disjoint_of_unbounded` for `W = d₀ᶜ`, which is
connected and unbounded by `jct` and misses `Γ ⊆ d₀`); `exists_theta_point` gives `q ∈ d₀`, so
`q ∈ d` for some `d ∈ D`; `q ∈ closure (h₁ ∩ h₂)` makes `d` meet `d_a ∩ d_b` (`h₁ ⊆ d_a`,
`h₂ ⊆ d_b`, `a ≠ b`), so `d ∈ {d_a, d_b}`; but then `q ∈ d₀ ∩ d_a` is in the closure of the
component `h₁` of that open set and hence in `h₁`, contradicting `q ∈ frontier h₁`.
(Formalized with the three sets `h₁`, `h₂`, `V`, `V` connected as the union of the chain
`h₃, …, h_m`, and `exists_theta_polygon`.) -/
theorem compFamily_no_circular (hPF : PlaneFacts) {J : Set Pt} (hJ : IsSimpleClosedPolygon J)
    {D : Finset (Set Pt)} (hopen : ∀ d ∈ D, IsOpen d)
    (hD : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ∀ d₃ ∈ D, d₁ ≠ d₂ → d₂ ≠ d₃ → d₁ ≠ d₃ → d₁ ∩ d₂ ∩ d₃ = ∅)
    (hcov : polyInterior J ⊆ ⋃ d ∈ D, d)
    (hpoly : ∀ h ∈ compFamily (polyInterior J) D,
      ∃ Γ, IsSimpleClosedPolygon Γ ∧ h = polyInterior Γ)
    (G : Finset (Set Pt))
    (hG : ∀ h ∈ G, h ∈ compFamily (polyInterior J) D) : ¬ IsCircularChain G := by
  rintro ⟨m, hm, d, hinj, rfl, hcirc⟩
  set d₀ := polyInterior J with hd₀
  have hd₀o : IsOpen d₀ := (hPF.polyInterior_eq hJ).1
  have hmem : ∀ i, d i ∈ compFamily d₀ D := fun i => hG _ (Finset.mem_image_of_mem d
    (Finset.mem_univ i))
  have hP : ∀ i, IsOpen (d i) ∧ IsConnected (d i) ∧ d i ⊆ d₀ := fun i =>
    compFamily_props hd₀o hopen (hmem i)
  -- the chain in `ℕ`-indexing
  set e : ℕ → Set Pt := fun j => if h : j < m then d ⟨j, h⟩ else ∅ with he
  have he' : ∀ (j : ℕ) (h : j < m), e j = d ⟨j, h⟩ := fun j h => by simp [he, h]
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set A₂ := ⋃ j ∈ Set.Icc 2 (m - 1), e j with hA₂
  have hA₂o : IsOpen A₂ := isOpen_biUnion fun j hj => by
    rw [he' j (by simp at hj; omega)]; exact (hP _).1
  have hA₂c : IsConnected A₂ := by
    obtain ⟨z, hz⟩ := (hP ⟨2, by omega⟩).2.1.nonempty
    refine ⟨⟨z, mem_biUnion (x := 2) (by simp; omega) (by rw [he' 2 (by omega)]; exact hz)⟩, ?_⟩
    refine IsPreconnected.biUnion_of_chain Set.ordConnected_Icc (fun j hj => ?_) ?_
    · rw [he' j (by simp at hj; omega)]; exact (hP _).2.1.isPreconnected
    · intro j hj hj'
      simp only [Set.mem_Icc, Order.succ_eq_add_one] at hj hj' ⊢
      rw [he' j (by omega), he' (j + 1) (by omega)]
      refine (hcirc ⟨j, by omega⟩ ⟨j + 1, by omega⟩).2 (Or.inl ?_)
      simp only
      omega
  have hA₂sub : A₂ ⊆ d₀ := iUnion₂_subset fun j hj => by
    rw [he' j (by simp at hj; omega)]; exact (hP _).2.2
  have hne : ∀ i j : Fin m, i ≠ j → d i ≠ d j := fun i j h h' => h (hinj h')
  have h₀₁ : (d i₀ ∩ d i₁).Nonempty := (hcirc i₀ i₁).2 (Or.inl (by simp [i₀, i₁]))
  have h₁₂ : (d i₁ ∩ A₂).Nonempty := by
    obtain ⟨z, hz⟩ := (hcirc i₁ ⟨2, by omega⟩).2 (Or.inl (by simp [i₁]))
    exact ⟨z, hz.1, mem_biUnion (x := 2) (by simp; omega) (by rw [he' 2 (by omega)]; exact hz.2)⟩
  have h₂₀ : (A₂ ∩ d i₀).Nonempty := by
    obtain ⟨z, hz⟩ := (hcirc i₀ ⟨m - 1, by omega⟩).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact ⟨z, mem_biUnion (x := m - 1) (by simp; omega) (by rw [he' _ (by omega)]; exact hz.2),
      hz.1⟩
  have ht : d i₀ ∩ d i₁ ∩ A₂ = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro z ⟨⟨hz₀, hz₁⟩, hz₂⟩
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.1 hz₂
    simp only [Set.mem_Icc] at hj
    rw [he' j (by omega)] at hzj
    have := compFamily_no_triple hD (hmem i₀) (hmem i₁) (hmem ⟨j, by omega⟩)
      (hne _ _ (by simp [i₀, i₁])) (hne _ _ (by simp [i₁, Fin.ext_iff]; omega))
      (hne _ _ (by simp [i₀, Fin.ext_iff]; omega))
    have hz : z ∈ d i₀ ∩ d i₁ ∩ d ⟨j, by omega⟩ := ⟨⟨hz₀, hz₁⟩, hzj⟩
    rw [this] at hz
    exact hz
  obtain ⟨Γ, α₀, α₁, α₂, p₀, p₁, p₂, hΓ, hdec, hc₀, hc₁, hc₂, hp₁, hp₂, hp₀, hs₀, hs₁, hs₂⟩ :=
    exists_theta_polygon (hP i₀).1 (hP i₁).1 hA₂o (hP i₀).2.1 (hP i₁).2.1 hA₂c h₀₁ h₁₂ h₂₀ ht
  obtain ⟨Γa, hΓa, hda⟩ := hpoly _ (hmem i₀)
  obtain ⟨Γb, hΓb, hdb⟩ := hpoly _ (hmem i₁)
  obtain ⟨q, hqU, hq₀, hq₁, hqcl⟩ := hPF.exists_theta_point hΓ hdec hc₀ hc₁ hc₂ hp₁ hp₂
    hp₀ hΓa hΓb hda hdb hA₂o hs₀ hs₁ hs₂ (by
      rw [inter_assoc, inter_comm, ht])
  -- the interior of `Γ` lies in `d₀`
  have hΓd₀ : Γ ⊆ d₀ := by
    rw [← hdec]
    exact union_subset (union_subset (hs₀.trans (hP i₀).2.2) (hs₁.trans (hP i₁).2.2))
      (hs₂.trans hA₂sub)
  have hqd₀ : q ∈ d₀ := by
    by_contra hq
    obtain ⟨hWc, hWb⟩ := hPF.compl_polyInterior hJ
    exact (polyInterior_disjoint_of_unbounded hWc hWb
      (Set.disjoint_compl_left_iff_subset.2 hΓd₀)).notMem_of_mem_left hq hqU
  obtain ⟨dd, hdd, hqdd⟩ := mem_iUnion₂.1 (hcov hqd₀)
  obtain ⟨da, hda, xa, hxa, hA⟩ := hmem i₀
  obtain ⟨db, hdb, xb, hxb, hB⟩ := hmem i₁
  have hab : da ≠ db := by
    rintro rfl
    apply hne i₀ i₁ (by simp [i₀, i₁, Fin.ext_iff])
    rw [hA, hB]
    exact connectedComponentIn_eq_of_meet (by rw [← hA, ← hB]; exact h₀₁)
  obtain ⟨u, hu, hu'⟩ := mem_closure_iff.1 hqcl dd (hopen dd hdd) hqdd
  have hua : u ∈ da := by
    have := hu'.1; rw [hA] at this; exact (connectedComponentIn_subset _ _ this).2
  have hub : u ∈ db := by
    have := hu'.2; rw [hB] at this; exact (connectedComponentIn_subset _ _ this).2
  have hcase : dd = da ∨ dd = db := by
    by_contra hc
    push_neg at hc
    have := hD dd hdd da hda db hdb hc.1 hab hc.2
    have hu3 : u ∈ dd ∩ da ∩ db := ⟨⟨hu, hua⟩, hub⟩
    rw [this] at hu3
    exact hu3
  have hfr : ∀ (h : Set Pt), IsOpen h → q ∈ frontier h → q ∉ h := fun h ho hq hqh => by
    rw [ho.frontier_eq] at hq; exact hq.2 hqh
  rcases hcase with rfl | rfl
  · refine hfr _ (hP i₀).1 hq₀ ?_
    rw [hA]
    exact mem_connectedComponentIn_of_mem_closure (hd₀o.inter (hopen _ hdd)) ⟨hqd₀, hqdd⟩
      (hA ▸ closure_mono inter_subset_left hqcl)
  · refine hfr _ (hP i₁).1 hq₁ ?_
    rw [hB]
    exact mem_connectedComponentIn_of_mem_closure (hd₀o.inter (hopen _ hdd)) ⟨hqd₀, hqdd⟩
      (hB ▸ closure_mono inter_subset_right hqcl)

/- `theorem6_1951` was moved to `HPC/Plane/Tree7Comp.lean` in batch 129 and re-proved there from
`theorem7_1951`: `compFamily_no_circular` now asks the members of `compFamily` to be polygon
interiors (so that Janiszewski is applied to polygonal sets only), which the notched-square cover
used here does not guarantee, while the general-position cover of Theorem 7 does. -/

end HPC.Plane
