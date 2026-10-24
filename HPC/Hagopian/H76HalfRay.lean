import HPC.Hagopian.Hagopian76E
import HPC.Hagopian.H76Lemma3
import HPC.Plane.SorgenfreyDefs

/-!
# Batch 162, item A: half-ray density

Hagopian 1976, p. 343 (Lemma 7). For a continuum `G` essential to `R(E)` with its minimal map `d`
and an interior layer `d⁻¹(u)`, the two "half-rays" of the composant from `d⁻¹(u)` are each dense in
`Cl R(E)` (`halfray_dense_aux`), and they meet only in `d⁻¹(u)` (`halfray_inter_subset`).

* `piece_end_layers`: on a piece `P = d⁻¹[[a, b]]` of a type A′ continuum with continuous
  decomposition, **every** minimal admissible map has end layers `d⁻¹(a)`, `d⁻¹(b)` (in some order);
  `piece_map`: such a map exists; `Rset_eq_of_maps`: `R(·)` does not depend on the map.
* `extUnion_eq_of_subset`: if `Q ⊇ P` has the same layer over `0`, then `R(X, P) = R(X, Q)` (the
  extensions away from `X` form a chain, `ext_chain`).
* `closure_Rset_piece`: `Cl R(P) = Cl R(G)` for a piece `P` of `G`;
  `closure_Rset_of_common`: two type A′ continua sharing a continuum that meets two layers of each
  have the same `Cl R(·)`;
* `closure_Rset_essential`: `Cl R(G) = Cl R(E)` for `G` essential to `R(E)` (the cases
  `G ⊆ R(X, E)`, `G ⊆ R(Z, E)`, and the two-sided case of `essential_typeA'_two_sided`).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

section Piece

variable {X : Type*} [MetricSpace X]

/-- **End layers on a piece.** Every minimal admissible map `p` of the piece `P = d⁻¹[[a, b]]` has
end layers `d⁻¹(a)`, `d⁻¹(b)`, in one order or the other. -/
theorem piece_end_layers {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) {P : Set X} (hP : P = layerSet d (Icc a b)) {p : P → unitInterval}
    (hp : IsMinimalAdmissible P p) :
    (layer p 0 = layer d a ∧ layer p 1 = layer d b) ∨
      (layer p 0 = layer d b ∧ layer p 1 = layer d a) := by
  subst hP
  have hPG : layerSet d (Icc a b) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hd := hG.2.1
  have hGc := hG.isCompact
  have hdpiece : ∀ c c' : unitInterval, a ≤ c → c ≤ c' → c' ≤ b →
      Fold.Q78.IsContinuum (layerSet d (Icc c c')) ∧ layerSet d (Icc c c') ⊆ layerSet d (Icc a b) :=
    fun c c' h1 h2 h3 =>
    ⟨isContinuum_img hGc hd isClosed_Icc isPreconnected_Icc ⟨c, le_rfl, h2⟩,
     by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, ⟨h1.trans hy.1, hy.2.trans h3⟩, rfl⟩⟩
  have hA : ∀ K ⊆ layerSet d (Icc a b), Fold.Q78.IsContinuum K → (K ∩ layer d a).Nonempty →
      (K ∩ layer d b).Nonempty → K = layerSet d (Icc a b) := fun K hK hKc ha hb =>
    eq_layerSet_of_subcontinuum hG hL (hK.trans hPG) hKc hab ha hb hK
  -- the two points
  obtain ⟨x₀, hx₀⟩ := hd.2.1 a
  obtain ⟨z₀, hz₀⟩ := hd.2.1 b
  have hxP : (x₀ : X) ∈ layerSet d (Icc a b) := ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hab.le⟩, rfl⟩
  have hzP : (z₀ : X) ∈ layerSet d (Icc a b) := ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hab.le, le_rfl⟩, rfl⟩
  set x : layerSet d (Icc a b) := ⟨x₀, hxP⟩
  set z : layerSet d (Icc a b) := ⟨z₀, hzP⟩
  have hxa : (x : X) ∈ layer d a := ⟨x₀, hx₀, rfl⟩
  have hzb : (z : X) ∈ layer d b := ⟨z₀, hz₀, rfl⟩
  -- the parameter in `G` of a point of the piece
  have hparam : ∀ w : layerSet d (Icc a b), ∃ g : G, (g : X) = w ∧ d g ∈ Icc a b := by
    rintro ⟨_, g, hg, rfl⟩; exact ⟨g, rfl, hg⟩
  -- the main step, for a map with `q x = 0`, `q z = 1`
  have main : ∀ q : layerSet d (Icc a b) → unitInterval, IsMinimalAdmissible _ q → q x = 0 →
      q z = 1 → layer q 0 = layer d a ∧ layer q 1 = layer d b := by
    intro q hq hqx hqz
    have hqc := hq.isCompact
    have hqpiece : ∀ c c' : unitInterval, c ≤ c' → Fold.Q78.IsContinuum (layerSet q (Icc c c')) ∧
        layerSet q (Icc c c') ⊆ layerSet d (Icc a b) := fun c c' h =>
      ⟨isContinuum_img hqc hq.2.1 isClosed_Icc isPreconnected_Icc ⟨c, le_rfl, h⟩,
       by rintro _ ⟨y, -, rfl⟩; exact y.2⟩
    have hB : ∀ K ⊆ layerSet d (Icc a b), Fold.Q78.IsContinuum K → (K ∩ layer q 0).Nonempty →
        (K ∩ layer q 1).Nonempty → K = layerSet d (Icc a b) := fun K hK hKc h0 h1 =>
      end_sets_aux hq hK hKc h0 h1
    have hmemq : ∀ (w : layerSet d (Icc a b)) (S : Set unitInterval), (w : X) ∈ layerSet q S →
        q w ∈ S := by
      rintro w S ⟨w', hw', hww'⟩
      rw [← Subtype.ext hww']; exact hw'
    have hmemd : ∀ (g : G) (S : Set unitInterval), (g : X) ∈ layerSet d S → d g ∈ S := by
      rintro g S ⟨g', hg', hgg'⟩
      rw [← Subtype.ext hgg']; exact hg'
    refine ⟨Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
    · -- `q⁻¹(0) ⊆ d⁻¹(a)`
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨g, hgw, hg⟩ := hparam w
      by_contra hne
      have hlt : a < d g := lt_of_le_of_ne hg.1 fun h => hne (by rw [← hgw]; exact ⟨g, h.symm, rfl⟩)
      obtain ⟨hKc, hKP⟩ := hdpiece (d g) b hlt.le hg.2 le_rfl
      have hK := hB _ hKP hKc ⟨w, by rw [← hgw]; exact ⟨g, ⟨le_rfl, hg.2⟩, rfl⟩, w, hw, rfl⟩
        ⟨z, ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hg.2, le_rfl⟩, rfl⟩, z, hqz, rfl⟩
      have : (x₀ : X) ∈ layerSet d (Icc (d g) b) := by rw [hK]; exact hxP
      have := (hmemd x₀ _ this).1
      rw [hx₀] at this
      exact absurd hlt (not_lt.2 this)
    · -- `d⁻¹(a) ⊆ q⁻¹(0)`
      rintro _ ⟨g, hg, rfl⟩
      have hgP : (g : X) ∈ layerSet d (Icc a b) := ⟨g, by rw [mem_preimage, hg]; exact ⟨le_rfl, hab.le⟩, rfl⟩
      set w : layerSet d (Icc a b) := ⟨g, hgP⟩
      by_contra hne
      have hlt : 0 < q w := lt_of_le_of_ne unitInterval.nonneg' fun h => hne ⟨w, h.symm, rfl⟩
      obtain ⟨hKc, hKP⟩ := hqpiece (q w) 1 unitInterval.le_one'
      have hK := hA _ hKP hKc ⟨w, ⟨w, ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, g, hg, rfl⟩
        ⟨z, ⟨z, by rw [mem_preimage, hqz]; exact ⟨unitInterval.le_one', le_rfl⟩, rfl⟩, hzb⟩
      have : (x : X) ∈ layerSet q (Icc (q w) 1) := by rw [hK]; exact hxP
      have := (hmemq x _ this).1
      rw [hqx] at this
      exact absurd hlt (not_lt.2 this)
    · -- `q⁻¹(1) ⊆ d⁻¹(b)`
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨g, hgw, hg⟩ := hparam w
      by_contra hne
      have hlt : d g < b := lt_of_le_of_ne hg.2 fun h => hne (by rw [← hgw]; exact ⟨g, h, rfl⟩)
      obtain ⟨hKc, hKP⟩ := hdpiece a (d g) le_rfl hg.1 hlt.le
      have hK := hB _ hKP hKc ⟨x, ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hg.1⟩, rfl⟩, x, hqx, rfl⟩
        ⟨w, by rw [← hgw]; exact ⟨g, ⟨hg.1, le_rfl⟩, rfl⟩, w, hw, rfl⟩
      have : (z₀ : X) ∈ layerSet d (Icc a (d g)) := by rw [hK]; exact hzP
      have := (hmemd z₀ _ this).2
      rw [hz₀] at this
      exact absurd hlt (not_lt.2 this)
    · -- `d⁻¹(b) ⊆ q⁻¹(1)`
      rintro _ ⟨g, hg, rfl⟩
      have hgP : (g : X) ∈ layerSet d (Icc a b) := ⟨g, by rw [mem_preimage, hg]; exact ⟨hab.le, le_rfl⟩, rfl⟩
      set w : layerSet d (Icc a b) := ⟨g, hgP⟩
      by_contra hne
      have hlt : q w < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => hne ⟨w, h, rfl⟩
      obtain ⟨hKc, hKP⟩ := hqpiece 0 (q w) unitInterval.nonneg'
      have hK := hA _ hKP hKc ⟨x, ⟨x, by rw [mem_preimage, hqx]; exact ⟨le_rfl, unitInterval.nonneg'⟩, rfl⟩, hxa⟩
        ⟨w, ⟨w, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, g, hg, rfl⟩
      have : (z : X) ∈ layerSet q (Icc 0 (q w)) := by rw [hK]; exact hzP
      have := (hmemq z _ this).2
      rw [hqz] at this
      exact absurd hlt (not_lt.2 this)
  -- `{p x, p z} = {0, 1}`
  have hpc := hp.isCompact
  set α := p x
  set β := p z
  obtain ⟨hKc, -⟩ : Fold.Q78.IsContinuum (layerSet p (Icc (min α β) (max α β))) ∧ True :=
    ⟨isContinuum_img hpc hp.2.1 isClosed_Icc isPreconnected_Icc ⟨min α β, le_rfl,
      min_le_max⟩, trivial⟩
  have hKP : layerSet p (Icc (min α β) (max α β)) ⊆ layerSet d (Icc a b) := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hK := hA _ hKP hKc ⟨x, ⟨x, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩, hxa⟩
    ⟨z, ⟨z, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩, hzb⟩
  have hall : ∀ w, p w ∈ Icc (min α β) (max α β) := by
    intro w
    have : (w : X) ∈ layerSet p (Icc (min α β) (max α β)) := by rw [hK]; exact w.2
    obtain ⟨w', hw', hww'⟩ := this
    rw [← Subtype.ext hww']; exact hw'
  obtain ⟨w0, hw0⟩ := hp.2.1.2.1 0
  obtain ⟨w1, hw1⟩ := hp.2.1.2.1 1
  have hmin : min α β = 0 := le_antisymm (hw0 ▸ (hall w0).1) unitInterval.nonneg'
  have hmax : max α β = 1 := le_antisymm unitInterval.le_one' (hw1 ▸ (hall w1).2)
  have hab' : (α = 0 ∧ β = 1) ∨ (α = 1 ∧ β = 0) := by
    rcases le_total α β with h | h
    · left; rw [min_eq_left h] at hmin; rw [max_eq_right h] at hmax; exact ⟨hmin, hmax⟩
    · right; rw [min_eq_right h] at hmin; rw [max_eq_left h] at hmax; exact ⟨hmax, hmin⟩
  rcases hab' with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · exact Or.inl (main p hp h0 h1)
  · have := main (unitInterval.symm ∘ p) hp.symm_comp
      (by simp only [Function.comp_apply]; rw [show p x = 1 from h1, unitInterval.symm_one])
      (by simp only [Function.comp_apply]; rw [show p z = 0 from h0, unitInterval.symm_zero])
    rw [layer_symm_comp, layer_symm_comp, unitInterval.symm_zero, unitInterval.symm_one] at this
    exact Or.inr ⟨this.2, this.1⟩

/-- **A piece carries a minimal admissible map with the expected end layers.** -/
theorem piece_map {G : Set X} [CompactSpace G] {d : G → unitInterval}
    (hG : IsMinimalAdmissible G d) (hL : ∀ x, LSCAt (Setoid.ker d) x) {a b : unitInterval}
    (hab : a < b) {P : Set X} (hP : P = layerSet d (Icc a b)) :
    ∃ p : P → unitInterval, IsMinimalAdmissible P p ∧ layer p 0 = layer d a ∧
      layer p 1 = layer d b := by
  subst hP
  have hd := hG.2.1
  have hHc : Fold.Q78.IsContinuum (layerSet d (Icc a b)) :=
    isContinuum_img hG.isCompact hd isClosed_Icc isPreconnected_Icc ⟨a, le_rfl, hab.le⟩
  have hHG : layerSet d (Icc a b) ⊆ G := by rintro _ ⟨y, -, rfl⟩; exact y.2
  obtain ⟨x₀, hx₀⟩ := hd.2.1 a
  obtain ⟨z₀, hz₀⟩ := hd.2.1 b
  obtain ⟨-, -, -, -, ⟨hirr, k₀, hk₀, hk₀0⟩⟩ := isTypeA'_of_subcontinuum hG hL hHG hHc hab.ne
    ⟨x₀, ⟨x₀, by rw [mem_preimage, hx₀]; exact ⟨le_rfl, hab.le⟩, rfl⟩, x₀, hx₀, rfl⟩
    ⟨z₀, ⟨z₀, by rw [mem_preimage, hz₀]; exact ⟨hab.le, le_rfl⟩, rfl⟩, z₀, hz₀, rfl⟩
  have hk : IsMinimalAdmissible (layerSet d (Icc a b)) k₀ := ⟨hirr, hk₀, hk₀0⟩
  rcases piece_end_layers hG hL hab rfl hk with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨k₀, hk, h0, h1⟩
  · refine ⟨unitInterval.symm ∘ k₀, hk.symm_comp, ?_, ?_⟩
    · rw [layer_symm_comp, unitInterval.symm_zero, h1]
    · rw [layer_symm_comp, unitInterval.symm_one, h0]

end Piece

section Ray

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

end Ray

end HPC.Hagopian
