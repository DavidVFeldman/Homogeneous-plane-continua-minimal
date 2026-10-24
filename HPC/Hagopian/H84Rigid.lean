import HPC.Hagopian.H84Lemma7

/-!
# Batch 185, §3.1–§3.2: rigidity and runs

* `layers_agree_aux` (§3.1): if `E ∩ G` meets two layers of `E`, then either `E` lies in a single
  layer of `G`, or `E ∩ G` is a segment of both and the two decompositions agree on it.
* `translate_run_left_aux`, `translate_run_right_aux` (§3.2): an end of the common segment that is
  not an end of `E` is an end layer of `G` (atriodicity, `no_arm_at_interior_layer`). Stated for any
  type λ continuum `E`; the translate `h[E]` is the instance `exists_image_map`.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

section Rigid

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-- **§3.1, rigidity.** `(E, k)`, `(G, d)` minimal admissible, `E ∩ G` meeting two layers of `E`.
Then either `E` lies in a single layer of `G` (the degenerate case: then `E ⊆ G`), or
* `E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a', b']]` with `a < b`, `a' < b'`;
* every layer of `k` meeting `G` is a layer of `d`, and every layer of `d` meeting `E` is a layer of
  `k`.

The nondegenerate case is Lemma 6 twice (`layer_common_of_essential`); the degenerate case is
excluded by Lemma 7 when neither continuum contains the other, and by the surjectivity of `d` when
`G ⊆ E`. -/
theorem layers_agree_aux (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E G : Set M}
    {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d)
    (h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((E ∩ G) ∩ layer k t₁).Nonempty ∧ ((E ∩ G) ∩ layer k t₂).Nonempty) :
    (∃ v, E ⊆ layer d v) ∨
      ((∃ a b a' b' : unitInterval, a < b ∧ a' < b' ∧ E ∩ G = layerSet k (Icc a b) ∧
          E ∩ G = layerSet d (Icc a' b')) ∧
        (∀ r, (G ∩ layer k r).Nonempty → ∃ u, layer k r = layer d u) ∧
        ∀ u, (E ∩ layer d u).Nonempty → ∃ r, layer d u = layer k r) := by
  have hHU := hagopian75_lemma1_hu hX hi
  have hEc : Fold.Q78.IsContinuum E := by obtain ⟨_, _, h⟩ := hE.1; exact h.1
  have hGc : Fold.Q78.IsContinuum G := by obtain ⟨_, _, h⟩ := hG.1; exact h.1
  obtain ⟨t₁, t₂, ht, ⟨p, hpK, hp₁⟩, ⟨q, hqK, hq₂⟩⟩ := h2
  have hK : Fold.Q78.IsContinuum (E ∩ G) := isContinuum_inter_of_hu hHU hEc hGc ⟨p, hpK⟩
  have h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((E ∩ G) ∩ layer k t₁).Nonempty ∧
      ((E ∩ G) ∩ layer k t₂).Nonempty := ⟨t₁, t₂, ht, ⟨p, hpK, hp₁⟩, ⟨q, hqK, hq₂⟩⟩
  rcases two_layers_or_subset (inter_subset_right : E ∩ G ⊆ G) hpK
      ((mem_layer_iff' hpK.2).2 rfl) with hK₂ | hKv
  · right
    obtain ⟨⟨a, b, hab, hseg⟩, -, -⟩ := hagopian84_lemma6 hX hi hE
      (⟨inter_subset_left, hK, h2⟩ : IsEssential84 k (E ∩ G))
    obtain ⟨⟨a', b', hab', hseg'⟩, -, -⟩ := hagopian84_lemma6 hX hi hG
      (⟨inter_subset_right, hK, hK₂⟩ : IsEssential84 d (E ∩ G))
    have hK' : Fold.Q78.IsContinuum (G ∩ E) := by rw [inter_comm]; exact hK
    have h2' : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((G ∩ E) ∩ layer k t₁).Nonempty ∧
        ((G ∩ E) ∩ layer k t₂).Nonempty := by rw [inter_comm]; exact h2
    have hK₂' : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((G ∩ E) ∩ layer d t₁).Nonempty ∧
        ((G ∩ E) ∩ layer d t₂).Nonempty := by rw [inter_comm]; exact hK₂
    refine ⟨⟨a, b, a', b', hab, hab', hseg, hseg'⟩, fun r ⟨x, hxG, hxr⟩ => ?_,
      fun u ⟨x, hxE, hxu⟩ => ?_⟩
    · exact layer_common_of_essential hX hi hE hG hK h2 hK₂ ⟨layer_subset' k r hxr, hxG⟩ hxr
    · exact layer_common_of_essential hX hi hG hE hK' hK₂' h2' ⟨layer_subset' d u hxu, hxE⟩ hxu
  · left
    set v := d ⟨p, hpK.2⟩
    by_cases hEG : E ⊆ G
    · refine ⟨v, fun x hx => hKv ⟨hx, hEG hx⟩⟩
    by_cases hGE : G ⊆ E
    · exfalso
      obtain ⟨w, hw⟩ : ∃ w : unitInterval, w ≠ v := by
        by_cases hv : v = 0
        · exact ⟨1, by rw [hv]; exact one_ne_zero⟩
        · exact ⟨0, fun h => hv h.symm⟩
      obtain ⟨x, hx⟩ := layer_nonempty hG.2.1.2.1 w
      have hxv := hKv ⟨hGE (layer_subset' d w hx), layer_subset' d w hx⟩
      exact hw (layer_param_eq hx hxv)
    exfalso
    obtain ⟨e₁, he₁E, he₁G⟩ := not_subset.1 hEG
    obtain ⟨g₁, hg₁G, hg₁E⟩ := not_subset.1 hGE
    obtain ⟨u₁, hu₁⟩ := hagopian84_lemma7_aux hX hi hE hG ⟨e₁, he₁E, he₁G⟩ ⟨g₁, hg₁G, hg₁E⟩
      ⟨p, hpK.2, hp₁⟩
    obtain ⟨u₂, hu₂⟩ := hagopian84_lemma7_aux hX hi hE hG ⟨e₁, he₁E, he₁G⟩ ⟨g₁, hg₁G, hg₁E⟩
      ⟨q, hqK.2, hq₂⟩
    have e₁' : u₁ = v := layer_param_eq (hu₁ ▸ hp₁) (hKv hpK)
    have e₂' : u₂ = v := layer_param_eq (hu₂ ▸ hq₂) (hKv hqK)
    have : layer k t₁ = layer k t₂ := by rw [hu₁, hu₂, e₁', e₂']
    exact ht (layer_param_eq hp₁ (this ▸ hp₁))

end Rigid

end HPC.Hagopian
