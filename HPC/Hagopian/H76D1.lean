import HPC.Hagopian.Hagopian76A

/-!
# Batch 157, item A: D1 reduced to the swallowed-layer configuration

The first paragraph of Lemma 4 (Hagopian 1976, p. 341), re-rendered in `Hagopian76B.lean`, and the
statement `hagopian76_no_swallowed_layer` ("no layer `k⁻¹(t)`, `t < 1`, lies in a layer of `F` that
meets `k⁻¹(1)`") are equivalent, given `hagopian76_lemma4_layers'`. Both directions are proved here,
without homogeneity:

* `lemma4_layers_of_no_swallowed`: from `lemma4_layers_aux`, `k⁻¹(1)` lies in `d⁻¹(s)` (otherwise
  `k⁻¹(1) = d⁻¹(u)` with `u < s`, and `d⁻¹[[0, u]]` would be a proper subcontinuum of `E` meeting both
  end sets); so a layer `k⁻¹(t)`, `t < 1`, that is not a layer of `F` lies in `d⁻¹(s)`, which meets
  `k⁻¹(1)`: the swallowed configuration.
* `no_swallowed_of_lemma4_layers`: if `k⁻¹(t) = d⁻¹(u')` and `k⁻¹(t) ⊆ d⁻¹(u)`, then `u' = u`, and
  `k⁻¹(1)` would meet `k⁻¹(t)`.

So D1 is exactly the exclusion of the swallowed configuration; it remains open (`OPEN.md`).
-/

namespace HPC.Hagopian

open Set Topology Metric HPC.Plane HPC.Jones

section D1

theorem IsMinimalAdmissible.isCompact {X : Type*} [MetricSpace X] {E : Set X} {k : E → unitInterval}
    (hE : IsMinimalAdmissible E k) : IsCompact E := by
  obtain ⟨⟨a, b, hab⟩, -, -⟩ := hE
  exact hab.1.1

/-- Two layers sharing a point have the same parameter. -/
theorem layer_param_eq {X : Type*} {F : Set X} {d : F → unitInterval} {x : X} {u u' : unitInterval}
    (hx : x ∈ layer d u) (hx' : x ∈ layer d u') : u = u' := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hx'
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact (mem_singleton_iff.1 hy).symm.trans (mem_singleton_iff.1 hy')

theorem layer_nonempty {X : Type*} {E : Set X} {k : E → unitInterval} (hk : Function.Surjective k)
    (t : unitInterval) : (layer k t).Nonempty := by
  obtain ⟨e, he⟩ := hk t
  exact ⟨e, e, he, rfl⟩

variable {M : Set Pt}

end D1

end HPC.Hagopian
