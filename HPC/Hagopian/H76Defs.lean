import HPC.Hagopian.Hagopian75

/-!
# Batch 156: the definitions of the skeleton `Hagopian76A.lean`

The definitions of the batch-156 skeleton (p. 340 of Hagopian 1976) and the statement
`Hagopian76Thm1`, verbatim, split off so that the supporting files `H76*.lean` can use them.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones

/-! ## Definitions (p. 340) -/

section Defs

variable {X : Type*} [MetricSpace X]

/-- "The decomposition" of a type A′ continuum: an admissible map with layers of void interior, on
a continuum irreducible between two points. -/
def IsMinimalAdmissible (E : Set X) (k : E → unitInterval) : Prop :=
  (∃ a b, IsIrreducibleBetween E a b) ∧ IsAdmissibleMap E k ∧ ∀ t, interior (k ⁻¹' {t}) = ∅

/-- The union of the layers over a set of parameters, as a subset of the ambient space. -/
def layerSet {E : Set X} (k : E → unitInterval) (A : Set unitInterval) : Set X :=
  Subtype.val '' (k ⁻¹' A)

/-- `F` is an **extension of `E` away from `X₀`** (p. 340): "a continuum of type A′ that contains
`E` and has `X₀` as an end set". The end set is normalized to the layer over `0`. -/
def IsExtensionAway (E X₀ F : Set X) : Prop :=
  E ⊆ F ∧ ∃ d : F → unitInterval, IsMinimalAdmissible F d ∧ layer d 0 = X₀

/-- `R(X₀, E)`: the union of all extensions of `E` away from `X₀`. -/
def extUnion (E X₀ : Set X) : Set X := ⋃₀ {F | IsExtensionAway E X₀ F}

end Defs

/-! ### Chains in the plane (p. 340) -/

section Chains

variable {M : Set Pt}

/-- A subset of `M` as a subset of the plane. -/
def toPt (A : Set M) : Set Pt := Subtype.val '' A

end Chains

/-- **Hagopian 1976, Theorem 1** (p. 345), as a statement: "If `M` is an indecomposable homogeneous
continuum in `R²`, then `M` is hereditarily indecomposable." (Proved in later batches.) -/
def Hagopian76Thm1 : Prop :=
  ∀ (M : Set Pt) [CompactSpace M] [ConnectedSpace M], IsHomogeneous M →
    ¬ IsDecomposableSpace M → IsHereditarilyIndecomposable (univ : Set M)

end HPC.Hagopian
