import HPC.Plane.Most51
import HPC.Chains.Basic
import HPC.Plane.Composant91
import HPC.Plane.Surgery91

/-!
# Bing 1951 (*Snake-like continua*), §4, part one: definitions and general topology

The definitions of the batch-92 skeleton (`Atriodic51.lean`, split into three files; see
`HPC/Plane/Atriodic51.lean`), unchanged, and the general-topology facts used for properties 1–6
and Theorem 8 that do not involve Bing's standing hypothesis.

Throughout, `S` is a compact metric space which is itself the continuum (Bing: "we suppose that
`S` is all of the space"); "continuum" means `Fold.Q78.IsContinuum` (nonempty compact connected).
`A` contains `B` *interiorly* means `B ⊆ interior A`.
-/

namespace HPC.Plane

open Set Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

/-- A *triod*: a continuum `M` containing a subcontinuum `N` such that `M \ N` is the union of
three mutually separated nonempty sets (Bing 1951, §1). -/
def IsTriod (M : Set S) : Prop :=
  Fold.Q78.IsContinuum M ∧ ∃ N : Set S, Fold.Q78.IsContinuum N ∧ N ⊆ M ∧
    ∃ A B C : Set S, A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧ M \ N = A ∪ B ∪ C ∧
      Disjoint (closure A) B ∧ Disjoint A (closure B) ∧ Disjoint (closure A) C ∧
      Disjoint A (closure C) ∧ Disjoint (closure B) C ∧ Disjoint B (closure C)

/-- *Atriodic*: contains no triod. -/
def IsAtriodic (M : Set S) : Prop := ∀ T ⊆ M, ¬ IsTriod T

/-- *Unicoherent*: whenever the continuum is the union of two subcontinua, their intersection is
connected. -/
def IsUnicoherent (M : Set S) : Prop :=
  ∀ H K : Set S, Fold.Q78.IsContinuum H → Fold.Q78.IsContinuum K → H ∪ K = M → IsConnected (H ∩ K)

/-- *Hereditarily unicoherent*: every nondegenerate subcontinuum is unicoherent. -/
def IsHereditarilyUnicoherent (M : Set S) : Prop :=
  ∀ K ⊆ M, Fold.Q78.IsContinuum K → K.Nontrivial → IsUnicoherent K

/-! ## General topology -/

omit [CompactSpace S] in
theorem isContinuum_union {A B : Set S} (hA : Fold.Q78.IsContinuum A)
    (hB : Fold.Q78.IsContinuum B) (h : (A ∩ B).Nonempty) : Fold.Q78.IsContinuum (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := h
  exact ⟨hA.1.union hB.1, ⟨⟨x, Or.inl hxA⟩, hA.2.2.union x hxA hxB hB.2.2⟩⟩

end HPC.Plane
