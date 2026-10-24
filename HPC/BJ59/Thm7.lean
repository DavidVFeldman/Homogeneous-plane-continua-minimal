import HPC.BJ59.Thm7Core
import HPC.BJ59.Transfer

/-!
# Batch 199, library: Bing–Jones Theorem 7, first sentence, in a metric space
(commission 199, §6)

The pseudo-arc `P` is a compact space; the traces of the links of `D` on `P` form a chain of `P`
(`traceChain`), Theorem 7 holds there (`bj7_compact`), and the resulting chain of `P` lifts back to
a chain of the ambient space in Bing–Jones's sense inside the links of `D`
(`exists_bjChain_shrink'`).
-/

namespace HPC.BJ59

open Set Topology Metric HPC.Plane

variable {X : Type*} [MetricSpace X]

/-- The traces of the links of a chain on a connected set `P` that they cover and all meet. -/
def traceChain {P : Set X} (hP : IsPreconnected P) {n : ℕ} (D : Chain X n)
    (hDP : P ⊆ D.union) (hDp : ∀ j, (D.link j ∩ P).Nonempty) : Chain P n where
  link j := Subtype.val ⁻¹' D.link j
  isOpen j := (D.isOpen j).preimage continuous_subtype_val
  adjacent i j := by
    have hpre : IsPreconnected (univ : Set P) :=
      Subtype.preconnectedSpace hP |>.isPreconnected_univ
    have hdisj : ∀ i j : Fin n, 1 < ((i : ℤ) - j).natAbs →
        Subtype.val ⁻¹' D.link i ∩ Subtype.val ⁻¹' D.link j = (∅ : Set P) := fun i j hij =>
      eq_empty_of_forall_notMem fun x hx => by
        have := (D.adjacent i j).1 ⟨x, hx.1, hx.2⟩
        omega
    have hcov : (univ : Set P) ⊆ ⋃ j, Subtype.val ⁻¹' D.link j := fun x _ => by
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hDP x.2)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hne : ∀ j, (Subtype.val ⁻¹' D.link j ∩ (univ : Set P)).Nonempty := fun j => by
      obtain ⟨x, hxD, hxP⟩ := hDp j
      exact ⟨⟨x, hxP⟩, hxD, mem_univ _⟩
    constructor
    · intro h
      by_contra h'
      push_neg at h'
      rw [hdisj i j h'] at h
      exact not_nonempty_empty h
    · intro h
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact adjacent_meet_of_cover hpre _ (fun j => (D.isOpen j).preimage continuous_subtype_val)
          hcov hne hdisj i j (by omega)
      · have : i = j := Fin.ext heq
        subst this
        obtain ⟨x, hx, -⟩ := hne i
        exact ⟨x, hx, hx⟩
      · rw [inter_comm]
        exact adjacent_meet_of_cover hpre _ (fun j => (D.isOpen j).preimage continuous_subtype_val)
          hcov hne hdisj j i (by omega)

end HPC.BJ59
