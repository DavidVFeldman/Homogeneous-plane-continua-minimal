import HPC.Moore.Sec7B

/-!
# Moore, F.A. (1916), §7: chords of a closed curve (batch 139)

The device behind Theorems 37 and 38. `J` and `C` are closed curves, `T` is an arc of `J`
(parametrized by an embedding `g`, from `A₁ = g 0` to `A₂ = g 1`) through `O = g o`, and `O` is not
on `C`. A *chord* is an arc of `C` from a point `g s` of `T` to a point `g t` (`s ≤ o ≤ t`) whose
open part misses `J`. Given any family of chords containing an arc `A₁XA₂` of `C`,
`exists_maximal_chord` gives a chord `g p … g q` in the family such that no other chord of the family
has its ends `g s`, `g t` on the intervals `g p … O` and `O … g q` of `T`.

The proof shows that the family has only finitely many pairs of ends (`param_chords_finite`):
except for `A₁XA₂` itself, every chord lies in the other arc `K` of `C` from `A₁` to `A₂`; in the
parameter of `K` distinct chords have disjoint open intervals (their ends are on `J`, their open
parts are not), and all have length at least some `λ > 0` (compactness, since their two ends lie in
the disjoint compact sets `C ∩ g[0, o]` and `C ∩ g[o, 1]`). This replaces Moore's limit-point
argument (the points `L₁`, `L₂`, `F`, `G` of p. 153) and makes his monotonicity statement
(\"in view of Theorem 29 …\") unnecessary.
-/

namespace HPC.Moore

open Set Topology Gen
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- A `λ`-separated set of points of `[0, 1]` is finite. -/
theorem finite_of_separated {α : Type*} {P : Set α} {l : ℝ} (hl : 0 < l) (m : α → ℝ)
    (hm01 : ∀ x ∈ P, 0 ≤ m x ∧ m x ≤ 1) (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → l ≤ |m x - m y|) :
    P.Finite := by
  classical
  refine Finite.of_finite_image (f := fun x => ⌊m x / l⌋₊) ?_ ?_
  · refine (finite_Iic ⌊1 / l⌋₊).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (hm01 x hx).2 hl.le)
  · intro x hx y hy hxy
    by_contra hne
    have h := hsep x hx y hy hne
    simp only at hxy
    have hx0 : 0 ≤ m x / l := div_nonneg (hm01 x hx).1 hl.le
    have hy0 : 0 ≤ m y / l := div_nonneg (hm01 y hy).1 hl.le
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one (m x / l)
    have h3 := Nat.floor_le hy0
    have h4 := Nat.lt_floor_add_one (m y / l)
    rw [hxy] at h1 h2
    have : |m x / l - m y / l| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hl, div_lt_one hl] at this
    linarith

section Chord

variable (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h51 : Space.Axiom5₁ (S := S))
include h1 h3 h4 h51

end Chord

end HPC.Moore
