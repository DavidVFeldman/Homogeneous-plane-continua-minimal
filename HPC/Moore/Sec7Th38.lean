import HPC.Moore.Sec7Chord

/-!
# Moore, F.A. (1916), §7: Theorem 38 (batch 139)

**Theorem 38** (p. 153, as printed). If `J` and `C` are closed curves, `O` is a point on `J` but
not on `C`, `A₁` and `A₂` are distinct points common to `C` and `J`, and `A₁XA₂` is an arc on `C`
such that the interior of the closed curve `A₁XA₂OA₁` is a subset of the exterior of `J`, then there
exist two points `O₁` and `O₂`, distinct from `O`, such that (1) on the interval `O₁OO₂` of the
curve `J`, `O` is between `O₁` and `A₂` and between `O₂` and `A₁`, (2) there is on the curve `C` an
arc `O₁YO₂` such that `O₁YO₂` and the interior of the closed curve `O₁YO₂OO₁` are subsets of the
exterior of `J`, (3) if the exterior of `J` contains `B₁ZB₂` and the interior of the closed curve
`B₁ZB₂OB₁` where `B₁` and `B₂` are points on that arc of `J` from `O₁` to `O₂` which does not
contain `O`, and `B₁ZB₂` is an arc of `C`, then `B₁ = O₁` and `B₂ = O₂`.

**Reading** (commission §2, \"record the reading\"):
* `A₁XA₂OA₁` is the closed curve formed by `A₁XA₂` and the arc `T` of `J` from `A₁` to `A₂`
  through `O` (there is exactly one such arc: `O` is not `A₁`, `A₂`). The open arc `A₁XA₂` is
  assumed to lie in the exterior of `J` (**added hypothesis** `hXE`; Moore's conclusion (2) states
  it for `O₁YO₂`, and Theorem 41's use, \"an interval `A_pXB_p` of `J₁` lying entirely without `J₂`
  except for its endpoints\", assumes it).
* (1): `O₁`, `O₂` lie on the arc `T'` of `J` from `A₁` to `A₂` not containing `O`, in the order
  `A₁, O₁, O₂, A₂`; the interval `O₁OO₂` is the arc `V` of `J` from `O₁` to `O₂` through `O`, and it
  contains `T`. \"`O` is between `O₁` and `A₂`\" is stated as: every arc of `V` from `O₁` to `A₂`
  contains `O` (and likewise for `O₂`, `A₁`).
* (3): as printed, `B₁`, `B₂` on the arc `V'` of `J` from `O₁` to `O₂` **not** containing `O`. So
  `O₁YO₂` is the *outermost* such arc of `C` (its pocket `O₁YO₂OO₁` is the largest), not the
  innermost as in Theorem 37. This is the form Theorem 41 uses (\"if `Z` and `W` are points on
  `A_pC` and `B_pC` …\"). The conclusion is stated as `{B₁, B₂} = {O₁, O₂}`: the statement does not
  say which of `B₁`, `B₂` is nearer `O₁`.

Proof (\"analogous\"; none printed): the chords here are the arcs of `C` from `T'` to `T'` whose open
part and pocket lie in the exterior of `J`. As in Theorem 37, all but `A₁XA₂` lie in the other arc
`K` of `C` from `A₁` to `A₂`, with disjoint open intervals in its parameter. They are finitely many:
otherwise chords would shrink to a point `y` of `J` (`param_chords_accumulate`), and the closed curve
formed by a small chord and the small arc of `J` between its ends would enclose `O` (Theorem 27)
while lying in a small region about `y` (Theorem 21). The outermost one is then chosen.
-/

namespace HPC.Moore

open Set Topology Gen Filter
open unitInterval (nonneg' le_one')

variable {S : Type*} {σ : Space S}

/-- Two different arcs of a closed curve with the same ends are its two arcs between them.
*Axioms used: 1, 3, 4, 5₁.* -/
theorem two_arcs_eq (h1 : σ.Axiom1) (h3 : σ.Axiom3) (h4 : σ.Axiom4)
    (h51 : Space.Axiom5₁ (S := S)) {J : Set S} (hJ : σ.IsSCC J) {u v : S} {U₁ U₂ : Set S}
    (hU₁ : σ.IsArc u v U₁) (hU₂ : σ.IsArc u v U₂) (hU₁J : U₁ ⊆ J) (hU₂J : U₂ ⊆ J)
    (hne : U₁ ≠ U₂) : U₁ ∩ U₂ = {u, v} ∧ U₁ ∪ U₂ = J := by
  obtain ⟨D₁, D₂, hD₁, hD₂, hDi, hDu, huniq⟩ :=
    fa_scc_two_arcs h1 h3 h4 h51 hJ (hU₁J hU₁.left_mem) (hU₁J hU₁.right_mem) hU₁.1
  rcases huniq U₁ hU₁J hU₁ with rfl | rfl <;> rcases huniq U₂ hU₂J hU₂ with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨hDi, hDu⟩
  · exact ⟨by rw [inter_comm, hDi], by rw [union_comm, hDu]⟩
  · exact absurd rfl hne

section Th38

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h7 h8

end Th38

end HPC.Moore
