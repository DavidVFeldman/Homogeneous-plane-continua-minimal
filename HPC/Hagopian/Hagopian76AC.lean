import HPC.Hagopian.Hagopian84A
import HPC.Hagopian.H84Rigid
import HPC.Hagopian.H84Lemma7

/-!
# Batch 185: Hagopian 1976, Theorem 1 — Lemma 7 of 1984; saturation; the case split

Sources: Hagopian 1976 (`doc/sources/hagopian1976.pdf`), pp. 347–348; Hagopian 1984
(`doc/sources/hagopian1984.pdf`), pp. 336–337. Route: commission 185. The skeleton is
`doc/batches/skeletons/Hagopian76AC.lean`; the proofs are split under `HPC/Hagopian/`:

* `H84TwoSided.lean` (§1): gluing of two type λ continua along a common end layer; the two-sided
  extension.
* `H84Lemma7.lean` (§2): the triod at an interior layer; Lemma 7.
* `H84Rigid.lean` (§3.1–§3.2): rigidity; runs.
* `H76Sat185.lean` (§4): the tip by Lemma 7; saturation.
* `H76Split185.lean` (§5): the case split for `i ≥ 3`.

| item | status | declaration |
|---|---|---|
| §0 `Wset84 = Wset` | proved | `wset84_eq_wset` |
| §1 two-sided extension | proved | `hagopian84_two_sided` |
| §2 Lemma 7 of 1984 | proved | `hagopian84_lemma7`, `hagopian84Lemma7_holds` |
| §3.1 rigidity | proved (shape below) | `layers_agree` |
| §3.2 runs | proved (shape below) | `translate_run`, `translate_run_right` |
| §3.3 runs of `F` along a translate | open | comment block below |
| §4.1 steps 4–5 | proved | `noncrossing_half_in_O_steps45` |
| §4.2 the tip by Lemma 7 | proved | `half_in_O_false` |
| §4.3 saturation | proved | `innerComponentsCross_hagopian` |
| §5 case split for `i ≥ 3` | proved | `blockLayersMeetSides3`, `layer_x3_meets_side` |
| §6 "between" with runs | open | comment block below |
| §7 Theorem 1, conditional | proved | `hagopian76_theorem1_of_cases4` |

Shape changes against the skeleton (report §1–§7): the items stated as `True` are given shapes; the
conditional form `innerComponentsCross_hagopian_of_lemma7` is not stated, since §2 is proved and
`innerComponentsCross_hagopian` is unconditional (report §0).
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-! ## §0. `W(x, ε)` -/

section Rigidity

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §1. The two-sided extension -/

/-! ## §2. Lemma 7 of 1984 -/

end Rigidity

section Runs

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §3. Rigidity and translate runs -/

/-- **§3.1, rigidity**. *Shape:* `(E, k)`, `(G, d)` minimal admissible, `E ∩ G` meeting two layers
of `E`. Then either `E` lies in a single layer of `G` (the only degenerate case; it forces `E ⊆ G`),
or `E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a', b']]` (`a < b`, `a' < b'`), every layer of `k` meeting `G` is a
layer of `d`, and every layer of `d` meeting `E` is a layer of `k`.

The degenerate case "`G` inside a single layer of `E`" is excluded by the hypothesis; "`E` inside a
single layer of `G`" with `E ⊄ G` or `G ⊄ E` is excluded inside the proof (Lemma 7, and the
surjectivity of `d` when `G ⊆ E`). -/
theorem layers_agree (hX : IsHomogeneous M) (hi : ¬ IsDecomposableSpace M) {E G : Set M}
    {k : E → unitInterval} {d : G → unitInterval} (hE : IsMinimalAdmissible E k)
    (hG : IsMinimalAdmissible G d)
    (h2 : ∃ t₁ t₂, t₁ ≠ t₂ ∧ ((E ∩ G) ∩ layer k t₁).Nonempty ∧ ((E ∩ G) ∩ layer k t₂).Nonempty) :
    (∃ v, E ⊆ layer d v) ∨
      ((∃ a b a' b' : unitInterval, a < b ∧ a' < b' ∧ E ∩ G = layerSet k (Icc a b) ∧
          E ∩ G = layerSet d (Icc a' b')) ∧
        (∀ r, (G ∩ layer k r).Nonempty → ∃ u, layer k r = layer d u) ∧
        ∀ u, (E ∩ layer d u).Nonempty → ∃ r, layer d u = layer k r) :=
  layers_agree_aux hX hi hE hG h2

end Runs

section Sat

variable {M : Set Pt} [CompactSpace M] [ConnectedSpace M]

/-! ## §4. Saturation (2e) -/

/-! ## §5. The case split for `i ≥ 3` -/

end Sat

/-! ## Open items (commission 185; obstructions in `OPEN.md`, batch 185, and the report)

**OPEN (§3.3, `crossing_component_run`).** For a crossing component `C` of `F ∩ π⁻¹[D]` and the
translate `h[E]` of `strand_lemma` through a point of `C` over the middle: `F ∩ h[E]` is a common
segment containing `C` running to within `2/n` of a translate end or to `d⁻¹(1)`. The first part is
available (`C` lies in the strand through that point, so `Cl C ⊆ h[E]`; `F ∩ h[E]` is a continuum;
`layers_agree` applies). Obstruction: (i) the degenerate alternative of `layers_agree`, `h[E]` inside
one layer of `F`, is not excluded; (ii) `translate_run` allows the end layer `d⁻¹(0)` as well as
`d⁻¹(1)`, and `d⁻¹(0)` is not excluded; (iii) no shape was found that is both provable this way and
strong enough for §6 (report §3.3).

theorem crossing_component_run : True := by
  sorry

**OPEN (§6, `case1_between_runs`).** As batch 183 §3, with §3.3 (open) as the missing input
(report §6).

theorem case1_between_runs : True := by
  sorry
-/

end HPC.Hagopian
