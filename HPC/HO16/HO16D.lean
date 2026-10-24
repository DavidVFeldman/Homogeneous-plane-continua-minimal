import HPC.HO16.Thm20
import HPC.HO16.Prop19Conn
import HPC.HO16.P19Defs

/-!
# Batch 196: Hoehn–Oversteegen Theorem 1, IV — Proposition 19; Theorem 20 from Theorem 15

The skeleton `HO16D.lean` of commission 196, split under `HPC/HO16/`:

* `P19Defs.lean`: the skeleton's `p19T`, `p19α`, `HOThm15`; `HOProp19` (new: the statement of
  `ho16_prop19` as a named `Prop`, used to derive Theorem 20 before Proposition 19 was proved).
* `OrdFold.lean`: §2, `IsSimpleFoldOf.isOrdinaryPt_iff`.
* `P19Lib.lean`, `P19Ctx.lean`, `Prop19A.lean`–`Prop19D.lean`, `Prop19.lean`: §3,
  `ho16_prop19_full`.
* `Prop19Conn.lean`: §3, `ho16_prop19`, and `hoProp19_holds : HOProp19`.
* `P208.lean`: §4, `ho16_p208_false`.
* `Thm20.lean`: §5 with `HOProp19` as a hypothesis.
* This file: §5 in the skeleton's form, `HOProp19` discharged.
-/

namespace HPC.HO16

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Span

/-- **H–O Theorem 20, forward direction**, from Theorem 15. -/
theorem ho16_theorem20_of_thm15 (h15 : HOThm15) : HOThm20 :=
  ho16_theorem20_of_thm15_prop19 hoProp19_holds h15

end HPC.HO16
