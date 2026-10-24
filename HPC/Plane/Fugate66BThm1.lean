import HPC.Plane.Fugate66Lemma1
import HPC.Plane.Fugate66BHU

/-!
# Batch 101: Fugate's Theorem 1, sufficiency

From the data of Lemma 4 (`Fit`), the two-case construction of Fugate (pp. 466–467) of a weak
`ε`-chain covering `A ∪ B` (Case i: `E ⊕ F(k−1..0)`; Case ii: the chain `𝒢`, after Claims 2–3 and
the separation of `D`), turned into a chain by trimming (`isSnakeLike_of_weak`).
-/

namespace HPC.Plane

open Set Metric Topology

variable {S : Type*} [MetricSpace S] [CompactSpace S]

omit [CompactSpace S] in
/-- Hereditary unicoherence passes to subsets. -/
theorem IsHereditarilyUnicoherent.mono {T U : Set S} (h : IsHereditarilyUnicoherent T)
    (hUT : U ⊆ T) : IsHereditarilyUnicoherent U := fun K hKU hK hnt =>
  h K (hKU.trans hUT) hK hnt

section FitCases

variable {A B : Set S} {ε : ℝ} {m n j k t : ℕ} {E F : ℕ → Set S}

end FitCases

end HPC.Plane
