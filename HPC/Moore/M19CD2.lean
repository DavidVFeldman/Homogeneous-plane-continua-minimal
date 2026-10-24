import HPC.Moore.M19CDMain
import HPC.Moore.M19CDCells
import HPC.Moore.M19CDRegion
import HPC.Moore.M19DThm

/-!
# Batch 142: Moore 1919, Theorem C corrected; Theorem D

The batch-142 skeleton (kept verbatim at `doc/batches/skeletons/Moore1919CD2.lean`) is split as
follows.

| skeleton item | file | outcome |
|---|---|---|
| `Space.IsCrossCut` | this file | verbatim |
| `m19_theoremC_crosscuts` | this file, from `chords_rulable` (`M19DChords.lean`) | proved |
| `m19_theoremC_within` | this file, from `inside_rulable` (`M19DInside.lean`) | proved |
| `m19_theoremC_corrected` | this file, from `curve_rulable` (`M19DThm.lean`) | proved |
| `m19_theoremD` | `M19DThm.lean` | proved |
| (added) `m19_theoremD_regions` | this file, from `m19_theoremD_regions_of_curves` | proved |

The supporting files, in import order: `M19DGlue`, `M19DDefs`, `M19DPocket`, `M19DOuter`,
`M19DWeight`, `M19DCorner`, `M19DChords` (a ruling missing finitely many disjoint chords),
`M19DInside` (a closed curve within `ABCDA`), `M19DExtract` (the chords of a closed curve),
`M19DLens` (lenses about the points of `J`), `M19DNice` (a curve about a compact set crossing `J`
at each common point), `M19DThm` (Theorem D).
-/

namespace HPC.Moore

open Set Topology Gen

variable {S : Type*} {σ : Space S}

section M19CD2

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

end M19CD2

section Regions

variable (h1 : σ.Axiom1) (h2 : σ.Axiom2) (h3 : σ.Axiom3) (h4 : σ.Axiom4) (h5 : σ.Axiom5)
  (h6 : σ.Axiom6) (h7 : σ.Axiom7) (h8 : σ.Axiom8)
include h1 h2 h3 h4 h5 h6 h7 h8

variable {J I : Set S} {A B C D : S} {sAB sBC sCD sDA : Set S}

/-- **Theorem D, region form** (as used in Theorem E): if each point on or within `ABCDA` lies in a
region of `𝒢`, the interior of `ABCDA` has a double ruling each of whose subdivisions lies in some
region of `𝒢`. From `m19_theoremD` and `m19_theoremD_regions_of_curves`. *Axioms used: 1–8.* -/
theorem m19_theoremD_regions (q : σ.Quad J I A B C D sAB sBC sCD sDA) (𝒢 : Set (Set S))
    (h𝒢 : 𝒢 ⊆ σ.region) (hcov : ∀ P ∈ J ∪ I, ∃ V ∈ 𝒢, P ∈ V) :
    ∃ n m, ∃ R : σ.DoubleRuling q n m, ∀ U ∈ R.cells, ∃ V ∈ 𝒢, U ⊆ V :=
  m19_theoremD_regions_of_curves h1 h2 h3 h4 h5 h6 h7 h8 q
    (fun G hG hc => m19_theoremD h1 h2 h3 h4 h5 h6 h7 h8 q G hG hc) 𝒢 h𝒢 hcov

end Regions


end HPC.Moore
