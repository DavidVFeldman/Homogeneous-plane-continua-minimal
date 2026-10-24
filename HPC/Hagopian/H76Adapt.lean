import HPC.Hagopian.Hagopian76E

/-!
# Batch 163, item A: a collar in which a given transverse arc is vertical

Route (commission 163 §2.A, made concrete). Start from any collar `F` of `γ`
(`exists_collar`), made continuous on the whole plane by clamping. Near its end `γ y` the arc `β`
lies in the open collar rectangle, and, being connected and off `γ`, on one side of it; flipping
`F` if necessary, below. In collar coordinates the end piece of `β`, cut at its last exit from a
small box under `(y, 0)` and continued by a vertical segment down to the bottom side, is an arc
`β₁` from `(y, 0)` to a point `(x₀, -1)` of the bottom side, crossing the open lower rectangle
`Q = (0, 1) × (-1, 0)` (`exists_drop_arc`). `β₁` cuts `Q` into two Jordan domains
(`plane_split`); two-sided Schoenflies (`plane_schoenflies₂`) in each, with the bottom side on
the top edge of `Q` and the left side on `β₁`, glue to a new lower half-collar whose vertical over
`y` runs along `β₁` (`exists_lower_halfcollar`). The upper half of `F` is kept.
-/

namespace HPC.Hagopian

open Set Topology Metric Filter HPC.Plane HPC.Jones HPC.Moore.Gen

/-- A horizontal segment is an arc. -/
theorem tarc_hseg {a b : ℝ} (c : ℝ) (hab : a ≠ b) :
    TArc ((a, c) : Pt) (b, c) (uIcc a b ×ˢ {c}) := by
  have h : ((a, c) : Pt) ≠ (b, c) := fun e => hab (congrArg Prod.fst e)
  have := tarc_segment h
  rwa [← Prod.image_mk_segment_left, segment_eq_uIcc, ← prod_singleton] at this

/-- A vertical segment is an arc. -/
theorem tarc_vseg {a b : ℝ} (c : ℝ) (hab : a ≠ b) :
    TArc ((c, a) : Pt) (c, b) ({c} ×ˢ uIcc a b) := by
  have h : ((c, a) : Pt) ≠ (c, b) := fun e => hab (congrArg Prod.snd e)
  have := tarc_segment h
  rwa [← Prod.image_mk_segment_right, segment_eq_uIcc, ← singleton_prod] at this

/-- A collar turned upside down is a collar. -/
theorem IsCollar.flip {γ : unitInterval → Pt} {F : ℝ × ℝ → Pt} (hF : IsCollar γ F) :
    IsCollar γ (fun q => F (q.1, -q.2)) := by
  obtain ⟨hemb, h0, hopen⟩ := hF
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 with hK
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.1, -q.2)) K K := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [mem_Icc] at hb
    exact ⟨ha, by simp only [mem_Icc]; constructor <;> linarith [hb.1, hb.2]⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  have hfl : IsEmbedding (hmaps.restrict _ K K) := by
    refine (Continuous.isClosedEmbedding ?_ ?_).isEmbedding
    · exact (continuous_fst.prodMk continuous_snd.neg).restrict hmaps
    · rintro ⟨⟨a, b⟩, _⟩ ⟨⟨a', b'⟩, _⟩ e
      simp only [MapsTo.restrict, Subtype.map, Subtype.mk.injEq, Prod.mk.injEq, neg_inj] at e
      exact Subtype.ext (Prod.ext e.1 e.2)
  refine ⟨hemb.comp hfl, fun t => by simpa using h0 t, ?_⟩
  have : (fun q : ℝ × ℝ => F (q.1, -q.2)) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) =
      F '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
    ext z; constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      simp only [mem_Ioo] at hb
      exact ⟨(a, -b), ⟨ha, by simp only [mem_Ioo]; constructor <;> linarith [hb.1, hb.2]⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      simp only [mem_Ioo] at hb
      exact ⟨(a, -b), ⟨ha, by simp only [mem_Ioo]; constructor <;> linarith [hb.1, hb.2]⟩,
        by simp⟩
  rw [this]; exact hopen

end HPC.Hagopian
