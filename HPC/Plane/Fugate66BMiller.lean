import HPC.Plane.Fugate66BHU

/-!
# Batch 101: the transcribed Miller Theorem 1.5 is false (two half-disks)

The closed unit disk `Disk` of `ℂ` is unicoherent (`isUnicoherent_disk`: a space contractible by an
explicit homotopy is unicoherent, via lifting through `exp` — Eilenberg's argument). It is the union
of the closed half-disks `A = {im ≥ 0}`, `B = {im ≤ 0}`, and its boundary circle is a
non-unicoherent subcontinuum lying in neither half (`miller_1_5_false`).
-/

namespace HPC.Plane

open Set Topology Metric unitInterval

/-- **Lifting through `exp`** on a space contracted to a point by a homotopy `Hc`: every continuous
map to `ℂ ∖ {0}` has a continuous logarithm (homotopy lifting for the covering `exp`). -/
theorem exists_exp_lift {X : Type*} [TopologicalSpace X] (Hc : C(I × X, X)) (x₀ : X)
    (h0 : ∀ x, Hc (0, x) = x₀) (h1 : ∀ x, Hc (1, x) = x)
    (g : C(X, {z : ℂ // z ≠ 0})) : ∃ G : C(X, ℂ), ∀ x, Complex.exp (G x) = g x := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Complex.exp c = g x₀ := ⟨Complex.log (g x₀), Complex.exp_log (g x₀).2⟩
  set Hg : C(I × X, {z : ℂ // z ≠ 0}) := g.comp Hc with hHg
  have H_0 : ∀ a, Hg (0, a) = (fun z : ℂ => (⟨_, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      (ContinuousMap.const X c a) := by
    intro a; apply Subtype.ext; simp [Hg, h0, hc]
  have hcov := Complex.isCoveringMap_exp
  refine ⟨(hcov.liftHomotopy Hg (ContinuousMap.const X c) H_0).comp
    ((ContinuousMap.const X (1 : I)).prodMk (ContinuousMap.id X)), fun x => ?_⟩
  have := congr_fun (hcov.liftHomotopy_lifts Hg _ H_0) (1, x)
  have := congrArg Subtype.val this
  simpa [Hg, h1] using this

/-- An integer-valued continuous real function on a preconnected set is constant. -/
theorem eq_of_isPreconnected_int_valued {X : Type*} [TopologicalSpace X] {Z : Set X}
    (hZ : IsPreconnected Z) {f : X → ℝ} (hf : ContinuousOn f Z) (hint : ∀ x ∈ Z, ∃ n : ℤ, f x = n)
    {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) : f x = f y := by
  wlog hxy : f x ≤ f y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  obtain ⟨n, hn⟩ := hint x hx
  obtain ⟨n', hn'⟩ := hint y hy
  by_contra hne
  have hlt : n < n' := by
    have := lt_of_le_of_ne hxy hne
    rw [hn, hn'] at this
    exact_mod_cast this
  have hlt' : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hlt
  obtain ⟨z, hz, hfz⟩ := hZ.intermediate_value hx hy hf
    (show (n : ℝ) + 1 / 2 ∈ Icc (f x) (f y) from ⟨by rw [hn]; linarith, by rw [hn']; linarith⟩)
  obtain ⟨m, hm⟩ := hint z hz
  rw [hm] at hfz
  have h2 : ((2 * m : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : 2 * m = 2 * n + 1 := by exact_mod_cast h2
  omega

/-! ## The disk -/

end HPC.Plane
