import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuous logarithms of holomorphic functions are holomorphic

If `U` is open in `ℂ`, `g` is holomorphic and nonvanishing on `U`, and `f` is a
*continuous* logarithm of `g` on `U` (i.e. `exp (f z) = g z` for all `z ∈ U`),
then `f` is holomorphic on `U`.

The proof is local.  Near a point `z₀ ∈ U` with `g z₀ = exp (f z₀)`, the
principal branch `w ↦ f z₀ + log (w / g z₀)` of the logarithm is holomorphic in
a neighbourhood of `g z₀` and inverts `exp` there: for `z` close enough to `z₀`
one has `‖f z - f z₀‖ < π`, hence
`f z₀ + log (g z / g z₀) = f z₀ + log (exp (f z - f z₀)) = f z`.
So `f` agrees near `z₀` with the composition of the holomorphic map `g` with a
holomorphic function, and is therefore holomorphic at `z₀`.
-/

open scoped Topology

namespace Work.Escape

theorem differentiableOn_of_continuousOn_exp_eq {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ z ∈ U, g z ≠ 0) (h : ∀ z ∈ U, Complex.exp (f z) = g z) :
    DifferentiableOn ℂ f U := by
  intro z0 hz0
  -- `U` is a neighbourhood of `z0`, and `g` is holomorphic at `z0`.
  have hUmem : U ∈ 𝓝 z0 := hU.mem_nhds hz0
  -- A ball around `z0` contained in `U`, and one on which `f` stays within
  -- distance `π` of `f z0`.
  obtain ⟨r1, hr1pos, hr1sub⟩ := Metric.isOpen_iff.mp hU z0 hz0
  obtain ⟨δf, hδfpos, hδf⟩ :=
    Metric.continuousWithinAt_iff.mp (hf.continuousWithinAt hz0) Real.pi Real.pi_pos
  have hδ : 0 < min r1 δf := lt_min hr1pos hδfpos
  -- The local branch of the logarithm at `g z0`.
  have hγne : g z0 ≠ 0 := hne z0 hz0
  have hLdiff : DifferentiableAt ℂ (fun v : ℂ => f z0 + Complex.log (v / g z0)) (g z0) := by
    have hslit : (fun v : ℂ => v / g z0) (g z0) ∈ Complex.slitPlane := by
      simp only [div_self hγne, Complex.mem_slitPlane_iff, Complex.one_re]
      norm_num
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v / g z0) (g z0) := by
      simpa using (differentiableAt_id (x := g z0) (𝕜 := ℂ)).div_const (g z0)
    exact (h1.clog hslit).const_add (f z0)
  have hcomp : DifferentiableAt ℂ (fun z => f z0 + Complex.log (g z / g z0)) z0 := by
    have h' := hLdiff.comp z0 (hg.differentiableAt hUmem)
    simpa [Function.comp_def] using h'
  -- On a neighbourhood of `z0`, `f` coincides with that composition.
  have heq : f =ᶠ[𝓝 z0] (fun z => f z0 + Complex.log (g z / g z0)) := by
    filter_upwards [Metric.ball_mem_nhds z0 hδ] with z hz
    have hdist : dist z z0 < min r1 δf := Metric.mem_ball.mp hz
    have hzU : z ∈ U := hr1sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hfd : dist (f z) (f z0) < Real.pi :=
      hδf hzU (lt_of_lt_of_le hdist (min_le_right _ _))
    have hnorm : ‖f z - f z0‖ < Real.pi := by simpa [dist_eq_norm] using hfd
    have habs : |(f z - f z0).im| < Real.pi := lt_of_le_of_lt (Complex.abs_im_le_norm _) hnorm
    have hgt : -Real.pi < (f z - f z0).im := (abs_lt.mp habs).1
    have hle : (f z - f z0).im ≤ Real.pi := (abs_lt.mp habs).2.le
    have hlog : Complex.log (Complex.exp (f z - f z0)) = f z - f z0 := Complex.log_exp hgt hle
    rw [← h z hzU, ← h z0 hz0, ← Complex.exp_sub, hlog]
    ring
  exact (hcomp.congr_of_eventuallyEq heq).differentiableWithinAt

end Work.Escape
