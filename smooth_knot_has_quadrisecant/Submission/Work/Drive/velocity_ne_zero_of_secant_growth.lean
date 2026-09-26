import Mathlib
import Submission.Work.Drive.chordSweepDefs

namespace Work.Drive

open scoped Topology
open LeanEval.KnotTheory.Quadrisecant

/-- **A one-sided secant growth rate forces a non-vanishing velocity.**  If `F` is differentiable at
`t` and, along a fixed direction `n`, every forward secant of length `g ∈ (0,h]` grows at least at
rate `c > 0` (`c*g ≤ ⟪n, F(t+g) - F t⟫`), then `velocity F t ≠ 0`.  (The right-hand slope limit of
`u ↦ ⟪n, F u⟫` at `t` is `⟪n, velocity F t⟫ ≥ c > 0`.)  This is the
`Submission/Work/Drive/sweepFamVelNz.lean` lines 198–252 argument made generic (its instance is
`Work.Drive.velNz_velocity_ne_zero_of_avg_chord`). -/
lemma velocity_ne_zero_of_secant_growth {F : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {t h c : ℝ} {n : LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : DifferentiableAt ℝ F t) (hh : 0 < h) (hc : 0 < c)
    (hg : ∀ g : ℝ, 0 < g → g ≤ h → c * g ≤ inner ℝ n (F (t + g) - F t)) :
    LeanEval.KnotTheory.Quadrisecant.velocity F t ≠ 0 := by
  -- the one-sided slope limit of `F` at `t` is `deriv F t`
  have hslope : Filter.Tendsto (slope F t) (𝓝[>] t) (𝓝 (deriv F t)) :=
    hF.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  have hlim : Filter.Tendsto (fun y : ℝ => inner ℝ n (slope F t y)) (𝓝[>] t)
      (𝓝 (inner ℝ n (deriv F t))) :=
    (tendsto_const_nhds (x := n)).inner hslope
  -- the eventual lower bound on the inner product of the slope
  have hev : ∀ᶠ y in 𝓝[>] t, c ≤ inner ℝ n (slope F t y) := by
    refine Filter.mem_of_superset (Ioc_mem_nhdsGT (a := t + h) (by linarith : t < t + h)) ?_
    intro y hy
    show c ≤ inner ℝ n (slope F t y)
    rw [Set.mem_Ioc] at hy
    obtain ⟨hyt, hyh⟩ := hy
    have hgt : 0 < y - t := by linarith
    have hle : y - t ≤ h := by linarith
    have hy_eq : t + (y - t) = y := by ring
    have hstep := hg (y - t) hgt hle
    rw [hy_eq] at hstep
    have hsl : slope F t y = (y - t)⁻¹ • (F y - F t) := rfl
    rw [hsl, inner_smul_right, inv_mul_eq_div]
    exact (le_div_iff₀ hgt).mpr hstep
  have hfinal : c ≤ inner ℝ n (velocity F t) := ge_of_tendsto hlim hev
  intro hzero
  rw [hzero, inner_zero_right] at hfinal
  exact absurd hfinal (not_le.mpr hc)

end Work.Drive
