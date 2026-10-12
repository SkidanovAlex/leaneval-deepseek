import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.heatK3_head_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The truncated heat-kernel integral `∫₀^ε p_s(x) ds` for `‖x‖ ≥ 3`

For `0 < ε ≤ 1` and `3 ≤ ‖x‖` we bound the heat-kernel integral over the small-time
range `(0, ε]` by the Gaussian factor `e^{-‖x‖²/4}`:

  `∫ s in Ioc 0 ε, heatK3 s x ≤ (1/(2π^{3/2})) · ‖x‖^{-2} · e^{-‖x‖²/4}`.

**Proof.**  The head estimate `heatK3_head_le` with `a = ‖x‖²/4`, `η = ε` gives

  `∫ s in Ioc 0 ε, (4πs)^{-3/2} e^{-a/s} ≤ √ε · e^{-a/ε} / (8 π^{3/2} a)`
  ` = √ε · e^{-‖x‖²/(4ε)} / (2 π^{3/2} ‖x‖²)`,

and since `ε ≤ 1` implies `√ε ≤ 1 ≤ e^{a/ε - a} = e^{‖x‖²(1/ε-1)/4}` we have
`√ε · e^{-a/ε} ≤ e^{-a} = e^{-‖x‖²/4}`; dividing by the positive `8 π^{3/2} a`
yields the claim.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

theorem heatK3_ioc_integral_le_gauss {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : 3 ≤ ‖x‖) :
    ∫ s in Set.Ioc 0 ε, Work.BoseFixR.LatGreen.heatK3 s x
      ≤ 1 / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / ‖x‖ ^ 2)
          * Real.exp (-‖x‖ ^ 2 / 4) := by
  have hxpos : 0 < ‖x‖ := by linarith
  have ha : 0 < ‖x‖ ^ 2 / 4 := by positivity
  obtain ⟨_hintg, hbnd⟩ :=
    heatK3_head_le (a := ‖x‖ ^ 2 / 4) (η := ε) ha hε
  -- rewrite `heatK3 s x` as the integrand of `heatK3_head_le`
  have hcongr : ∫ s in Set.Ioc 0 ε, Work.BoseFixR.LatGreen.heatK3 s x
      = ∫ t in Set.Ioc 0 ε,
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x‖ ^ 2 / 4 / t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    have h : -‖x‖ ^ 2 / (4 * s) = -(‖x‖ ^ 2 / 4 / s) := by
      rw [div_div]; ring
    simp only [Work.BoseFixR.LatGreen.heatK3, h]
  -- `√ε · e^{-a/ε} ≤ e^{-a}` for `a = ‖x‖²/4`
  have hs : Real.sqrt ε * Real.exp (-(‖x‖ ^ 2 / 4 / ε)) ≤ Real.exp (-(‖x‖ ^ 2 / 4)) := by
    have h1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    have hone : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    have hE : 0 ≤ (‖x‖ ^ 2 / 4) / ε - (‖x‖ ^ 2 / 4) := by
      have h2 : 0 ≤ (‖x‖ ^ 2 / 4) * (1 / ε - 1) := mul_nonneg (le_of_lt ha) (by linarith)
      have h3 : (‖x‖ ^ 2 / 4) / ε - (‖x‖ ^ 2 / 4) = (‖x‖ ^ 2 / 4) * (1 / ε - 1) := by ring
      linarith [h3 ▸ h2]
    have h2 : 1 ≤ Real.exp ((‖x‖ ^ 2 / 4) / ε - (‖x‖ ^ 2 / 4)) := Real.one_le_exp hE
    have h3 : Real.sqrt ε ≤ Real.exp ((‖x‖ ^ 2 / 4) / ε - (‖x‖ ^ 2 / 4)) := by
      have h := mul_le_mul h1 h2 (by norm_num) (by norm_num)
      simpa using h
    have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt (Real.exp_pos (-(‖x‖ ^ 2 / 4 / ε))))
    rw [← Real.exp_add] at h4
    rwa [show (‖x‖ ^ 2 / 4) / ε - (‖x‖ ^ 2 / 4) + -(‖x‖ ^ 2 / 4 / ε) = -(‖x‖ ^ 2 / 4)
      by ring] at h4
  -- the scalar comparison in the exact shape of the goal
  have hfin : Real.sqrt ε * Real.exp (-(‖x‖ ^ 2 / 4 / ε))
        / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 / 4))
      ≤ 1 / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / ‖x‖ ^ 2) * Real.exp (-‖x‖ ^ 2 / 4) := by
    have hc : (0 : ℝ) ≤ 8 * Real.pi ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 / 4) := by positivity
    calc Real.sqrt ε * Real.exp (-(‖x‖ ^ 2 / 4 / ε))
          / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 / 4))
        ≤ Real.exp (-(‖x‖ ^ 2 / 4)) / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 / 4)) :=
          div_le_div_of_nonneg_right hs hc
      _ = 1 / (2 * Real.pi ^ (3 / 2 : ℝ)) * (1 / ‖x‖ ^ 2) * Real.exp (-‖x‖ ^ 2 / 4) := by
          rw [neg_div]; field_simp; ring
  calc ∫ s in Set.Ioc 0 ε, Work.BoseFixR.LatGreen.heatK3 s x
      = ∫ t in Set.Ioc 0 ε,
          (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x‖ ^ 2 / 4 / t)) := hcongr
    _ ≤ Real.sqrt ε * Real.exp (-(‖x‖ ^ 2 / 4 / ε))
          / (8 * Real.pi ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 / 4)) := hbnd
    _ ≤ _ := hfin

end Work.BoseFixR.LatGreen
