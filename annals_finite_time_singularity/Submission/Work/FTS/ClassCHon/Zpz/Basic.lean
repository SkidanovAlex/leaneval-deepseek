/-
Copyright: work module for the Elgindi finite-time singularity project.

# `cmode` expressed through the mode numerator `numW`

The mode coefficient `cmode m F z` of `Work.FTS.PhiStar.Series` is defined with interval
integrals over `0..π/2`; for the differentiation lemma `cmode_Dz` it is convenient to use the
set-integral form `numW m F z = ∫_{Iθ} F z θ · φ_m(θ)` fixed in `Zpz/Defs.lean`
(`φ_m(θ) = e_m(θ) cos θ`).  This file collects the elementary rewritings:

* `numW_eq_interval` — `numW` is the interval integral of `cmode`;
* `cmode_eq_numW_div` — `cmode m G z = numW m G z / D_m` with the explicit normalisation
  constant `D_m = (2m+2)(2m+3)/(4m+5)`;
* `numW_Dz` — `numW m (D_z G) z = z · pwF m G z`;
* `uIoc_subset_of_mem` — an interval-nesting fact used by the FTC bound.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.ClassCHon.Zpz.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `cmode` as a set integral over `Iθ` -/

/-- `numW` written with the interval integral appearing in the definition of `cmode`. -/
theorem numW_eq_interval (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    numW m G z = ∫ θ in (0 : ℝ)..(Real.pi / 2),
      G z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  rw [numW, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
    Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  simp only [phiW]
  ring

/-- The mode coefficient as `numW` divided by the explicit mode normalisation constant. -/
theorem cmode_eq_numW_div (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m G z
      = numW m G z / (((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5)) := by
  rw [Work.FTS.PhiStar.Series.cmode, numW_eq_interval m G z,
    Work.FTS.PhiStar.Gegenbauer.FamNormValue m]

/-- `numW m (D_z G) z = z · pwF m G z`. -/
theorem numW_Dz (m : ℕ) (G : ℝ → ℝ → ℝ) (z : ℝ) :
    numW m (Work.Spaces.Dz G) z = z * pwF m G z := by
  rw [numW, pwF]
  rw [show (fun θ => Work.Spaces.Dz G z θ * phiW m θ)
      = (fun θ => z * (Work.Spaces.pz G z θ * phiW m θ)) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## Elementary interval facts -/

/-- For `t` between `z₀` and `x`, the interval between `z₀` and `t` is contained in the
interval between `z₀` and `x`. -/
theorem uIoc_subset_of_mem {t z₀ x : ℝ} (h : t ∈ Set.uIoc z₀ x) :
    Set.uIoc z₀ t ⊆ Set.uIoc z₀ x := by
  rcases Set.mem_uIoc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Set.uIoc_of_le h1.le, Set.uIoc_of_le (lt_of_lt_of_le h1 h2).le]
    exact Set.Ioc_subset_Ioc_right h2
  · rw [Set.uIoc_of_ge h2, Set.uIoc_of_ge (show x ≤ z₀ from le_trans h1.le h2)]
    exact Set.Ioc_subset_Ioc_left h1.le

end Work.FTS.ClassCHon.Zpz
