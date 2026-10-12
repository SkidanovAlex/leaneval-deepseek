import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.uvKernel_moment_le`

The UV-smoothing kernel `uvKernel fu Λ` (`fu : LowCut`, `Λ > 0`) is the inverse Fourier
transform of the symbol `ζ_Λ(p) = fu.f(‖p‖/Λ)`.  It has unit mass and the *scaled* Schwartz
decay

    `‖uvKernel fu Λ z‖ ≤ C Λ³ (1 + Λ‖z‖)^{-N}`   (all `N`, all `Λ > 0`, all `z`)

(`Work.BoseBoxFock.uvKernel_decay`).  The target here is the consequence that every *weighted*
moment of `uvKernel fu Λ` is uniformly bounded in `Λ ≥ 1`:

    `∫ z, |uvKernel fu Λ z| (1 + Λ‖z‖)^j ≤ C`   (`Λ ≥ 1`).

The mechanism is the scaling: choosing the decay exponent `N = j + 4` (so that the weight
`(1 + Λ‖z‖)^j` cancels all but four powers, leaving the integrable profile
`(1 + Λ‖z‖)^{-4}`, whose exponent `4` exceeds the dimension `3`), the change of variables
`z = Λ⁻¹ • y` turns

    `∫ z, Λ³ (1 + Λ‖z‖)^{-4} dz = ∫ y, (1 + ‖y‖)^{-4} dy`

(`Measure.integral_comp_smul`), which is a *fixed* finite number.  So the bound is uniform in
`Λ > 0` (in particular for `Λ ≥ 1`).

This is a verbatim `j`-generalisation of the `N = 5` L¹-bound
`Work.BoseBoxFock.uvKernel_L1_bound_of_decay`; the only new ingredient is the power bookkeeping
`(1 + Λ‖z‖)^{-(j+4)} * (1 + Λ‖z‖)^j = (1 + Λ‖z‖)^{-4}` (`zpow_add₀`).
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem uvKernel_moment_le (fu : Work.BoseBoxFix.LowCut) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ : ℝ), 1 ≤ Λ →
      ∫ z : EuclideanSpace ℝ (Fin 3), |Work.BoseBoxFock.uvKernel fu Λ z| * (1 + Λ * ‖z‖) ^ j ≤ C := by
  -- the scalar-weighted Schwartz decay with exponent `j + 4`
  obtain ⟨C₀, hC₀nn, hdec⟩ := Work.BoseBoxFock.uvKernel_decay fu (j + 4)
  -- integrability of the fixed profile `z ↦ C₀ (1 + ‖z‖)^{-4}` (`4 > 3 = finrank ℝ ℝ³`)
  have hbase : Integrable (fun z : E3 => C₀ * (1 + ‖z‖) ^ (-(4 : ℤ))) :=
    (Work.BoseBoxFock.integrable_one_add_norm_zpow 4 (by norm_num)).const_mul C₀
  refine ⟨C₀ * ∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ)), ?_, ?_⟩
  · exact mul_nonneg hC₀nn (integral_nonneg (fun y => zpow_nonneg (by positivity) _))
  · intro Λ hΛ
    have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
    set G : E3 → ℝ := fun z => C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(4 : ℤ)) with hG
    -- the rescaled form of `G`, matching the change of variables `z ↦ Λ • z`
    have hG_eq : ∀ z : E3, G z = Λ ^ 3 * (C₀ * (1 + ‖(Λ : ℝ) • z‖) ^ (-(4 : ℤ))) := by
      intro z
      simp only [hG]
      rw [norm_smul, Real.norm_of_nonneg hΛpos.le]
      ring
    have hIntG : Integrable G := by
      have h2 : Integrable (fun z : E3 => C₀ * (1 + ‖(Λ : ℝ) • z‖) ^ (-(4 : ℤ))) :=
        hbase.comp_smul hΛpos.ne'
      have h3 : Integrable (fun z : E3 => Λ ^ 3 * (C₀ * (1 + ‖(Λ : ℝ) • z‖) ^ (-(4 : ℤ)))) :=
        h2.const_mul (Λ ^ 3)
      refine h3.congr ?_
      filter_upwards with z
      rw [hG_eq z]
    -- the pointwise bound: the weight cancels all but four powers of the decay
    have hpt : ∀ z : E3, |Work.BoseBoxFock.uvKernel fu Λ z| * (1 + Λ * ‖z‖) ^ j ≤ G z := by
      intro z
      have ha : (0 : ℝ) < 1 + Λ * ‖z‖ := by
        have h : (0 : ℝ) ≤ Λ * ‖z‖ := mul_nonneg hΛpos.le (norm_nonneg z)
        linarith
      have h1 : |Work.BoseBoxFock.uvKernel fu Λ z|
          ≤ C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-((j + 4 : ℕ) : ℤ)) := by
        rw [← Real.norm_eq_abs]
        exact hdec Λ hΛpos z
      have h2 : (0 : ℝ) ≤ (1 + Λ * ‖z‖) ^ j := by positivity
      have hpow : (1 + Λ * ‖z‖) ^ (-((j + 4 : ℕ) : ℤ)) * (1 + Λ * ‖z‖) ^ j
          = (1 + Λ * ‖z‖) ^ (-(4 : ℤ)) := by
        rw [← zpow_natCast (1 + Λ * ‖z‖) j, ← zpow_add₀ ha.ne']
        congr 1
        omega
      have h3 : C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-((j + 4 : ℕ) : ℤ)) * (1 + Λ * ‖z‖) ^ j
          = C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(4 : ℤ)) := by
        rw [mul_assoc, hpow]
      calc |Work.BoseBoxFock.uvKernel fu Λ z| * (1 + Λ * ‖z‖) ^ j
          ≤ (C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-((j + 4 : ℕ) : ℤ))) * (1 + Λ * ‖z‖) ^ j :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = C₀ * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(4 : ℤ)) := h3
        _ = G z := rfl
    have hmono : ∫ z, |Work.BoseBoxFock.uvKernel fu Λ z| * (1 + Λ * ‖z‖) ^ j ≤ ∫ z, G z :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => by positivity)) hIntG
        (Filter.Eventually.of_forall hpt)
    -- the scaling: `∫ z, G z` is independent of `Λ`
    have hGval : ∫ z, G z = ∫ y : E3, C₀ * (1 + ‖y‖) ^ (-(4 : ℤ)) := by
      have step1 : ∫ z, G z
          = ∫ z : E3, Λ ^ 3 * (C₀ * (1 + ‖(Λ : ℝ) • z‖) ^ (-(4 : ℤ))) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hG_eq z]
      rw [step1, integral_const_mul,
        Measure.integral_comp_smul volume (fun y : E3 => C₀ * (1 + ‖y‖) ^ (-(4 : ℤ))) Λ]
      have hfindim : Module.finrank ℝ E3 = 3 := by rw [finrank_euclideanSpace]; simp
      have hΛ3 : (0 : ℝ) < Λ ^ 3 := by positivity
      simp only [hfindim, smul_eq_mul]
      rw [abs_of_pos (inv_pos.mpr hΛ3), ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hΛ3), one_mul]
    have hGval' : ∫ z, G z = C₀ * ∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ)) := by
      rw [hGval, integral_const_mul]
    calc ∫ z, |Work.BoseBoxFock.uvKernel fu Λ z| * (1 + Λ * ‖z‖) ^ j
        ≤ ∫ z, G z := hmono
      _ = C₀ * ∫ y : E3, (1 + ‖y‖) ^ (-(4 : ℤ)) := hGval'

end Work.BoseBoxFock.PCFU
