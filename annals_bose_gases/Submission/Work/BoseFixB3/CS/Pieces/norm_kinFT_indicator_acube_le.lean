import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.OneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- Trivial sup bound for the `p`-Fourier transform of a function supported in the
centred cube `acube ℓ` and bounded by `D` there: since `|e^{−i⟪p,y⟫}| = 1`, the
transform is at most `∫_{acube ℓ}|ψ| ≤ D·vol(acube ℓ) = D ℓ³`. -/
theorem norm_kinFT_indicator_acube_le {ℓ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψm : Measurable ψ)
    (hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ D)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖Submission.BoseGases.kinFT
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) p‖
      ≤ D * ℓ ^ 3 := by
  set s := Submission.BoseGases.acube ℓ with hs_def
  have hs_meas : MeasurableSet s := by
    rw [hs_def]; exact Submission.BoseGases.acube_measurable ℓ
  have hs_lt_top : (volume : Measure (EuclideanSpace ℝ (Fin 3))) s < ⊤ := by
    rw [hs_def]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le
  -- the transform of the truncated function is the integral of the phase against `ψ` over `s`
  have hpt : ∀ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        (((s.indicator ψ y : ℝ)) : ℂ)
      = s.indicator
          (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (ψ y : ℂ)) y := by
    intro y
    by_cases hy : y ∈ s <;> simp [Set.indicator, hy]
  have hkey : Submission.BoseGases.kinFT
        (fun z : EuclideanSpace ℝ (Fin 3) => (((s.indicator ψ z : ℝ)) : ℂ)) p
      = ∫ y in s, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (ψ y : ℂ) := by
    rw [Submission.BoseGases.kinFT]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_indicator hs_meas
  rw [hkey]
  -- the integrand has norm `|ψ| ≤ D` on `s`
  have hb : ∀ y ∈ s,
      ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (ψ y : ℂ)‖ ≤ D := by
    intro y hy
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero, one_mul]
    simpa [hs_def] using hψb y hy
  calc ‖∫ y in s, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (ψ y : ℂ)‖
      ≤ D * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real s :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_lt_top hb
    _ = D * ℓ ^ 3 := by
        rw [MeasureTheory.Measure.real, hs_def,
          Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]

end Work.BoseFixB3.CS.Pieces
