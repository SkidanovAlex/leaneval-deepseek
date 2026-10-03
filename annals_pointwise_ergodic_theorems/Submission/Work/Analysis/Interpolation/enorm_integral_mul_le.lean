import Mathlib
import Submission.Port.Aesm

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal

/-- **Hölder's inequality** for the pairing integral `∫ y, u y * v y ∂ν`: the `ℝ≥0∞`-valued norm
of the integral is bounded by the product of the `eLpNorm`s of `u` and `v` at conjugate exponents
`q` and `q / (q - 1)` (`1 < q`).  Only a.e.-measurability of `u` and `v` is assumed: the estimate
is stated in `ℝ≥0∞`, so the degenerate cases (`eLpNorm` zero or infinite) are absorbed by the
arithmetic of `ℝ≥0∞`. -/
theorem enorm_integral_mul_le {β : Type*} [MeasurableSpace β] {ν : Measure β} {q : ℝ} (hq : 1 < q)
    {u v : β → ℂ} (hu : AEMeasurable u ν) (hv : AEMeasurable v ν) :
    ‖∫ y, u y * v y ∂ν‖ₑ ≤
      eLpNorm u (ENNReal.ofReal q) ν * eLpNorm v (ENNReal.ofReal (q / (q - 1))) ν := by
  have hInst : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal (q / (q - 1))) 1 :=
    Real.HolderConjugate.ennrealOfReal ((Real.holderConjugate_iff_eq_conjExponent hq).mpr rfl)
  have hmul : eLpNorm (fun y => u y * v y) 1 ν ≤
      eLpNorm u (ENNReal.ofReal q) ν * eLpNorm v (ENNReal.ofReal (q / (q - 1))) ν := by
    simpa using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := ENNReal.ofReal q)
        (q := ENNReal.ofReal (q / (q - 1))) (r := 1) (fun a b => a * b) 1
        (by exact continuous_mul) hu.aestronglyMeasurable hv.aestronglyMeasurable
        (by filter_upwards with y; simp)
        (hpqr := hInst)
  calc ‖∫ y, u y * v y ∂ν‖ₑ ≤ ∫⁻ y, ‖u y * v y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun y => u y * v y) 1 ν := (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm
    _ ≤ eLpNorm u (ENNReal.ofReal q) ν * eLpNorm v (ENNReal.ofReal (q / (q - 1))) ν := hmul

end Work.Analysis.Interpolation
