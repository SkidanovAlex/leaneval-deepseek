import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Ebs

open MeasureTheory

/-- Cauchy–Schwarz (Bunyakovsky) in the `L²` form, written with square roots: for real functions
`u`, `v` that are square-integrable on a set `s`,
`|∫_s u v| ≤ √(∫_s u²) · √(∫_s v²)`.

The proof uses Hölder's inequality `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` with
`p = q = 2`, after bounding `|∫ u v| ≤ ∫ |u| |v|` and replacing `|u|²` by `u²` inside the
integrals. -/
theorem abs_integral_mul_le_sqrt {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict s)) :
    |∫ x in s, u x * v x| ≤ Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
  have h1 : |∫ x in s, u x * v x| ≤ ∫ x in s, |u x| * |v x| := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict s)
        (f := fun x => u x * v x))
  have hu2 : MemLp u (ENNReal.ofReal (2 : ℝ)) (volume.restrict s) := by simpa using hu
  have hv2 : MemLp v (ENNReal.ofReal (2 : ℝ)) (volume.restrict s) := by simpa using hv
  have h2 : ∫ x in s, |u x| * |v x| ≤
      (∫ x in s, |u x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x in s, |v x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict s)
        (p := 2) (q := 2) (f := u) (g := v) (by norm_num [Real.holderConjugate_iff]) hu2 hv2)
  have hA : (∫ x in s, |u x| ^ (2 : ℝ)) = ∫ x in s, u x ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by simpa using sq_abs (u x)))
  have hB : (∫ x in s, |v x| ^ (2 : ℝ)) = ∫ x in s, v x ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by simpa using sq_abs (v x)))
  calc |∫ x in s, u x * v x| ≤ ∫ x in s, |u x| * |v x| := h1
    _ ≤ (∫ x in s, |u x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ x in s, |v x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := h2
    _ = Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
        rw [hA, hB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

end Work.FTS.EllipticEst.remov.Ebs
