import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Commons.Analysis.Complex.contour_shift_residue

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

/-- Cauchy's theorem for the rectangle with vertical sides on `Re = a`, `Re = b` and horizontal
sides on `Im = -T`, `Im = T`. -/
private lemma rect_vert_identity {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ g z) :
    (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      - (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      = (∫ u : ℝ in a..b, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u : ℝ in a..b, g ((u : ℂ) - (T : ℂ) * Complex.I)) := by
  set z : ℂ := (a : ℂ) + (-T : ℂ) * Complex.I with hzdef
  set w : ℂ := (b : ℂ) + (T : ℂ) * Complex.I with hwdef
  have hzre : z.re = a := by simp [z]
  have hzim : z.im = -T := by simp [z]
  have hwre : w.re = b := by simp [w]
  have hwim : w.im = T := by simp [w]
  have hd : DifferentiableOn ℂ g (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    rw [hzre, hwre, hzim, hwim]
    intro z' hz'
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith : -T ≤ T)] at hz'
    exact (hdiff z' hz'.1.1 hz'.1.2).differentiableWithinAt
  have hraw : ((∫ x : ℝ in a..b, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b, g ((x : ℂ) + (T : ℂ) * Complex.I)))
      + Complex.I * (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g z w hd
    rw [hzre, hwre, hzim, hwim] at h
    simpa using h
  have hPI : (∫ x : ℝ in a..b, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = ∫ x : ℝ in a..b, g ((x : ℂ) - (T : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg g
    push_cast
    ring
  have hCb : Complex.I * (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I) * Complex.I := by
    rw [intervalIntegral.integral_mul_const, mul_comm]
  have hCa : Complex.I * (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I := by
    rw [intervalIntegral.integral_mul_const, mul_comm]
  have hkey : (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      - (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      = (∫ x : ℝ in a..b, g ((x : ℂ) + (T : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    rw [← hCb, ← hCa]
    linear_combination hraw
  rw [hkey, hPI]

theorem vertical_shift_analytic {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (g : ℂ → ℂ)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ g z)
    (hinta : MeasureTheory.Integrable (fun t : ℝ => g ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I))
    (hintb : MeasureTheory.Integrable (fun t : ℝ => g ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I))
    (hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in a..b, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in a..b, g ((u : ℂ) - (T : ℂ) * Complex.I))) Filter.atTop (nhds 0)) :
    (∫ t : ℝ, g ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = ∫ t : ℝ, g ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I := by
  have hb := intervalIntegral_tendsto_integral hintb tendsto_neg_atTop_atBot tendsto_id
  have ha' := intervalIntegral_tendsto_integral hinta tendsto_neg_atTop_atBot tendsto_id
  have hLHS : Filter.Tendsto (fun T : ℝ =>
      (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
        - (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I))
      Filter.atTop (nhds ((∫ t : ℝ, g ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        - ∫ t : ℝ, g ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I)) := hb.sub ha'
  have heq : (fun T : ℝ =>
      (∫ y : ℝ in (-T)..T, g ((b : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
        - (∫ y : ℝ in (-T)..T, g ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I))
      =ᶠ[Filter.atTop] (fun T : ℝ =>
      (∫ u in a..b, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in a..b, g ((u : ℂ) - (T : ℂ) * Complex.I))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rect_vert_identity hab hT.le hdiff
  have hLHS0 : Filter.Tendsto (fun T : ℝ =>
      (∫ u in a..b, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in a..b, g ((u : ℂ) - (T : ℂ) * Complex.I)))
      Filter.atTop (nhds ((∫ t : ℝ, g ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        - ∫ t : ℝ, g ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I)) :=
    hLHS.congr' heq
  have hzero : (∫ t : ℝ, g ((b : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      - ∫ t : ℝ, g ((a : ℂ) + (t : ℂ) * Complex.I) * Complex.I = 0 :=
    tendsto_nhds_unique hLHS0 hhoriz
  exact sub_eq_zero.mp hzero

end Commons.Analysis.Complex