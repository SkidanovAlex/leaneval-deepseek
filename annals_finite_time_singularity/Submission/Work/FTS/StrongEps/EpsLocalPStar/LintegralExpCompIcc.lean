import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory in
/-- Change of variables for the substitution `p ↦ z * exp (-(ε * p))` on `[-1, 1]`, in the
form needed by the strong-`ε` construction: the map is an antitone diffeomorphism of
`[-1, 1]` onto `[z * exp (-ε), z * exp ε]` whose Jacobian factor
`ε * z * exp (-(ε * p))` is bounded below by `ε * z * exp (-ε)` on the interval. -/
theorem LintegralExpCompIcc {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) (F : ℝ → ENNReal) :
    ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))
      ≤ ENNReal.ofReal (1 / (ε * z * Real.exp (-ε)))
        * ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
  have hcpos : 0 < ε * z * Real.exp (-ε) := by positivity
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun p : ℝ => z * Real.exp (-(ε * p)))
        (-(ε * (z * Real.exp (-(ε * x))))) (Set.Icc (-1 : ℝ) 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun p : ℝ => -(ε * p)) (-ε) x := by
      have h : HasDerivAt (fun p : ℝ => (-ε) * p) (-ε) x := hasDerivAt_const_mul (x := x) (-ε)
      simpa only [neg_mul] using h
    have h2 : HasDerivAt (fun p : ℝ => Real.exp (-(ε * p)))
        (Real.exp (-(ε * x)) * (-ε)) x := h1.exp
    have h3 : HasDerivAt (fun p : ℝ => z * Real.exp (-(ε * p)))
        (z * (Real.exp (-(ε * x)) * (-ε))) x := h2.const_mul z
    have heq : z * (Real.exp (-(ε * x)) * (-ε)) = -(ε * (z * Real.exp (-(ε * x)))) := by ring
    rw [heq] at h3
    exact h3.hasDerivWithinAt
  have hcont : ContinuousOn (fun p : ℝ => z * Real.exp (-(ε * p))) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hanti : AntitoneOn (fun p : ℝ => z * Real.exp (-(ε * p))) (Set.Icc (-1 : ℝ) 1) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hz.le
  have himg : (fun p : ℝ => z * Real.exp (-(ε * p))) '' Set.Icc (-1 : ℝ) 1
      = Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε) := by
    have h := hcont.image_Icc_of_antitoneOn (show (-1 : ℝ) ≤ 1 by norm_num) hanti
    simpa using h
  have hcov' : ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u
      = ∫⁻ p in Set.Icc (-1 : ℝ) 1,
          ENNReal.ofReal (ε * (z * Real.exp (-(ε * p)))) * F (z * Real.exp (-(ε * p))) := by
    have h := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := Set.Icc (-1 : ℝ) 1) (f := fun p : ℝ => z * Real.exp (-(ε * p)))
      (f' := fun x : ℝ => -(ε * (z * Real.exp (-(ε * x))))) measurableSet_Icc hderiv hanti F
    rw [himg] at h
    simpa only [neg_neg] using h
  have hpt : ∀ p ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (ε * z * Real.exp (-ε)) * F (z * Real.exp (-(ε * p)))
        ≤ ENNReal.ofReal (ε * (z * Real.exp (-(ε * p)))) * F (z * Real.exp (-(ε * p))) := by
    intro p hp
    have hp1 : p ≤ 1 := hp.2
    have hexp : Real.exp (-ε) ≤ Real.exp (-(ε * p)) := Real.exp_le_exp.mpr (by nlinarith)
    have hzexp : z * Real.exp (-ε) ≤ z * Real.exp (-(ε * p)) :=
      mul_le_mul_of_nonneg_left hexp hz.le
    have hle : ε * z * Real.exp (-ε) ≤ ε * (z * Real.exp (-(ε * p))) := by
      calc ε * z * Real.exp (-ε) = ε * (z * Real.exp (-ε)) := by ring
        _ ≤ ε * (z * Real.exp (-(ε * p))) := mul_le_mul_of_nonneg_left hzexp hε.le
    exact mul_le_mul_left (ENNReal.ofReal_mono hle) (F (z * Real.exp (-(ε * p))))
  have hstep1 : ∫⁻ p in Set.Icc (-1 : ℝ) 1,
        ENNReal.ofReal (ε * z * Real.exp (-ε)) * F (z * Real.exp (-(ε * p)))
      ≤ ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
    rw [hcov']
    exact MeasureTheory.setLIntegral_mono' measurableSet_Icc hpt
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hstep1
  have hcne : ENNReal.ofReal (ε * z * Real.exp (-ε)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hcpos
  have hctop : ENNReal.ofReal (ε * z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hconsteq : (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹
      = ENNReal.ofReal (1 / (ε * z * Real.exp (-ε))) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hcpos]
  calc ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))
      = (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹ *
          (ENNReal.ofReal (ε * z * Real.exp (-ε)) *
            ∫⁻ p in Set.Icc (-1 : ℝ) 1, F (z * Real.exp (-(ε * p)))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
    _ ≤ (ENNReal.ofReal (ε * z * Real.exp (-ε)))⁻¹ *
          ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u :=
        mul_le_mul_right hstep1 _
    _ = ENNReal.ofReal (1 / (ε * z * Real.exp (-ε))) *
          ∫⁻ u in Set.Icc (z * Real.exp (-ε)) (z * Real.exp ε), F u := by
        rw [hconsteq]

end Work.FTS.StrongEps.EpsLocalPStar
