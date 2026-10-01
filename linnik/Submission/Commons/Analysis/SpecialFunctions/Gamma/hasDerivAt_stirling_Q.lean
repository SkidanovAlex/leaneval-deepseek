import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.SpecialFunctions.Gamma

theorem hasDerivAt_stirling_Q (u v : ℝ) (hu : 0 < u) :
    HasDerivAt (fun s : ℝ => (s - 1 / 2) * Real.log (Real.sqrt (s ^ 2 + v ^ 2)) - s
        + v * Real.arctan (s / v) - 1 / (12 * s))
      (Real.log (Real.sqrt (u ^ 2 + v ^ 2)) - u / (2 * (u ^ 2 + v ^ 2)) + 1 / (12 * u ^ 2)) u := by
  have hne : u ^ 2 + v ^ 2 ≠ 0 := by positivity
  have hsA : Real.sqrt (u ^ 2 + v ^ 2) ≠ 0 := by positivity
  -- Derivative of log(√(s²+v²))
  have hlog : HasDerivAt (fun s : ℝ => Real.log (Real.sqrt (s ^ 2 + v ^ 2)))
      (u / (u ^ 2 + v ^ 2)) u := by
    have hA : HasDerivAt (fun s : ℝ => s ^ 2 + v ^ 2) (2 * u) u := by
      simpa using ((hasDerivAt_id u).pow 2).add_const (v ^ 2)
    have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + v ^ 2))
        (u / Real.sqrt (u ^ 2 + v ^ 2)) u := by
      refine (hA.sqrt hne).congr_deriv ?_
      field_simp
    refine (hsqrt.log hsA).congr_deriv ?_
    rw [div_div]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  -- Derivative of (s - 1/2) * log(√(s²+v²))
  have h1 : HasDerivAt (fun s : ℝ => (s - 1 / 2) * Real.log (Real.sqrt (s ^ 2 + v ^ 2)))
      (Real.log (Real.sqrt (u ^ 2 + v ^ 2)) + (u - 1 / 2) * (u / (u ^ 2 + v ^ 2))) u := by
    have hlin : HasDerivAt (fun s : ℝ => s - 1 / 2) 1 u := (hasDerivAt_id u).sub_const (1 / 2)
    refine (hlin.mul hlog).congr_deriv ?_
    ring
  -- Derivative of s
  have h2 : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  -- Derivative of v * arctan(s/v)
  have h3 : HasDerivAt (fun s : ℝ => v * Real.arctan (s / v)) (v ^ 2 / (u ^ 2 + v ^ 2)) u := by
    have hdiv : HasDerivAt (fun s : ℝ => s / v) (1 / v) u := (hasDerivAt_id u).div_const v
    have harctan : HasDerivAt (fun s : ℝ => Real.arctan (s / v))
        (1 / (1 + (u / v) ^ 2) * (1 / v)) u := hdiv.arctan
    have h3' := harctan.const_mul v
    refine h3'.congr_deriv ?_
    rcases eq_or_ne v 0 with hv | hv
    · subst hv; simp
    · field_simp
      ring
  -- Derivative of 1/(12 s)
  have h4 : HasDerivAt (fun s : ℝ => 1 / (12 * s)) (-(1 / (12 * u ^ 2))) u := by
    have h4' : HasDerivAt (fun s : ℝ => 12 * s) 12 u := by
      simpa using (hasDerivAt_id u).const_mul 12
    have h4inv : HasDerivAt (fun s : ℝ => (12 * s)⁻¹) (-(12) / (12 * u) ^ 2) u :=
      h4'.inv (by positivity)
    have hfun : (fun s : ℝ => 1 / (12 * s)) = fun s : ℝ => (12 * s)⁻¹ := by
      ext s; rw [one_div]
    rw [hfun]
    refine h4inv.congr_deriv ?_
    field_simp
  have hcomb := ((h1.sub h2).add h3).sub h4
  refine hcomb.congr_deriv ?_
  field_simp
  ring

end Commons.Analysis.SpecialFunctions.Gamma