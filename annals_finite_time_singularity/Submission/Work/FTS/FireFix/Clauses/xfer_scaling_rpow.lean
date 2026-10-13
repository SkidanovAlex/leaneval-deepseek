import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

open MeasureTheory Set
open scoped ENNReal

/-- Change of variables `r = (B s)^{1/(3α)}` (`α > 0`, `B > 0`) for the Lebesgue
`lintegral` over the positive half-line. -/
theorem xfer_scaling_rpow {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {G : ℝ → ENNReal}
    (hG : AEMeasurable G MeasureTheory.volume) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * G r
      = ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * G ((B * s) ^ (1 / (3 * α))) := by
  -- `hG` is the a.e.-measurability hypothesis of the requested statement; the identity below
  -- in fact holds for an arbitrary `G : ℝ → ℝ≥0∞` (the one-dimensional change of variables
  -- formula for the `lintegral` needs no measurability of the integrand, and the constant is
  -- pulled out with `lintegral_const_mul'`, which only asks the constant to be finite).
  have _ := hG
  set p : ℝ := 1 / (3 * α) with hp
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hBne : B ≠ 0 := ne_of_gt hB
  -- the change-of-variables map `s ↦ (B s)^p`, its derivative, its image and its monotonicity
  have hderiv : ∀ s ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt (fun s : ℝ => (B*s)^p) (p * B ^ p * s ^ (p - 1)) (Set.Ioi 0) s := by
    intro s hs
    have hs0 : 0 < s := hs
    have hne : B * s ≠ 0 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => (B * t) ^ p) (p * (B * s) ^ (p - 1) * B) s :=
      (Real.hasDerivAt_rpow_const (Or.inl hne)).comp s
        (by simpa using (hasDerivAt_id s).const_mul B)
    have hBs : (B * s) ^ (p - 1) = B ^ (p - 1) * s ^ (p - 1) := Real.mul_rpow hB.le hs0.le
    have hBp : B ^ (p - 1) * B = B ^ p := by
      rw [← Real.rpow_add_one hBne (p - 1)]; congr 1; ring
    exact (h1.congr_deriv (by rw [hBs, ← hBp]; ring)).hasDerivWithinAt
  have himage : (fun s : ℝ => (B*s)^p) '' Set.Ioi (0:ℝ) = Set.Ioi 0 := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Real.rpow_pos_of_pos (mul_pos hB hs) p
    · intro hr
      refine ⟨r ^ (3*α) / B, ?_, ?_⟩
      · exact div_pos (Real.rpow_pos_of_pos hr _) hB
      · show (B * (r ^ (3*α) / B)) ^ p = r
        have hBmul : B * (r ^ (3*α) / B) = r ^ (3*α) := by field_simp
        rw [hBmul, hp, ← Real.rpow_mul hr.le (3*α) (1/(3*α))]
        rw [show (3:ℝ) * α * (1/(3*α)) = 1 by field_simp]
        exact Real.rpow_one r
  have hmono : MonotoneOn (fun s : ℝ => (B*s)^p) (Set.Ioi (0:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow (le_of_lt (mul_pos hB hx)) (by nlinarith [hB]) hp_pos.le
  -- the one-dimensional change of variables formula
  have hcov := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn (s := Set.Ioi (0:ℝ))
      (f := fun s : ℝ => (B*s)^p) (f' := fun s : ℝ => p * B ^ p * s ^ (p - 1))
      measurableSet_Ioi hderiv hmono (fun r : ℝ => ENNReal.ofReal (r ^ 2) * G r)
  rw [himage] at hcov
  -- the pointwise identification of the Jacobian factor
  have hpt : ∀ s ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (p*B^p*s^(p-1)) * (ENNReal.ofReal (((B*s)^p)^2) * G ((B*s)^p))
        = ENNReal.ofReal (B^(1/α)/(3*α)) * (ENNReal.ofReal (s^(1/α-1)) * G ((B*s)^p)) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hcoe : p*B^p*s^(p-1) * ((B*s)^p)^2 = (B^(1/α)/(3*α)) * s^(1/α-1) := by
      rw [hp]
      have hff2 : ((B*s) ^ (1/(3*α)))^2 = B^((1/(3*α))*2) * s^((1/(3*α))*2) := by
        rw [show ((B*s) ^ (1/(3*α)))^2 = ((B*s) ^ (1/(3*α)))^(2:ℝ) from (Real.rpow_two _).symm,
            ← Real.rpow_mul (le_of_lt (mul_pos hB hs0)) (1/(3*α)) 2, Real.mul_rpow hB.le hs0.le]
      have hBadd : B^(1/(3*α)) * B^((1/(3*α))*2) = B^(1/α) := by
        rw [← Real.rpow_add hB (1/(3*α)) ((1/(3*α))*2)]
        congr 1; field_simp; ring
      have hsadd : s^(1/(3*α)-1) * s^((1/(3*α))*2) = s^(1/α - 1) := by
        rw [← Real.rpow_add hs0 (1/(3*α)-1) ((1/(3*α))*2)]
        congr 1; field_simp; ring
      have hcoef : (1/(3*α)) * B^(1/α) = B^(1/α)/(3*α) := by
        rw [div_mul_eq_mul_div, one_mul]
      rw [hff2]
      calc (1/(3*α)) * B^(1/(3*α)) * s^(1/(3*α)-1) * (B^((1/(3*α))*2) * s^((1/(3*α))*2))
          = ((1/(3*α)) * (B^(1/(3*α)) * B^((1/(3*α))*2))) * (s^(1/(3*α)-1) * s^((1/(3*α))*2)) := by ring
        _ = ((1/(3*α)) * B^(1/α)) * s^(1/α-1) := by rw [hBadd, hsadd]
        _ = (B^(1/α)/(3*α)) * s^(1/α-1) := by rw [hcoef]
    have hA : 0 ≤ p*B^p*s^(p-1) :=
      le_of_lt (mul_pos (mul_pos hp_pos (Real.rpow_pos_of_pos hB p))
        (Real.rpow_pos_of_pos hs0 (p-1)))
    have hC : 0 ≤ B^(1/α)/(3*α) := div_nonneg (Real.rpow_nonneg hB.le _) (by positivity)
    calc ENNReal.ofReal (p*B^p*s^(p-1)) * (ENNReal.ofReal (((B*s)^p)^2) * G ((B*s)^p))
        = (ENNReal.ofReal (p*B^p*s^(p-1)) * ENNReal.ofReal (((B*s)^p)^2)) * G ((B*s)^p) := by ring
      _ = ENNReal.ofReal (p*B^p*s^(p-1) * ((B*s)^p)^2) * G ((B*s)^p) := by
            rw [← ENNReal.ofReal_mul hA]
      _ = ENNReal.ofReal ((B^(1/α)/(3*α)) * s^(1/α-1)) * G ((B*s)^p) := by rw [hcoe]
      _ = (ENNReal.ofReal (B^(1/α)/(3*α)) * ENNReal.ofReal (s^(1/α-1))) * G ((B*s)^p) := by
            rw [ENNReal.ofReal_mul hC]
      _ = ENNReal.ofReal (B^(1/α)/(3*α)) * (ENNReal.ofReal (s^(1/α-1)) * G ((B*s)^p)) := by ring
  calc ∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal (r^2) * G r
      = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (p*B^p*s^(p-1)) *
          (ENNReal.ofReal (((B*s)^p)^2) * G ((B*s)^p)) := hcov
    _ = ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (B^(1/α)/(3*α)) *
          (ENNReal.ofReal (s^(1/α-1)) * G ((B*s)^p)) :=
          setLIntegral_congr_fun measurableSet_Ioi hpt
    _ = ENNReal.ofReal (B^(1/α)/(3*α)) *
          ∫⁻ s in Set.Ioi (0:ℝ), ENNReal.ofReal (s^(1/α-1)) * G ((B*s)^p) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Work.FTS.FireFix.Clauses
