import Mathlib
import Submission.Work.C7.xdefs

namespace Work.C7

open PowerSeries

/-- `yps = x²/(x-1)` as `x²·(x-1)⁻¹`. -/
private lemma yps_eq : yps = (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1)⁻¹ := by
  rw [yps, Submission.CDT.sympY, Submission.CDT.sympPhi]; ring

/-- `(x-1)²·yps = x²·(x-1)`. -/
private lemma subOne_sq_mul_yps :
    ((X : PowerSeries ℚ) - 1) ^ 2 * yps = (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1) := by
  have hu : ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne
  rw [yps_eq]
  linear_combination ((X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1)) * hu

/-- `yps' = x(x-2)/(x-1)²`. -/
private lemma deriv_yps : (PowerSeries.derivative (R := ℚ)) yps
    = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
  have hu : ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne
  have h11 : (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) - 1) = 1 := by
    rw [show ((X : PowerSeries ℚ) - 1) = (X : PowerSeries ℚ) - 1 by rfl, map_sub]
    simp
  have hdu : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1)⁻¹)
      = -(((X : PowerSeries ℚ) - 1)⁻¹) ^ 2 := by
    rw [PowerSeries.derivative_inv', h11]; ring
  have hX2 : (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) ^ 2) = 2 * (X : PowerSeries ℚ) := by
    rw [show (X : PowerSeries ℚ) ^ 2 = X * X by ring, Derivation.leibniz]
    simp only [smul_eq_mul, PowerSeries.derivative_X]
    ring
  rw [yps_eq, Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [hX2, hdu]
  linear_combination (-(2 * (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 1)⁻¹)) * hu

/-- `(x-1)²·yps' = x(x-2)`. -/
private lemma subOne_sq_mul_deriv_yps :
    ((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) yps
      = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) := by
  have hu : ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne
  rw [deriv_yps]
  linear_combination
    ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)
      * (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ + 1)) * hu

/-- `(x-1)·(x - φ) = x(x-2)`. -/
private lemma subOne_mul_sub_phi :
    ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
      = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) := by
  have hu : ((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - 1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne
  have hphi : Submission.CDT.sympPhi = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 1)⁻¹ := rfl
  rw [hphi]
  linear_combination (-(X : PowerSeries ℚ)) * hu

/-- `2·(1/2) = 1` in `ℚ⟦x⟧`. -/
private lemma two_mul_C_half : (2 : PowerSeries ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from by
        rw [PowerSeries.C_eq_algebraMap]
        exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm,
      ← map_mul]
  norm_num

theorem g67_deriv
    (h2 : Work.C7.g 2 = -(PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)
    (h3 : Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
    (h6 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5) = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps)
    (h7 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6) = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps) :
    (2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) (Work.C7.g 5) = -(PowerSeries.X - 2) * Work.C7.Lps ^ 2) ∧
    ((PowerSeries.X - 1) ^ 2 * PowerSeries.derivative (R := ℚ) (Work.C7.g 6)
      = (PowerSeries.X - 2) ^ 2 * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)) := by
  have h2' : Work.C7.g 2 = -(PowerSeries.C (1/2 : ℚ) * Work.C7.Lps ^ 2) := by rw [h2]; ring
  have htwo := two_mul_C_half
  constructor
  · -- first identity: clear the denominators of `yps` and `yps'`
    have hg5 : (X : PowerSeries ℚ)
          * ((2 * (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 1))
              * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 5))
        = (X : PowerSeries ℚ) * ((-((X : PowerSeries ℚ) - 2)) * Work.C7.Lps ^ 2) := by
      calc (X : PowerSeries ℚ)
              * ((2 * (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 1))
                  * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 5))
          = (2 * (((X : PowerSeries ℚ) - 1) ^ 2 * Work.C7.yps))
              * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 5) := by
                rw [subOne_sq_mul_yps]; ring
        _ = (2 * ((X : PowerSeries ℚ) - 1) ^ 2)
              * (Work.C7.yps * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 5)) := by ring
        _ = (2 * ((X : PowerSeries ℚ) - 1) ^ 2)
              * ((Work.C7.g 2) * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by rw [h6]
        _ = (2 * ((X : PowerSeries ℚ) - 1) ^ 2)
              * ((-(PowerSeries.C (1/2 : ℚ) * Work.C7.Lps ^ 2))
                  * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by rw [h2']
        _ = (2 * (-(PowerSeries.C (1/2 : ℚ) * Work.C7.Lps ^ 2)))
              * (((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by ring
        _ = (2 * (-(PowerSeries.C (1/2 : ℚ) * Work.C7.Lps ^ 2)))
              * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) := by rw [subOne_sq_mul_deriv_yps]
        _ = (X : PowerSeries ℚ) * ((-((X : PowerSeries ℚ) - 2)) * Work.C7.Lps ^ 2) := by
              rw [show (2 : PowerSeries ℚ) * (-(PowerSeries.C (1/2 : ℚ) * Work.C7.Lps ^ 2))
                    = -((2 * PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2) by ring, htwo]
              ring
    exact mul_left_cancel₀ PowerSeries.X_ne_zero hg5
  · -- second identity
    have hE : (X : PowerSeries ℚ) ^ 2
          * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6))
        = (((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
              * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
            * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) := by
      calc (X : PowerSeries ℚ) ^ 2
              * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6))
          = (((X : PowerSeries ℚ) - 1) ^ 2 * Work.C7.yps)
              * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6) := by
                rw [subOne_sq_mul_yps]; ring
        _ = ((X : PowerSeries ℚ) - 1) ^ 2
              * (Work.C7.yps * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6)) := by ring
        _ = ((X : PowerSeries ℚ) - 1) ^ 2
              * ((Work.C7.g 3) * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by rw [h7]
        _ = ((X : PowerSeries ℚ) - 1) ^ 2
              * ((((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
                    * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
                  * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by rw [h3]
        _ = (((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
                * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
              * (((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) Work.C7.yps) := by ring
        _ = (((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
                * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
              * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) := by rw [subOne_sq_mul_deriv_yps]
    have hF : (X : PowerSeries ℚ) ^ 2
          * (((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6))
        = (X : PowerSeries ℚ) ^ 2
          * (((X : PowerSeries ℚ) - 2) ^ 2
              * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)) := by
      calc (X : PowerSeries ℚ) ^ 2
              * (((X : PowerSeries ℚ) - 1) ^ 2 * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6))
          = ((X : PowerSeries ℚ) - 1)
              * ((X : PowerSeries ℚ) ^ 2
                  * (((X : PowerSeries ℚ) - 1) * (PowerSeries.derivative (R := ℚ)) (Work.C7.g 6))) := by ring
        _ = ((X : PowerSeries ℚ) - 1)
              * ((((X : PowerSeries ℚ) - Submission.CDT.sympPhi)
                    * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
                  * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2))) := by rw [hE]
        _ = (((X : PowerSeries ℚ) - 1) * ((X : PowerSeries ℚ) - Submission.CDT.sympPhi))
              * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)
              * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) := by ring
        _ = ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2))
              * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)
              * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) := by rw [subOne_mul_sub_phi]
        _ = (X : PowerSeries ℚ) ^ 2
              * (((X : PowerSeries ℚ) - 2) ^ 2
                  * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)) := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 PowerSeries.X_ne_zero) hF

end Work.C7
