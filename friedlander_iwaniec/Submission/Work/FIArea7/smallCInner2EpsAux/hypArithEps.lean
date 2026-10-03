import Mathlib
import Submission.Work.FIArea7hyper.hyperbolaLogArith

namespace Work.FIArea7.smallCInner2EpsAux

lemma hypArithEps (u c0 : ℕ) (hu : 1 ≤ u) (C1 eps τ P I : ℝ)
    (hC1 : 0 < C1) (heps : 0 < eps) (hτnn : 0 ≤ τ) (hPnn : 0 ≤ P) (hInn : 0 ≤ I)
    (hIle : I ≤ Real.log (6 * (u : ℝ))) :
    ((Nat.log 2 u + 1 : ℕ) : ℝ) * (C1 * τ * P * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
        * ((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps) * I)
      ≤ C1 * (2 ^ ((11 : ℝ) / 12) * (2 ^ eps) * 10) * τ * P * ((u : ℝ) ^ ((11 : ℝ) / 12))
        * (((u : ℝ) + (c0 : ℝ) + 2) ^ eps)
        * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) := by
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huRpos : (0 : ℝ) < (u : ℝ) := by linarith
  have huRnn : (0 : ℝ) ≤ (u : ℝ) := le_of_lt huRpos
  set A : ℝ := ((Nat.log 2 u + 1 : ℕ) : ℝ) with hAdef
  set s : ℝ := Real.log ((u : ℝ) + 2) with hsdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  -- `log (6u) ≤ 2 log (u+2)`, `Nat.log 2 u + 1 ≤ 5 log (u+2)`: combined key bound
  have hkey : A * Real.log (6 * (u : ℝ)) ≤ 10 * s ^ 2 := by
    have hh := Work.FIArea7hyper.hyperbolaLogArith u hu
    rw [hAdef, hsdef]
    push_cast
    exact hh
  -- `(2u)^(11/12) = 2^(11/12) u^(11/12)`
  have hmul : (2 * (u : ℝ)) ^ ((11 : ℝ) / 12)
      = (2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12) :=
    Real.mul_rpow (by norm_num) huRnn
  -- `(2u + c0 + 2)^eps ≤ 2^eps (u + c0 + 2)^eps`
  have hbase : (2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps
      ≤ (2 : ℝ) ^ eps * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps := by
    have hc0 : (0 : ℝ) ≤ (c0 : ℝ) := Nat.cast_nonneg c0
    have hle : 2 * (u : ℝ) + (c0 : ℝ) + 2 ≤ 2 * ((u : ℝ) + (c0 : ℝ) + 2) := by linarith
    have hnn : (0 : ℝ) ≤ 2 * (u : ℝ) + (c0 : ℝ) + 2 := by positivity
    have h := Real.rpow_le_rpow hnn hle (le_of_lt heps)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : (0 : ℝ) ≤ (u : ℝ) + (c0 : ℝ) + 2)] at h
    exact h
  have hZnn : (0 : ℝ) ≤ C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12)) := by
    positivity
  have hXnn : (0 : ℝ) ≤ C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
      * ((2 : ℝ) ^ eps * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps) := by
    positivity
  have hFnn : (0 : ℝ) ≤ C1 * τ * P
      * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps * (u : ℝ) ^ ((11 : ℝ) / 12)
          * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps) := by
    positivity
  have hmain : A * (C1 * τ * P * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
        * ((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps) * I)
      ≤ (10 * s ^ 2) * (C1 * τ * P
          * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps * (u : ℝ) ^ ((11 : ℝ) / 12)
              * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps)) := by
    calc
      A * (C1 * τ * P * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
              * ((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps) * I)
          = A * ((C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
              * ((2 * (u : ℝ) + (c0 : ℝ) + 2) ^ eps)) * I) := by rw [hmul]
        _ ≤ A * ((C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
              * ((2 : ℝ) ^ eps * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps)) * I) := by
            apply mul_le_mul_of_nonneg_left _ hAnn
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hZnn) hInn
        _ ≤ A * ((C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
              * ((2 : ℝ) ^ eps * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps))
              * Real.log (6 * (u : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hAnn
            exact mul_le_mul_of_nonneg_left hIle hXnn
        _ = (C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps
              * (u : ℝ) ^ ((11 : ℝ) / 12) * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps))
              * (A * Real.log (6 * (u : ℝ))) := by ring
        _ ≤ (C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps
              * (u : ℝ) ^ ((11 : ℝ) / 12) * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps))
              * (10 * s ^ 2) := by
            exact mul_le_mul_of_nonneg_left hkey hFnn
        _ = (10 * s ^ 2) * (C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps
              * (u : ℝ) ^ ((11 : ℝ) / 12) * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps)) := by ring
  have hfinal : (10 * s ^ 2) * (C1 * τ * P * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps
        * (u : ℝ) ^ ((11 : ℝ) / 12) * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps))
      = C1 * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (2 : ℝ) ^ eps * 10) * τ * P
        * (u : ℝ) ^ ((11 : ℝ) / 12) * ((u : ℝ) + (c0 : ℝ) + 2) ^ eps * s ^ (2 : ℝ) := by
    rw [Real.rpow_two]; ring
  exact le_trans hmain (le_of_eq hfinal)

end Work.FIArea7.smallCInner2EpsAux
