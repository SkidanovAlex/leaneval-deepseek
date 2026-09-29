import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.expStepErr
import Submission.Work.Fx.ExpPosTdivKit

namespace Work.Resample

/-- Scaling step: if `u ≥ 0` and `A` approximates `T·q` to within `1`, then `A·u` approximates
`T·(q·u)` to within `u`. -/
theorem abs_mul_sub_scale (A T q u : ℝ) (hu : 0 ≤ u) (hA : |A - T * q| ≤ 1) :
    |A * u - T * (q * u)| ≤ u := by
  have heq : A * u - T * (q * u) = (A - T * q) * u := by ring
  rw [heq, abs_mul, abs_of_nonneg hu]
  simpa using mul_le_mul_of_nonneg_right hA hu

/-- `buZ p α s t ℓ h` is nonnegative and approximates `2^P · π · (α² N / s²)` to within
`1 + α² N / s²` (`P = auPrec p`, `N = buN s t ℓ h`).  The two error sources are the truncating
division by `s²` (error `≤ 1`, `ExpPosTdivKit`) and the π-approximation
`|auPi p - 2^P π| ≤ 1` (error `≤ α²N/s²`, scaled by the nonnegative factor `α²N/s²`). -/
theorem buZClose (p α s t : ℕ) (hp : 100 ≤ p) (hs : 2 ≤ s) (ℓ h : ℤ)
    (hN : 0 ≤ Work.Resample.buN s t ℓ h) (hPi0 : 0 ≤ Work.Resample.auPi p)
    (hPi1 : |(Work.Resample.auPi p : ℝ) - (2 : ℝ) ^ Work.Resample.auPrec p * Real.pi| ≤ 1) :
    0 ≤ Work.Resample.buZ p α s t ℓ h ∧
    |((Work.Resample.buZ p α s t ℓ h : ℤ) : ℝ)
        - (2 : ℝ) ^ Work.Resample.auPrec p * (Real.pi * ((α : ℝ) ^ 2 * (Work.Resample.buN s t ℓ h : ℝ) / (s : ℝ) ^ 2))|
      ≤ 1 + (α : ℝ) ^ 2 * (Work.Resample.buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 := by
  have hs1 : (1 : ℤ) ≤ (s : ℤ) := by omega
  have hs0Z : (0 : ℤ) ≤ (s : ℤ) := by omega
  have hsqZ : (1 : ℤ) ≤ (s : ℤ) ^ 2 := by
    calc (1 : ℤ) = 1 * 1 := by ring
      _ ≤ (s : ℤ) * (s : ℤ) := mul_le_mul hs1 hs1 (by norm_num) (by omega)
      _ = (s : ℤ) ^ 2 := by ring
  have hNR : (0 : ℝ) ≤ (buN s t ℓ h : ℝ) := by exact_mod_cast hN
  have hu_nn : (0 : ℝ) ≤ (α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (sq_nonneg (α : ℝ)) hNR) (sq_nonneg (s : ℝ))
  have hYnn : (0 : ℤ) ≤ auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h) :=
    mul_nonneg hPi0 (mul_nonneg (sq_nonneg (α : ℤ)) hN)
  obtain ⟨_, _, _, _, h5⟩ :=
    Work.Fx.ExpPosTdivKit (auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h)) ((s : ℤ) ^ 2) hsqZ
  have hYR : ((auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h) : ℤ) : ℝ)
      = (auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ)) := by push_cast; ring
  have hLR : (((s : ℤ) ^ 2 : ℤ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
  have hYdiv : ((auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h) : ℤ) : ℝ) / (((s : ℤ) ^ 2 : ℤ) : ℝ)
      = (auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2) := by
    rw [hYR, hLR, mul_div_assoc]
  have h1 : |(buZ p α s t ℓ h : ℝ)
      - (auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2)| ≤ 1 := by
    rw [buZ, ← hYdiv]
    exact h5
  have h2 : |(auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2)
      - (2 : ℝ) ^ (auPrec p) * (Real.pi * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2))| ≤
      (α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 :=
    abs_mul_sub_scale (auPi p : ℝ) ((2 : ℝ) ^ (auPrec p)) Real.pi
      ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2) hu_nn hPi1
  refine ⟨?_, ?_⟩
  · rw [buZ]
    exact Int.tdiv_nonneg hYnn (pow_nonneg hs0Z 2)
  · calc |(buZ p α s t ℓ h : ℝ)
          - (2 : ℝ) ^ (auPrec p) * (Real.pi * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2))|
        ≤ |(buZ p α s t ℓ h : ℝ)
            - (auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2)|
          + |(auPi p : ℝ) * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2)
            - (2 : ℝ) ^ (auPrec p) * (Real.pi * ((α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2))| :=
        abs_sub_le _ _ _
    _ ≤ 1 + (α : ℝ) ^ 2 * (buN s t ℓ h : ℝ) / (s : ℝ) ^ 2 := add_le_add h1 h2

end Work.Resample
