import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.ExpPosTdivKit

namespace Work.Resample

/-- Scaling step: if `u ≥ 0` and `A` approximates `T·q` to within `1`, then `A·u` approximates
`T·(q·u)` to within `u`. -/
theorem buZb_abs_mul_sub_scale (A T q u : ℝ) (hu : 0 ≤ u) (hA : |A - T * q| ≤ 1) :
    |A * u - T * (q * u)| ≤ u := by
  have heq : A * u - T * (q * u) = (A - T * q) * u := by ring
  rw [heq, abs_mul, abs_of_nonneg hu]
  simpa using mul_le_mul_of_nonneg_right hA hu

/-- `buZb p α s t ℓ` is nonnegative and approximates `2^P · π · (α² β_ℓ² / s²)` to within
`1 + α² β_ℓ² / s²` (`P = auPrec p`, `β_ℓ = buBeta s t ℓ`).  Both error sources are as in
`buZClose`: the truncating division (error `≤ 1`) and the π-approximation `|auPi p - 2^P π| ≤ 1`,
the latter scaled by the nonnegative factor `α²β²/s²`.  Here only `s ≥ 1` is needed. -/
theorem buZbClose (p α s t : ℕ) (hp : 100 ≤ p) (hs : 0 < s) (ℓ : ℤ)
    (hPi0 : 0 ≤ Work.Resample.auPi p)
    (hPi1 : |(Work.Resample.auPi p : ℝ) - (2 : ℝ) ^ Work.Resample.auPrec p * Real.pi| ≤ 1) :
    0 ≤ Work.Resample.buZb p α s t ℓ ∧
    |((Work.Resample.buZb p α s t ℓ : ℤ) : ℝ)
        - (2 : ℝ) ^ Work.Resample.auPrec p *
          (Real.pi * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2))|
      ≤ 1 + (α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2 := by
  have hs1 : (1 : ℤ) ≤ (s : ℤ) := by omega
  have hs0Z : (0 : ℤ) ≤ (s : ℤ) := by omega
  have hsqZ : (1 : ℤ) ≤ (s : ℤ) ^ 2 := by
    calc (1 : ℤ) = 1 * 1 := by ring
      _ ≤ (s : ℤ) * (s : ℤ) := mul_le_mul hs1 hs1 (by norm_num) (by omega)
      _ = (s : ℤ) ^ 2 := by ring
  have hNR : (0 : ℝ) ≤ ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have hu_nn : (0 : ℝ) ≤ (α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (sq_nonneg (α : ℝ)) hNR) (sq_nonneg (s : ℝ))
  have hYnn : (0 : ℤ) ≤ auPi p * ((α : ℤ) ^ 2 * Work.Resample.buBeta s t ℓ ^ 2) :=
    mul_nonneg hPi0 (mul_nonneg (sq_nonneg (α : ℤ)) (sq_nonneg _))
  obtain ⟨_, _, _, _, h5⟩ :=
    Work.Fx.ExpPosTdivKit (auPi p * ((α : ℤ) ^ 2 * Work.Resample.buBeta s t ℓ ^ 2))
      ((s : ℤ) ^ 2) hsqZ
  have hYR : ((auPi p * ((α : ℤ) ^ 2 * Work.Resample.buBeta s t ℓ ^ 2) : ℤ) : ℝ)
      = (auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2) := by
    push_cast; ring
  have hLR : (((s : ℤ) ^ 2 : ℤ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
  have hYdiv :
      ((auPi p * ((α : ℤ) ^ 2 * Work.Resample.buBeta s t ℓ ^ 2) : ℤ) : ℝ) / (((s : ℤ) ^ 2 : ℤ) : ℝ)
      = (auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2) := by
    rw [hYR, hLR, mul_div_assoc]
  have h1 : |(Work.Resample.buZb p α s t ℓ : ℝ)
      - (auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2)|
      ≤ 1 := by
    rw [Work.Resample.buZb, ← hYdiv]
    exact h5
  have h2 : |(auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2)
      - (2 : ℝ) ^ (Work.Resample.auPrec p) *
        (Real.pi * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2))| ≤
      (α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2 :=
    buZb_abs_mul_sub_scale (auPi p : ℝ) ((2 : ℝ) ^ (Work.Resample.auPrec p)) Real.pi
      ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2) hu_nn hPi1
  refine ⟨?_, ?_⟩
  · rw [Work.Resample.buZb]
    exact Int.tdiv_nonneg hYnn (pow_nonneg hs0Z 2)
  · calc |(Work.Resample.buZb p α s t ℓ : ℝ)
          - (2 : ℝ) ^ (Work.Resample.auPrec p) *
            (Real.pi * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2))|
        ≤ |(Work.Resample.buZb p α s t ℓ : ℝ)
            - (auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2)|
          + |(auPi p : ℝ) * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2)
            - (2 : ℝ) ^ (Work.Resample.auPrec p) *
              (Real.pi * ((α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2))| :=
        abs_sub_le _ _ _
    _ ≤ 1 + (α : ℝ) ^ 2 * ((Work.Resample.buBeta s t ℓ : ℤ) : ℝ) ^ 2 / (s : ℝ) ^ 2 :=
        add_le_add h1 h2

end Work.Resample
