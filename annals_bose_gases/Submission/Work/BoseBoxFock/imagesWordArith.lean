import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.sideAt_large
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesWordArith`

The scalar (`rpow`) arithmetic of the images-word budget, at the box side
`ℓ = sideAt μ α = α (μα³)^{-163/323}` and diluteness `t = μα³ ≤ 1`:

    (R/ℓ)^6 · μ² · ℓ^{9/2} · (1 + kk √(μℓ³))  ≤  R^6 α^{-11/2} (1 + kk) (μα) .

Everything is the two sharp identifications of the side

* `ℓ^{-3/2} = α^{-3/2} t^{489/646}`  (`sideAt_eq_rpow`),
* `μℓ³ = t^{-166/323}`, hence `√(μℓ³) = t^{-83/323}`  (`mu_ell_cube_fsParams`),

which turn the left side into

    R^6 (μ² ℓ^{-3/2} + kk · μ² ℓ^{-3/2} √(μℓ³)) = R^6 α^{-9/2} μ (t^{1135/646} + kk · t^{3/2}),

and both exponents are positive, so `t ≤ 1` bounds the bracket by `1 + kk`.
-/

namespace Work.BoseBoxFock

theorem imagesWordArith {α R kk μ : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hkk : 0 ≤ kk) (ht1 : μ * α ^ 3 ≤ 1) :
    (R / Work.BoseBox.sideAt μ α) ^ 6 * μ ^ 2 * (Work.BoseBox.sideAt μ α) ^ ((9 : ℝ) / 2)
        * (1 + kk * Real.sqrt (μ * (Work.BoseBox.sideAt μ α) ^ 3))
      ≤ R ^ 6 * α ^ (-(11 / 2) : ℝ) * (1 + kk) * (μ * α) := by
  have ht : 0 < μ * α ^ 3 := by positivity
  set ℓ : ℝ := Work.BoseBox.sideAt μ α with hℓdef
  have hℓpos : 0 < ℓ := by
    rw [hℓdef]
    exact Work.BoseBox.boxSide_pos hμ hα (Work.BoseBox.fsXp_pos (by positivity))
  -- ## the two `rpow` identifications of the side
  have hL : ℓ ^ (-(3 / 2) : ℝ)
      = α ^ (-(3 / 2) : ℝ) * (μ * α ^ 3) ^ ((489 : ℝ) / 646) := by
    rw [hℓdef, Work.BoseBox.sideAt_eq_rpow hα hμ,
      Real.mul_rpow hα.le (Real.rpow_nonneg ht.le _)]
    congr 1
    rw [← Real.rpow_mul ht.le]
    norm_num
  have hμℓ3 : μ * ℓ ^ 3 = (μ * α ^ 3) ^ (-(166 / 323) : ℝ) := by
    rw [hℓdef]
    have h := Work.BoseBox.mu_ell_cube_fsParams (a := α) hμ hα
    simpa [Work.BoseBox.sideAt, Work.BoseBox.paramsAt] using h
  have hS : Real.sqrt (μ * ℓ ^ 3) = (μ * α ^ 3) ^ (-(83 / 323) : ℝ) := by
    rw [Real.sqrt_eq_rpow, hμℓ3, ← Real.rpow_mul ht.le]
    norm_num
  -- ## the `α`-exponent bookkeeping: `α^{-3/2} α^{9/2} = α³`
  have hα1 : α ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2) = α ^ 3 := by
    have h : α ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2) = α ^ ((3 : ℕ) : ℝ) := by
      rw [← Real.rpow_add hα (-(3 / 2) : ℝ) ((9 : ℝ) / 2)]
      norm_num
    rwa [Real.rpow_natCast] at h
  -- ## the two core inequalities, after multiplying by `α^{9/2}`
  -- `μ² ℓ^{-3/2} α^{9/2} ≤ μ`
  have h1a : μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2) ≤ μ := by
    rw [hL]
    have htc : (μ * α ^ 3) * (μ * α ^ 3) ^ ((489 : ℝ) / 646)
        = (μ * α ^ 3) ^ ((1135 : ℝ) / 646) := by
      calc (μ * α ^ 3) * (μ * α ^ 3) ^ ((489 : ℝ) / 646)
          = (μ * α ^ 3) ^ (1 : ℝ) * (μ * α ^ 3) ^ ((489 : ℝ) / 646) := by
            rw [Real.rpow_one]
        _ = (μ * α ^ 3) ^ ((1135 : ℝ) / 646) := by
            rw [← Real.rpow_add ht (1 : ℝ) ((489 : ℝ) / 646)]
            norm_num
    calc μ ^ 2 * (α ^ (-(3 / 2) : ℝ) * (μ * α ^ 3) ^ ((489 : ℝ) / 646))
          * α ^ ((9 : ℝ) / 2)
        = μ ^ 2 * (α ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2)
            * (μ * α ^ 3) ^ ((489 : ℝ) / 646)) := by ring
      _ = μ ^ 2 * (α ^ 3 * (μ * α ^ 3) ^ ((489 : ℝ) / 646)) := by rw [hα1]
      _ = μ * ((μ * α ^ 3) * (μ * α ^ 3) ^ ((489 : ℝ) / 646)) := by ring
      _ = μ * (μ * α ^ 3) ^ ((1135 : ℝ) / 646) := by rw [htc]
      _ ≤ μ * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one ht.le ht1 (by norm_num : (0 : ℝ) ≤ 1135 / 646)) hμ.le
      _ = μ := mul_one μ
  -- `μ² ℓ^{-3/2} √(μℓ³) α^{9/2} ≤ μ`
  have h2a : μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3) * α ^ ((9 : ℝ) / 2)
      ≤ μ := by
    rw [hL, hS]
    have hAB : (μ * α ^ 3) ^ ((489 : ℝ) / 646) * (μ * α ^ 3) ^ (-(83 / 323) : ℝ)
        = (μ * α ^ 3) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add ht ((489 : ℝ) / 646) (-(83 / 323) : ℝ)]
      norm_num
    have htc : (μ * α ^ 3) * (μ * α ^ 3) ^ ((1 : ℝ) / 2)
        = (μ * α ^ 3) ^ ((3 : ℝ) / 2) := by
      calc (μ * α ^ 3) * (μ * α ^ 3) ^ ((1 : ℝ) / 2)
          = (μ * α ^ 3) ^ (1 : ℝ) * (μ * α ^ 3) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_one]
        _ = (μ * α ^ 3) ^ ((3 : ℝ) / 2) := by
            rw [← Real.rpow_add ht (1 : ℝ) ((1 : ℝ) / 2)]
            norm_num
    calc μ ^ 2 * (α ^ (-(3 / 2) : ℝ) * (μ * α ^ 3) ^ ((489 : ℝ) / 646))
          * (μ * α ^ 3) ^ (-(83 / 323) : ℝ) * α ^ ((9 : ℝ) / 2)
        = μ ^ 2 * (α ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2)
            * ((μ * α ^ 3) ^ ((489 : ℝ) / 646)
              * (μ * α ^ 3) ^ (-(83 / 323) : ℝ))) := by ring
      _ = μ ^ 2 * (α ^ 3
            * ((μ * α ^ 3) ^ ((489 : ℝ) / 646)
              * (μ * α ^ 3) ^ (-(83 / 323) : ℝ))) := by rw [hα1]
      _ = μ ^ 2 * (α ^ 3 * (μ * α ^ 3) ^ ((1 : ℝ) / 2)) := by rw [hAB]
      _ = μ * ((μ * α ^ 3) * (μ * α ^ 3) ^ ((1 : ℝ) / 2)) := by ring
      _ = μ * (μ * α ^ 3) ^ ((3 : ℝ) / 2) := by rw [htc]
      _ ≤ μ * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one ht.le ht1 (by norm_num : (0 : ℝ) ≤ 3 / 2)) hμ.le
      _ = μ := mul_one μ
  -- ## divide the `α^{9/2}` back out
  have hαinv : α ^ ((9 : ℝ) / 2) * α ^ (-(9 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hα ((9 : ℝ) / 2) (-(9 / 2) : ℝ),
      show ((9 : ℝ) / 2) + (-(9 / 2)) = 0 by norm_num, Real.rpow_zero]
  have h1 : μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) ≤ α ^ (-(9 / 2) : ℝ) * μ := by
    have h := mul_le_mul_of_nonneg_right h1a (Real.rpow_nonneg hα.le (-(9 / 2) : ℝ))
    calc μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ)
        = μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ)
          * (α ^ ((9 : ℝ) / 2) * α ^ (-(9 / 2) : ℝ)) := by rw [hαinv, mul_one]
      _ = (μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * α ^ ((9 : ℝ) / 2)) * α ^ (-(9 / 2) : ℝ) := by
          ring
      _ ≤ μ * α ^ (-(9 / 2) : ℝ) := h
      _ = α ^ (-(9 / 2) : ℝ) * μ := by exact mul_comm _ _
  have h2 : μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3)
      ≤ α ^ (-(9 / 2) : ℝ) * μ := by
    have h := mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hα.le (-(9 / 2) : ℝ))
    calc μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3)
        = μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3)
          * (α ^ ((9 : ℝ) / 2) * α ^ (-(9 / 2) : ℝ)) := by rw [hαinv, mul_one]
      _ = (μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3)
            * α ^ ((9 : ℝ) / 2)) * α ^ (-(9 / 2) : ℝ) := by ring
      _ ≤ μ * α ^ (-(9 / 2) : ℝ) := h
      _ = α ^ (-(9 / 2) : ℝ) * μ := by exact mul_comm _ _
  -- ## the two sides in factored form
  have hLHS : (R / ℓ) ^ 6 * μ ^ 2 * ℓ ^ ((9 : ℝ) / 2) * (1 + kk * Real.sqrt (μ * ℓ ^ 3))
      = R ^ 6 * (μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * (1 + kk * Real.sqrt (μ * ℓ ^ 3))) := by
    have hcomb : (R / ℓ) ^ 6 * ℓ ^ ((9 : ℝ) / 2) = R ^ 6 * ℓ ^ (-(3 / 2) : ℝ) := by
      have hc : (ℓ ^ ((6 : ℕ) : ℝ))⁻¹ * ℓ ^ ((9 : ℝ) / 2) = ℓ ^ (-(3 / 2) : ℝ) := by
        rw [← Real.rpow_neg hℓpos.le, ← Real.rpow_add hℓpos]
        norm_num
      calc (R / ℓ) ^ 6 * ℓ ^ ((9 : ℝ) / 2)
          = (R ^ 6 * (ℓ ^ ((6 : ℕ) : ℝ))⁻¹) * ℓ ^ ((9 : ℝ) / 2) := by
            rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast ℓ 6]
        _ = R ^ 6 * ((ℓ ^ ((6 : ℕ) : ℝ))⁻¹ * ℓ ^ ((9 : ℝ) / 2)) := by ring
        _ = R ^ 6 * ℓ ^ (-(3 / 2) : ℝ) := by rw [hc]
    calc (R / ℓ) ^ 6 * μ ^ 2 * ℓ ^ ((9 : ℝ) / 2) * (1 + kk * Real.sqrt (μ * ℓ ^ 3))
        = ((R / ℓ) ^ 6 * ℓ ^ ((9 : ℝ) / 2)) * μ ^ 2
            * (1 + kk * Real.sqrt (μ * ℓ ^ 3)) := by ring
      _ = (R ^ 6 * ℓ ^ (-(3 / 2) : ℝ)) * μ ^ 2
            * (1 + kk * Real.sqrt (μ * ℓ ^ 3)) := by rw [hcomb]
      _ = R ^ 6 * (μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ)
            * (1 + kk * Real.sqrt (μ * ℓ ^ 3))) := by ring
  have hRHS : R ^ 6 * α ^ (-(11 / 2) : ℝ) * (1 + kk) * (μ * α)
      = R ^ 6 * (α ^ (-(9 / 2) : ℝ) * μ * (1 + kk)) := by
    have hα11 : α ^ (-(11 / 2) : ℝ) * (μ * α) = α ^ (-(9 / 2) : ℝ) * μ := by
      calc α ^ (-(11 / 2) : ℝ) * (μ * α)
          = (α ^ (-(11 / 2) : ℝ) * α) * μ := by ring
        _ = (α ^ (-(11 / 2) : ℝ) * α ^ (1 : ℝ)) * μ := by rw [Real.rpow_one]
        _ = α ^ (-(9 / 2) : ℝ) * μ := by
            rw [← Real.rpow_add hα (-(11 / 2) : ℝ) (1 : ℝ)]
            norm_num
    calc R ^ 6 * α ^ (-(11 / 2) : ℝ) * (1 + kk) * (μ * α)
        = R ^ 6 * (1 + kk) * (α ^ (-(11 / 2) : ℝ) * (μ * α)) := by ring
      _ = R ^ 6 * (1 + kk) * (α ^ (-(9 / 2) : ℝ) * μ) := by rw [hα11]
      _ = R ^ 6 * (α ^ (-(9 / 2) : ℝ) * μ * (1 + kk)) := by ring
  rw [hLHS, hRHS]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ R ^ 6)
  calc μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * (1 + kk * Real.sqrt (μ * ℓ ^ 3))
      = μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ)
        + kk * (μ ^ 2 * ℓ ^ (-(3 / 2) : ℝ) * Real.sqrt (μ * ℓ ^ 3)) := by ring
    _ ≤ α ^ (-(9 / 2) : ℝ) * μ + kk * (α ^ (-(9 / 2) : ℝ) * μ) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hkk)
    _ = α ^ (-(9 / 2) : ℝ) * μ * (1 + kk) := by ring

end Work.BoseBoxFock
