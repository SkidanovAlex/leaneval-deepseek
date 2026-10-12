import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.farRadCountAux.c0Bound
import Submission.Work.BoseFixR.farRadCountAux.epsFarSqrtBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `farRadCountB` — the radial count budget of the far leg with the doubled fibre weight

This is `Work.BoseFixR.farRadCount` with the last factor doubled:
the radial/zero-point count term

  `ρ² (1/4 + 32√ε) ((10/(π s) + 1)³ + 1) · (2 (16πa)²) / (ρ ε^{-1/2} a)`

(with `ε = epsFar v μ ρ = √(𝓜/((ρ+μ)ℓ³))`, `s = (μa³)^{1/323}`,
`𝓜 = bigMV v μ`) is absorbed into the crude budget `ErrRes/4`, which is
dominated by `10^300 (ρ+μ) a 𝓜`.

The only change with respect to `farRadCount` is the constant: the product
`ρ·(1/4+32√ε)` is bounded by `ρ·1`, `((10/(π s)+1)³+1)` by `1000 𝓜`
(`farRadCountAux.c0Bound`), and `ε^{-1/2} ≥ 1` (`farRadCountAux.epsFarSqrtBound`),
so the left side is at most `2·256000·π²·ρ a 𝓜 ≤ 512000·16·ρ a 𝓜`, which is
vastly smaller than the available `10^300/4 · (ρ+μ) a 𝓜`.  The arithmetic is the
same as in `farRadCount`, with `256000` replaced by `512000`; the slack is so
large that nothing else needs to change.

`FarCond` is carried by the statement but, exactly as for `epsFar_le_inv_eight`,
it is not used by the estimates below.
-/

namespace Work.BoseFixR

open _root_.BoseGases

set_option linter.unusedVariables false

theorem farRadCountB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ ρ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hav : 0 < BoseGases.a v) (hρ : 0 < ρ) (hfar : Work.BoseFixR.FarCond v μ ρ) :
    ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (Work.BoseFixR.epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2
            / (ρ * (Work.BoseFixR.epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v))
      ≤ Work.BoseFixR.ErrRes v μ ρ / 4 := by
  have hμ : 0 < μ := hAdm.1
  have hAr : 0 < BoseGases.a v := hav
  have hMpos : 0 < bigMV v μ := Work.BoseBox.bigM_pos_of_params hμ hav
  -- smallness of the diluteness
  have ht0 : 0 < μ * BoseGases.a v ^ 3 := by positivity
  have htle : μ * BoseGases.a v ^ 3 ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := hAdm.2.1.trans hε₀
  have ht1 : μ * BoseGases.a v ^ 3 ≤ 1 := by
    have h1 : (10 : ℝ) ^ (-(4000 : ℤ)) ≤ 1 := by
      rw [show (10 : ℝ) ^ (-(4000 : ℤ)) = ((10 : ℝ) ^ 4000)⁻¹ by norm_num]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10))
    linarith
  -- the `s`-arithmetic
  have hs : (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
      = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 1 := rfl
  have hs_pos : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
    rw [hs]; exact Work.BoseBox.fsXp_pos ht0
  have hC0 : (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1
      ≤ 1000 * bigMV v μ := by
    have hM : bigMV v μ = Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
        * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ)) := by
      simp only [bigMV, Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [hs, hM]
    exact farRadCountAux.c0Bound ht0 ht1
  -- the `ε`-bounds
  obtain ⟨hsqrtE, hEinvg1⟩ :=
    farRadCountAux.epsFarSqrtBound hAdm hε₀ hav (le_of_lt hρ) hfar
  have hEinvgpos : 0 < epsFar v μ ρ ^ (-(1 / 2 : ℝ)) := lt_of_lt_of_le zero_lt_one hEinvg1
  have hfac : 1 / 4 + 32 * Real.sqrt (epsFar v μ ρ) ≤ 1 := by nlinarith [hsqrtE]
  -- the budget is at least `10^300 (ρ+μ) a 𝓜`
  have hErr : (10 : ℝ) ^ 300 * ((ρ + μ) * BoseGases.a v * bigMV v μ) ≤ ErrRes v μ ρ := by
    rw [ErrRes]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_add_of_nonneg_right ?_
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) (3 / 2)) (le_of_lt hAr))
      (Real.sqrt_nonneg _)
  have hErrpos : 0 < ErrRes v μ ρ :=
    lt_of_lt_of_le (by positivity) hErr
  -- the core inequality, with the `ρ`-factor divided out
  have hcore : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
      ≤ ErrRes v μ ρ / 4 * BoseGases.a v := by
    have hpre1 : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ)) ≤ ρ * 1 :=
      mul_le_mul_of_nonneg_left hfac (le_of_lt hρ)
    have hC0nn : 0 ≤ (10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3
        + 1 := by
      have hx : (0 : ℝ) ≤ 10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1 := by
        positivity
      linarith [pow_nonneg hx 3]
    have hpre : ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
          * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        ≤ ρ * 1 * (1000 * bigMV v μ) := by
      have h1 := mul_le_mul_of_nonneg_right hpre1 hC0nn
      have h2 : ρ * 1 * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3
            + 1) ≤ ρ * 1 * (1000 * bigMV v μ) :=
        mul_le_mul_of_nonneg_left hC0 (by positivity)
      linarith [h1, h2]
    have hFnn : 0 ≤ 2 * (16 * Real.pi * BoseGases.a v) ^ 2 := by positivity
    have hstep2 := mul_le_mul_of_nonneg_right hpre hFnn
    -- numeric comparison; the doubled constant `512000 = 2 · 256000` is still tiny
    have hnum : (512000 : ℝ) * Real.pi ^ 2 ≤ (10 : ℝ) ^ 300 / 4 := by
      have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
      have h3 : (512000 : ℝ) * 16 ≤ (10 : ℝ) ^ 10 / 4 := by norm_num
      have h4 : (512000 : ℝ) * Real.pi ^ 2 ≤ (10 : ℝ) ^ 10 / 4 := by nlinarith [hpi2, h3]
      have h5 : (10 : ℝ) ^ 10 / 4 ≤ (10 : ℝ) ^ 300 / 4 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
        exact pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact le_trans h4 h5
    have hstep3 : ρ * 1 * (1000 * bigMV v μ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
        ≤ (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ) := by
      rw [show ρ * 1 * (1000 * bigMV v μ) * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
          = 512000 * Real.pi ^ 2 * (ρ * BoseGases.a v ^ 2 * bigMV v μ) by ring]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    have hstep4 : (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ)
        ≤ ErrRes v μ ρ / 4 * BoseGases.a v := by
      have h2 : (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v * bigMV v μ)
          ≤ ErrRes v μ ρ / 4 := by linarith [hErr]
      have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hAr)
      have h4 : (10 : ℝ) ^ 300 / 4 * (ρ * BoseGases.a v ^ 2 * bigMV v μ)
          ≤ (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v ^ 2 * bigMV v μ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hμ, hρ, hAr, hMpos]
      have h5 : (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v * bigMV v μ)
            * BoseGases.a v
          = (10 : ℝ) ^ 300 / 4 * ((ρ + μ) * BoseGases.a v ^ 2 * bigMV v μ) := by ring
      linarith [h3, h4, h5]
    linarith [hstep2, hstep3, hstep4]
  -- clear the denominator
  have hDpos : 0 < ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by positivity
  rw [mul_div_assoc', div_le_iff₀ hDpos]
  have hE4nn : 0 ≤ ErrRes v μ ρ / 4 := by linarith [hErrpos]
  calc ρ ^ 2 * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)
      = ρ * (ρ * (1 / 4 + 32 * Real.sqrt (epsFar v μ ρ))
        * ((10 / (Real.pi * (Work.BoseBox.paramsAt μ (BoseGases.a v)).s) + 1) ^ 3 + 1)
        * (2 * (16 * Real.pi * BoseGases.a v) ^ 2)) := by ring
    _ ≤ ρ * (ErrRes v μ ρ / 4 * BoseGases.a v) :=
        mul_le_mul_of_nonneg_left hcore (le_of_lt hρ)
    _ ≤ ρ * (ErrRes v μ ρ / 4 * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hρ)
        have h1 : ErrRes v μ ρ / 4 * 1 ≤ ErrRes v μ ρ / 4 * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hEinvg1 hE4nn
        simpa using mul_le_mul_of_nonneg_right h1 (le_of_lt hAr)
    _ = ErrRes v μ ρ / 4 * (ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * BoseGases.a v) := by ring

end Work.BoseFixR
