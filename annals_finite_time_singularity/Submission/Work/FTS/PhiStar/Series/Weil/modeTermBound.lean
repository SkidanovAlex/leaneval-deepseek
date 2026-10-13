/-
# `modeTermBound` — decay of the modes of the remainder series

The mode terms of the remainder series `R α ψ = psiSeries α (RemSource α ψ)` are

  `trm α ψ m z θ = acoeff α m (RemSource α ψ) z · eFam m θ`,

and `acoeff_RemSource` factors the radial coefficient:

  `acoeff α m (RemSource α ψ) z = (α² · bmode m ψ) · radGreen α m (𝒜φ α) z`.

Each of the three factors is bounded by an existing result:

* `bmode_decay15`: `|bmode m ψ| ≤ C_b/(λ_m·√(2m+1))` with `λ_m = 2m(2m+5)`;

* `radGreen_phiA_bound`: `|radGreen α m (𝒜φ α) z| ≤ C_r·(1+1/z)·(m+1)^{-2}`;

* `eFam_sup_le`: `|eFam m θ| ≤ C_e·(m+1)`.

Since `1/(λ_m√(2m+1)) ≤ (m+1)^{-5/2}` (the elementary `lam_mul_sqrt_ge` below), and
`α² ≤ 1`, the product decays like `(m+1)^{-5/2-2+1} = (m+1)^{-7/2}`, which is exactly the
stated rate.  The whole point of the file is the exponent bookkeeping in `ℝ`-powers
(`inv_lam_mul_sqrt_le` and `rpow_factor`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Conjunctions34
import Submission.Work.FTS.PhiStar.Series.radGreen_phiA_bound
import Submission.Work.FTS.PhiStar.Series.bmode_decay15
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Weil

open scoped Real

/-! ## Elementary facts about `λ_m = 2m(2m+5)` -/

/-- `(m+1)^{5/2} ≤ λ_m·√(2m+1)` for `m ≥ 1`: indeed `λ_m ≥ (m+1)²` and
`√(2m+1) ≥ √(m+1)`. -/
private lemma lam_mul_sqrt_ge (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ (5 / 2 : ℝ)
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlam0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  have h2 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
    apply Real.sqrt_le_sqrt; linarith
  have h3 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hlam0
  calc ((m : ℝ) + 1) ^ (5 / 2 : ℝ) = ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1) := by
        rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hx, Real.sqrt_eq_rpow]
        norm_num
    _ ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := h3

/-- `1/(λ_m·√(2m+1)) ≤ (m+1)^{-5/2}` for `m ≥ 1`. -/
private lemma inv_lam_mul_sqrt_le (m : ℕ) (hm : 1 ≤ m) :
    1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hB : (0 : ℝ) < ((m : ℝ) + 1) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have h := one_div_le_one_div_of_le hB (lam_mul_sqrt_ge m hm)
  rw [one_div, one_div] at h
  rw [← Real.rpow_neg (le_of_lt hx)] at h
  rw [one_div]
  exact h

/-- `x^{-5/2}·(x^{-2}·x) = x^{-7/2}` — the exponent bookkeeping of the mode bound. -/
private lemma rpow_factor (x : ℝ) (hx : 0 < x) :
    x ^ (-(5 / 2 : ℝ)) * (x ^ (-(2 : ℝ)) * x) = x ^ (-(7 / 2 : ℝ)) := by
  have h2 : x ^ (-(5 / 2 : ℝ)) * x ^ (-(2 : ℝ)) = x ^ (-(9 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx]; norm_num
  have h3 : x ^ (-(9 / 2 : ℝ)) * x = x ^ (-(7 / 2 : ℝ)) := by
    have h : x ^ (-(9 / 2 : ℝ)) * x ^ (1 : ℝ) = x ^ (-(7 / 2 : ℝ)) := by
      rw [← Real.rpow_add hx]; norm_num
    simpa using h
  calc x ^ (-(5 / 2 : ℝ)) * (x ^ (-(2 : ℝ)) * x)
      = (x ^ (-(5 / 2 : ℝ)) * x ^ (-(2 : ℝ))) * x := by ring
    _ = x ^ (-(9 / 2 : ℝ)) * x := by rw [h2]
    _ = x ^ (-(7 / 2 : ℝ)) := h3

/-- **Decay of the mode terms of the remainder series.**  For `0 < α ≤ 1/5` and an angular
model `ψ`, the mode terms of `psiSeries α (RemSource α ψ)` decay at the rate
`(m+1)^{-7/2}`, uniformly in the angle and with the radial singularity `(1+1/z)`. -/
theorem modeTermBound (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(7 / 2 : ℝ)) := by
  obtain ⟨Cb, hCb, hbm⟩ := Work.FTS.PhiStar.Series.bmode_decay15
  obtain ⟨Cr, hCr, hr⟩ := Work.FTS.PhiStar.Series.radGreen_phiA_bound
  obtain ⟨Ce, hCe, he⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hα1 : α ≤ 1 := by linarith
  refine ⟨Cb * Cr * Ce, by positivity, ?_⟩
  intro m hm z θ hz hθ
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs : (0 : ℝ) ≤ 1 + 1 / z := by positivity
  have hx5 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hxi2 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ (-(2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα5]
  -- the three factor bounds
  have hBd : |Work.FTS.PhiStar.Series.bmode m ψ|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [Work.FTS.PhiStar.Series.bmode_eq_cmode m ψ 0]
      exact hbm α ψ hα hα5 hψ m hm
    calc |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hb
      _ = Cb * (1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
          rw [div_eq_mul_one_div]
      _ ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (inv_lam_mul_sqrt_le m hm) hCb.le
  have hRg : |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
      ≤ Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := (hr α hα hα1 m hm).1 z hz
  have hEf : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * ((m : ℝ) + 1) := he m θ hθ
  have hCbx5 : (0 : ℝ) ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := mul_nonneg hCb.le hx5
  have hCrs : (0 : ℝ) ≤ Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) :=
    mul_nonneg (mul_nonneg hCr.le hs) hxi2
  -- assemble
  have hsplit : |Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      = α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
    rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
    rw [abs_mul ((α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
      * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
      (Work.FTS.PhiStar.Gegenbauer.eFam m θ)]
    rw [abs_mul (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
      (Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)]
    rw [abs_mul (α ^ 2) (Work.FTS.PhiStar.Series.bmode m ψ)]
    rw [abs_of_nonneg (sq_nonneg α)]
  have step1 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
        * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
        * (Ce * ((m : ℝ) + 1)) := by
    have h1 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ 1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul hα2 hBd (abs_nonneg _) (by norm_num)
    have h2 : α ^ 2 * |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
          * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) :=
      mul_le_mul h1 hRg (abs_nonneg _) (by simpa using hCbx5)
    exact mul_le_mul h2 hEf (abs_nonneg _) (mul_nonneg (by simpa using hCbx5) hCrs)
  have heq : (1 * (Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
        * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
        * (Ce * ((m : ℝ) + 1))
      = Cb * Cr * Ce * (1 + 1 / z)
        * (((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
          * (((m : ℝ) + 1) ^ (-(2 : ℝ)) * ((m : ℝ) + 1))) := by ring
  rw [hsplit]
  refine le_trans step1 ?_
  rw [heq, rpow_factor ((m : ℝ) + 1) hx]

end Work.FTS.PhiStar.Series.Weil
