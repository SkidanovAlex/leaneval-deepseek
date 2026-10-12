import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.ParamsView
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.FSParamsVals` — the values of FS §10's parameters

At the parameter point `FSParamsView E` every scalar of the `Q3Env` is an
explicit monomial in the diluteness `t = μa³` (equivalently in `X = (μa³)^{1/323}`).
This module records the monomial values (in the `fsXp` normal form of
`Work.BoseBox.Basic`, `fsXp t c = t^{c/323} = X^c`) together with the elementary
positivity and the two bounds on `ρ_z` (FS `eq:Close`) that the error arithmetic
of `thm:Control3Q` uses.

The values (all with `X = (μa³)^{1/323}`):

| quantity | value |
|---|---|
| `K_ℓ = E.Kl` | `X^{-3/2}` |
| `K_L = E.KL` | `X^{-21/2}` |
| `K_H = E.KH` | `X^{-549/4}` |
| `d = E.d` | `X⁶` |
| `𝓜 = E.bigM` | `X^{-327/4}` |
| `𝓁 = E.lille` | `X^{97/2}` |
| `dil E c = (μa³)^c` | `X^{323c}` |
| `μℓ³` | `X^{-166}` |
| `M = E.intM` | `48` |

and the central consequence of `𝓜` and `μℓ³`, used to dominate the errors by the
`thm:Control3Q` bracket: the lower bound
`√(𝓜/z²) = √(𝓜/(ρ_zℓ³)) ≥ (4/5)·X^{337/8}`
(the exact exponent is `337/8 = 337/4/2` with `𝓜/(μℓ³) = X^{337/4}`; the
`(4/5)` covers the `ρ_z ≤ (3/2)μ` loss, `√(2/3) ≥ 4/5`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- A bare power of `t` is a power of `X = (μa³)^{1/323}`: `t^c = X^{323c}`. -/
lemma rpow_eq_fsXp {t c : ℝ} (ht : 0 ≤ t) : t ^ c = fsXp t (323 * c) := by
  conv_lhs => rw [delta_eq_fsXp ht]
  rw [fsXp_rpow ht]

/-! ## 1. The monomial values -/

/-- `K_ℓ = X^{-3/2}` (FS `sec:params`). -/
theorem Kl_val (E : Q3Env Mode) (h : FSParamsView E) : E.Kl = fsXp h.t (-(3 / 2)) := h.Kl_eq

/-- `d = X⁶` (FS `sec:params`). -/
theorem d_val (E : Q3Env Mode) (h : FSParamsView E) : E.d = fsXp h.t 6 := h.d_eq

/-- `K_L = (K_ℓd²)^{-1} = X^{-21/2}` (FS `eq:KL_d`). -/
theorem KL_val (E : Q3Env Mode) (h : FSParamsView E) : E.KL = fsXp h.t (-(21 / 2)) := by
  have ht0 : 0 < h.t := h.t_pos
  rw [h.KL_eq, KL, h.Kl_eq, h.d_eq, ← Real.rpow_natCast, fsXp_rpow ht0.le, fsXp_mul ht0,
    fsXp_rpow ht0.le]
  congr 1
  norm_num

/-- `K_H = K̃_H(μa³)^{-5/12} = X^{-549/4}` (FS `sec:params`). -/
theorem KH_val (E : Q3Env Mode) (h : FSParamsView E) : E.KH = fsXp h.t (-(549 / 4)) := by
  have ht0 : 0 < h.t := h.t_pos
  rw [h.KH_eq, KH]
  rw [show (E.mu * E.aScat ^ 3) ^ (-(5 / 12 : ℝ)) = h.t ^ (-(5 / 12 : ℝ)) by rw [h.mu_eq]]
  rw [rpow_eq_fsXp ht0.le, fsXp_mul ht0]
  congr 1
  norm_num

/-- `𝓜 = K_M(μa³)^{-1/4} = X^{-327/4}` (FS `eq:DefM`). -/
theorem bigM_val (E : Q3Env Mode) (h : FSParamsView E) : E.bigM = fsXp h.t (-(327 / 4)) := by
  have ht0 : 0 < h.t := h.t_pos
  rw [h.bigM_eq, rpow_eq_fsXp ht0.le, fsXp_mul ht0]
  congr 1
  norm_num

/-- `𝓁 = (μa³)K_H² = X^{97/2}` (FS `eq:DefLille`). -/
theorem lille_val (E : Q3Env Mode) (h : FSParamsView E) : E.lille = fsXp h.t (97 / 2) := by
  have ht0 : 0 < h.t := h.t_pos
  have h2 : (fsXp h.t (-(549 / 4))) ^ 2 = fsXp h.t (-(549 / 2)) := by
    rw [← Real.rpow_natCast, fsXp_rpow ht0.le]
    congr 1
    norm_num
  calc E.lille = h.t * (fsXp h.t (-(549 / 4))) ^ 2 := by
        rw [Q3Env.lille, lille, h.mu_eq, KH_val E h]
    _ = fsXp h.t 323 * fsXp h.t (-(549 / 2)) := by
        rw [h2]
        congr 1
        exact delta_eq_fsXp ht0.le
    _ = fsXp h.t (97 / 2) := by
        rw [fsXp_mul ht0]
        congr 1
        norm_num

/-- `(μa³)^c = X^{323c}` (the definition of `dil`). -/
theorem dil_val (E : Q3Env Mode) (h : FSParamsView E) (c : ℝ) : dil E c = fsXp h.t (323 * c) := by
  have ht0 : 0 < h.t := h.t_pos
  unfold dil
  rw [show E.mu * E.aScat ^ 3 = h.t by rw [h.mu_eq]]
  rw [rpow_eq_fsXp ht0.le]

/-- `(μa³)^c ≥ 0`. -/
theorem dil_nonneg (E : Q3Env Mode) (h : FSParamsView E) (c : ℝ) : 0 ≤ dil E c := by
  rw [dil_val E h c]
  exact fsXp_nonneg (c := 323 * c) h.t_pos.le

/-- `(μa³)^c > 0`. -/
theorem dil_pos (E : Q3Env Mode) (h : FSParamsView E) (c : ℝ) : 0 < dil E c := by
  rw [dil_val E h c]
  exact fsXp_pos (c := 323 * c) h.t_pos

/-- `μℓ³ = K_ℓ³(μa³)^{-1/2} = X^{-166}` (the healing length `ℓ = K_ℓ(μa)^{-1/2}`). -/
theorem mue_val (E : Q3Env Mode) (h : FSParamsView E) : E.mu * E.ell ^ 3 = fsXp h.t (-166) := by
  have ht0 : 0 < h.t := h.t_pos
  have ha : 0 < E.aScat := h.a_pos
  have hmu : 0 < E.mu := by
    have h1 := h.mu_eq
    nlinarith [h.t_pos, pow_pos ha 3]
  have hμa : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hell : E.ell = E.Kl * (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) := by rw [h.ell_eq, side]
  have h2 : ((E.mu * E.aScat) ^ (-(1 / 2 : ℝ))) ^ 3 = (E.mu * E.aScat) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμa.le]
    congr 1
    norm_num
  have hμneg : E.mu * E.mu ^ (-(3 / 2 : ℝ)) = E.mu ^ (-(1 / 2 : ℝ)) := by
    nth_rewrite 1 [show E.mu = E.mu ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hmu]
    congr 1
    norm_num
  have ha3 : (E.aScat ^ 3) ^ (-(1 / 2 : ℝ)) = E.aScat ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have h3 : E.mu * (E.mu * E.aScat) ^ (-(3 / 2 : ℝ)) = (E.mu * E.aScat ^ 3) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.mul_rpow hmu.le ha.le, Real.mul_rpow hmu.le (pow_nonneg ha.le 3), ha3]
    rw [← mul_assoc, hμneg]
  have h1 : E.mu * E.ell ^ 3 = E.Kl ^ 3 * (E.mu * (E.mu * E.aScat) ^ (-(3 / 2 : ℝ))) := by
    rw [hell, mul_pow, h2]
    ring
  rw [h1, h3]
  rw [show (E.mu * E.aScat ^ 3) ^ (-(1 / 2 : ℝ)) = h.t ^ (-(1 / 2 : ℝ)) by rw [h.mu_eq]]
  rw [Kl_val E h, ← Real.rpow_natCast, fsXp_rpow ht0.le, rpow_eq_fsXp ht0.le, fsXp_mul ht0]
  congr 1
  norm_num

/-- FS's regularity integer is `M = 48`. -/
theorem intM_val (E : Q3Env Mode) (h : FSParamsView E) : (E.intM : ℝ) = 48 := by
  rw [h.intM_eq, mValue]
  norm_num

/-! ## 2. Positivity and the bounds on `ρ_z` -/

/-- `a > 0`. -/
theorem a_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.aScat := h.a_pos

/-- `μ > 0`. -/
theorem mu_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.mu := by
  have ha : 0 < E.aScat := h.a_pos
  have h1 := h.mu_eq
  nlinarith [h.t_pos, pow_pos ha 3]

/-- `ℓ > 0`. -/
theorem ell_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.ell := by
  rw [h.ell_eq, side]
  exact mul_pos (lt_of_lt_of_le zero_lt_one h.one_le_Kl)
    (Real.rpow_pos_of_pos (mul_pos (mu_pos E h) (a_pos E h)) _)

/-- `𝓜 ≥ 0`. -/
theorem bigM_nonneg (E : Q3Env Mode) (h : FSParamsView E) : 0 ≤ E.bigM := le_trans zero_le_one h.one_le_bigM

/-- `z² > 0`. -/
theorem zsq_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.z ^ 2 := sq_pos_of_ne_zero h.z_ne

/-- `z² = ρ_zℓ³`. -/
theorem zsq_eq (E : Q3Env Mode) (h : FSParamsView E) : E.z ^ 2 = E.rho * E.ell ^ 3 := by
  rw [Q3Env.rho, rhoZ, div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt (ell_pos E h)))]

/-- FS `eq:Close` in the crudest form: `ρ_z ≤ (3/2)μ`. -/
theorem rho_le (E : Q3Env Mode) (h : FSParamsView E) : E.rho ≤ 3 * E.mu / 2 := by
  have h1 : E.rho - E.mu ≤ E.mu / 2 := (abs_le.mp h.rho_close).2
  linarith

/-- FS `eq:Close`: `ρ_z ≥ μ/2`. -/
theorem rho_ge (E : Q3Env Mode) (h : FSParamsView E) : E.mu / 2 ≤ E.rho := by
  have h1 : -(E.mu / 2) ≤ E.rho - E.mu := (abs_le.mp h.rho_close).1
  linarith

/-- `ρ_z > 0`. -/
theorem rho_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E.rho := lt_of_lt_of_le (by linarith [mu_pos E h]) (rho_ge E h)

/-! ## 3. The lower bound on `√(𝓜/z²)` -/

/-- `𝓜/(μℓ³) = X^{337/4}`. -/
theorem bigM_div_mue (E : Q3Env Mode) (h : FSParamsView E) : E.bigM / (E.mu * E.ell ^ 3) = fsXp h.t (337 / 4) := by
  have ht0 : 0 < h.t := h.t_pos
  rw [bigM_val E h, mue_val E h, div_eq_mul_inv, fsXp_inv ht0, neg_neg, fsXp_mul ht0]
  congr 1
  norm_num

/-- **The lower bound on `√(𝓜/z²)`**: `√(𝓜/(ρ_zℓ³)) ≥ (4/5)X^{337/8}`, since
`z² = ρ_zℓ³ ≤ (3/2)μℓ³` and `𝓜/(μℓ³) = X^{337/4}`, `√(2/3) ≥ 4/5`. -/
theorem S_lower (E : Q3Env Mode) (h : FSParamsView E) : (4 / 5) * fsXp h.t (337 / 8) ≤ Real.sqrt (E.bigM / E.z ^ 2) := by
  have ht0 : 0 < h.t := h.t_pos
  have hE : 0 < E.ell ^ 3 := pow_pos (ell_pos E h) 3
  have hkey : E.bigM / ((3 / 2) * (E.mu * E.ell ^ 3)) = (2 / 3) * fsXp h.t (337 / 4) := by
    rw [← bigM_div_mue E h]
    field_simp
  have hzle : E.z ^ 2 ≤ (3 / 2) * (E.mu * E.ell ^ 3) := by
    rw [zsq_eq E h]
    nlinarith [rho_le E h, hE, mu_pos E h]
  have hle1 : E.bigM / ((3 / 2) * (E.mu * E.ell ^ 3)) ≤ E.bigM / E.z ^ 2 :=
    div_le_div_of_nonneg_left (bigM_nonneg E h) (zsq_pos E h) hzle
  have hle2 : (2 / 3) * fsXp h.t (337 / 4) ≤ E.bigM / E.z ^ 2 := by
    rw [← hkey]; exact hle1
  have hL : Real.sqrt ((2 / 3) * fsXp h.t (337 / 4)) =
      Real.sqrt (2 / 3) * fsXp h.t (337 / 8) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    congr 1
    rw [Real.sqrt_eq_rpow, fsXp_rpow ht0.le]
    congr 1
    norm_num
  have h45 : (4 / 5 : ℝ) ≤ Real.sqrt (2 / 3) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  calc (4 / 5) * fsXp h.t (337 / 8)
      ≤ Real.sqrt (2 / 3) * fsXp h.t (337 / 8) :=
        mul_le_mul_of_nonneg_right h45 (fsXp_nonneg ht0.le)
    _ = Real.sqrt ((2 / 3) * fsXp h.t (337 / 4)) := hL.symm
    _ ≤ Real.sqrt (E.bigM / E.z ^ 2) := Real.sqrt_le_sqrt hle2

/-- `√(𝓜/z²) ≥ 0`. -/
theorem S_nonneg (E : Q3Env Mode) (_h : FSParamsView E) : 0 ≤ Real.sqrt (E.bigM / E.z ^ 2) :=
  Real.sqrt_nonneg _

/-- `√(𝓜/z²) > 0`. -/
theorem S_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < Real.sqrt (E.bigM / E.z ^ 2) := by
  rw [Real.sqrt_pos]
  exact div_pos (lt_of_lt_of_le zero_lt_one h.one_le_bigM) (zsq_pos E h)

end Work.BoseB7
