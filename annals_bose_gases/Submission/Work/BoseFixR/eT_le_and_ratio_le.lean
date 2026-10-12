import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseK15.arith_aKH_div_sell_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.eT_le_and_ratio_le`

At FS's parameter point (`FSParamsView E`) and at diluteness
`t = μa³ ≤ 10⁻⁴⁰⁰⁰`, the two "smallness" thresholds of `Work.BoseK15.arith_tau_ge`
hold with the *explicit* constants `9/49` and `1/16`:

  `ε_T ≤ 9/49`  and  `a·K_H/(s·ℓ) ≤ 1/16`.

Both are monomials in `t`: `ε_T = X^{23/4} = t^{23/1292}` and
`a·K_H/(s·ℓ) = t^{99/1292}` (`Work.BoseK15.arith_aKH_div_sell_le`).  Since
`t ↦ t^e` is increasing for `e > 0`, the hypothesis `t ≤ 10⁻⁴⁰⁰⁰` gives

  `t^e ≤ (10⁻⁴⁰⁰⁰)^e = 10^{-4000·e}`,

and `4000·23/1292 ≥ 1`, `4000·99/1292 ≥ 2` turn this into `1/10 ≤ 9/49` and
`1/100 ≤ 1/16`.

The two identities `ε_T = t^{23/1292}` and `a·K_H/(s·ℓ) = t^{99/1292}` are
recorded separately (`eT_eq_rpow`, `ratio_eq_fsXp`), together with the purely
analytic step `rpow_le_ten_rpow_neg_mul`.
-/

namespace Work.BoseFixR

open Work.BoseB7

/-- `ε_T = X^{23/4} = t^{23/1292}` at FS's parameter point. -/
lemma eT_eq_rpow {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) : E.eT = hv.t ^ (23 / 1292 : ℝ) := by
  rw [hv.eT_eq, Work.BoseBox.fsXp]
  congr 1
  norm_num

/-- `a·K_H/(s·ℓ) = t^{99/1292}` at FS's parameter point: this is the `hratio`
computation of `Work.BoseK15.arith_aKH_div_sell_le`, exported as an identity.

`K_H = X^{-549/4}`, `s = X`, `ℓ = X^{-3/2}(μa)^{-1/2}` and
`a(μa)^{1/2} = (μa³)^{1/2}`, so the ratio is `t^{1/2 - 547/1292}
= t^{99/1292}`. -/
lemma ratio_eq_fsXp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    E.aScat * E.KH / (E.s * E.ell) = hv.t ^ (99 / 1292 : ℝ) := by
  have hμa : 0 < E.mu * E.aScat := mul_pos (Work.BoseB7.mu_pos E hv) hv.a_pos
  have hell : E.ell = Work.BoseBox.fsXp hv.t (-(3 / 2)) * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ) := by
    rw [hv.ell_eq, Work.BoseB7.side, hv.Kl_eq]
  have hD : ((E.mu * E.aScat) ^ (-(1 / 2) : ℝ))⁻¹ = (E.mu * E.aScat) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hμa.le, inv_inv]
  have hsub : ((Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2)))
        * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ))⁻¹
      = (E.mu * E.aScat) ^ (1 / 2 : ℝ) *
        (Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2)))⁻¹ := by
    conv_lhs => rw [mul_inv_rev]
    rw [hD]
  rw [hell, hv.s_eq, Work.BoseB7.KH_val E hv]
  have hstep : E.aScat * Work.BoseBox.fsXp hv.t (-(549 / 4)) /
        (Work.BoseBox.fsXp hv.t 1 *
          (Work.BoseBox.fsXp hv.t (-(3 / 2)) * (E.mu * E.aScat) ^ (-(1 / 2) : ℝ)))
      = (E.aScat * (E.mu * E.aScat) ^ (1 / 2 : ℝ)) *
        (Work.BoseBox.fsXp hv.t (-(549 / 4)) *
          (Work.BoseBox.fsXp hv.t 1 * Work.BoseBox.fsXp hv.t (-(3 / 2)))⁻¹) := by
    rw [← mul_assoc, div_eq_mul_inv, hsub]
    ring
  rw [hstep, Work.BoseK15.ascat_mul_sqrt_mu_ascat E hv, Work.BoseK15.KH_s_Kl_fsXp E hv]
  rw [← Real.rpow_add hv.t_pos]
  congr 1
  norm_num

/-- **The analytic step.**  If `0 < t ≤ 10⁻⁴⁰⁰⁰` and `0 < e` then
`t^e ≤ 10^{-4000·e}`: raise the bound `t ≤ 10⁻⁴⁰⁰⁰` to the power `e` and use
`(10^y)^e = 10^{y·e}`. -/
lemma rpow_le_ten_rpow_neg_mul {t e : ℝ} (ht : 0 < t) (he : 0 < e)
    (h : t ≤ (10 : ℝ) ^ (-(4000 : ℤ))) :
    t ^ e ≤ (10 : ℝ) ^ (-(4000 : ℝ) * e) := by
  have h10 : (10 : ℝ) ^ (-(4000 : ℤ)) = (10 : ℝ) ^ (-(4000 : ℝ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [h10] at h
  calc t ^ e ≤ ((10 : ℝ) ^ (-(4000 : ℝ))) ^ e := Real.rpow_le_rpow ht.le h he.le
    _ = (10 : ℝ) ^ (-(4000 : ℝ) * e) := (Real.rpow_mul (by norm_num) _ _).symm

theorem eT_le_and_ratio_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (ht : hv.t ≤ 10 ^ (-(4000 : ℤ))) :
    E.eT ≤ 9 / 49 ∧ E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 16 := by
  have ht0 : 0 < hv.t := hv.t_pos
  constructor
  · rw [eT_eq_rpow E hv]
    have h1 : hv.t ^ (23 / 1292 : ℝ) ≤ (10 : ℝ) ^ (-(4000 : ℝ) * (23 / 1292)) :=
      rpow_le_ten_rpow_neg_mul ht0 (by norm_num) ht
    have h2 : (10 : ℝ) ^ (-(4000 : ℝ) * (23 / 1292)) ≤ (10 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one] at h2
    have h3 : (10 : ℝ)⁻¹ ≤ 9 / 49 := by norm_num
    linarith
  · rw [ratio_eq_fsXp E hv]
    have h1 : hv.t ^ (99 / 1292 : ℝ) ≤ (10 : ℝ) ^ (-(4000 : ℝ) * (99 / 1292)) :=
      rpow_le_ten_rpow_neg_mul ht0 (by norm_num) ht
    have h2 : (10 : ℝ) ^ (-(4000 : ℝ) * (99 / 1292)) ≤ (10 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h3 : (10 : ℝ) ^ (-2 : ℝ) = (1 : ℝ) / 100 := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
      norm_num
    rw [h3] at h2
    linarith

end Work.BoseFixR
