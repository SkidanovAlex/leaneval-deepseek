/-
# `Submission.Work.FIArea6Hecke.R.LocalInert341`

The **inert-prime local `(3,4,1)` bound**.  At an inert prime `p` (a rational prime `≡ 3 mod 4`)
the local Euler factor of the Hecke `L`-function `L(s,ψ)`, `ψ(z) = χ(z)(z/|z|)^m`, is a single
geometric factor `(1 - ζ (p^{-s})²)^{-1}` (with `ζ` a Satake parameter of modulus `≤ 1`), and the
local factor of the principal Hecke series is `(1 - (p^{-s})²)^{-1}`.

This file proves that the corresponding logarithmic-derivative combination

  `3·Re(-L'_1/L_1)(σ) + 4·Re(-L'_2/L_2)(σ+it) + Re(-L'_3/L_3)(σ+2it)`

(with `L_2` carrying the Satake parameter `c` and `L_3` carrying its square `c²`) is `≥ 0` for
every `σ > 1`.  Expanding every factor as a geometric series turns the combination into

  `2 log p · Σ_j (p^{-2σ})^j · (3 + 4 Re Z^j + Re Z^{2j})`,   `Z = c p^{-2it}`,

whose summands are non-negative by `three_four_one_aux` / `local341_nonneg` (`HeckeLDerivDefs`).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.HeckeLDerivDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

lemma one_sub_sq_ne_zero (p : Nat.Primes) (u : ℂ) {s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 0 < s.re) :
    1 - u * ((((p:ℕ):ℂ) ^ (-s)))^2 ≠ 0 := by
  intro h0
  have hxT : u * ((((p:ℕ):ℂ) ^ (-s)))^2 = 1 := (sub_eq_zero.mp h0).symm
  have h1 : ‖u * ((((p:ℕ):ℂ) ^ (-s)))^2‖ = 1 := by rw [hxT, norm_one]
  have h2 : ‖u * ((((p:ℕ):ℂ) ^ (-s)))^2‖ ≤ (((p:ℕ):ℝ) ^ (-s.re))^2 := by
    rw [norm_mul, norm_pow, norm_cpow_neg_nat]
    calc ‖u‖ * (((p:ℕ):ℝ) ^ (-s.re))^2 ≤ 1 * (((p:ℕ):ℝ) ^ (-s.re))^2 :=
          mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := one_mul _
  have hp1 : (1:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_lt
  have h3 : ((p:ℕ):ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have h4 : 0 ≤ ((p:ℕ):ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h5 : (((p:ℕ):ℝ) ^ (-s.re))^2 < 1 := by nlinarith
  linarith

lemma neg_logDeriv_inertModel (p : Nat.Primes) (u : ℂ) {s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 0 < s.re) :
    -logDeriv (fun z : ℂ => (1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹) s
      = 2 * ((Real.log ((p:ℕ):ℝ)) : ℂ)
        * (u * ((((p:ℕ):ℂ) ^ (-s)))^2 / (1 - u * ((((p:ℕ):ℂ) ^ (-s)))^2)) := by
  have hne := one_sub_sq_ne_zero p u hu hs
  have hmul : HasDerivAt (fun z : ℂ => ((((p:ℕ):ℂ) ^ (-z))) * ((((p:ℕ):ℂ) ^ (-z))))
      (-(((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ)^(-s))) * (((p:ℕ):ℂ)^(-s))
        + (((p:ℕ):ℂ)^(-s)) * (-(((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ)^(-s))))) s :=
    (hasDerivAt_natCast_cpow_neg p s).mul (hasDerivAt_natCast_cpow_neg p s)
  have hPsq : HasDerivAt (fun z : ℂ => ((((p:ℕ):ℂ) ^ (-z)))^2)
      (2 * (((p:ℕ):ℂ)^(-s)) * (-(((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ)^(-s))))) s := by
    rw [show (fun z : ℂ => ((((p:ℕ):ℂ) ^ (-z)))^2)
        = (fun z : ℂ => ((((p:ℕ):ℂ) ^ (-z))) * ((((p:ℕ):ℂ) ^ (-z)))) from by
      funext z; rw [pow_two]]
    exact hmul.congr_deriv (by ring)
  have hG : HasDerivAt (fun z : ℂ => 1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2)
      (-(u * (2 * (((p:ℕ):ℂ)^(-s))
        * (-(((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ)^(-s))))))) s :=
    (hPsq.const_mul u).const_sub 1
  have hd : DifferentiableAt ℂ (fun y : ℂ => y⁻¹) (1 - u * ((((p:ℕ):ℂ)^(-s)))^2) :=
    differentiableAt_inv hne
  have hcomp := logDeriv_comp (f := fun y : ℂ => y⁻¹)
    (g := fun z : ℂ => 1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2) hd hG.differentiableAt
  have hfun : (fun z : ℂ => (1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹)
      = (fun y : ℂ => y⁻¹) ∘ (fun z : ℂ => 1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2) := rfl
  rw [hfun, hcomp, logDeriv_inv, hG.deriv]
  field_simp

lemma neg_logDeriv_inertModel_re (p : Nat.Primes) (u : ℂ) {s : ℂ} (hu : ‖u‖ ≤ 1)
    (hs : 0 < s.re) :
    (-logDeriv (fun z : ℂ => (1 - u * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹) s).re
      = 2 * Real.log ((p:ℕ):ℝ)
        * (u * ((((p:ℕ):ℂ) ^ (-s)))^2 / (1 - u * ((((p:ℕ):ℂ) ^ (-s)))^2)).re := by
  rw [neg_logDeriv_inertModel p u hu hs]
  have hfac : 2 * ((Real.log ((p:ℕ):ℝ)) : ℂ) * (u * ((((p:ℕ):ℂ) ^ (-s)))^2
        / (1 - u * ((((p:ℕ):ℂ) ^ (-s)))^2))
      = ((2 * Real.log ((p:ℕ):ℝ) : ℝ) : ℂ) * (u * ((((p:ℕ):ℂ) ^ (-s)))^2
        / (1 - u * ((((p:ℕ):ℂ) ^ (-s)))^2)) := by push_cast; ring
  rw [hfac, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem LocalInert341 (p : Nat.Primes) {σ t : ℝ} (hσ : 1 < σ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ 3 * (-logDeriv (fun z : ℂ => (1 - (1:ℂ) * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹) ((σ:ℂ))).re
      + 4 * (-logDeriv (fun z : ℂ => (1 - w * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹)
              ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      + (-logDeriv (fun z : ℂ => (1 - w^2 * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹)
              ((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by
  have hs1 : (0:ℝ) < ((σ:ℂ)).re := by simp; linarith
  have hs2 : (0:ℝ) < (((σ:ℂ) + (t:ℂ) * Complex.I)).re := by simp; linarith
  have hs3 : (0:ℝ) < (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by simp; linarith
  have hw2 : ‖w^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg w) hw
  have e1 := neg_logDeriv_inertModel_re p (1:ℂ) (by simp) hs1
  have e2 := neg_logDeriv_inertModel_re p w hw hs2
  have e3 := neg_logDeriv_inertModel_re p (w^2) hw2 hs3
  rw [e1, e2, e3]
  set ww : ℝ := ((p:ℕ):ℝ) ^ (-σ) with hww
  set Z : ℂ := ((p:ℕ):ℂ) ^ (-((t:ℂ) * Complex.I)) with hZ
  set Zc : ℂ := w * Z^2 with hZc
  have ht2 : (0:ℝ) < ww := by
    rw [hww]; exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr p.prop.pos) _
  have ht1 : ww < 1 := by
    rw [hww]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hc : (((p:ℕ):ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact p.prop.pos.ne'
  have hP1 : ((p:ℕ):ℂ) ^ (-(σ:ℂ)) = (ww:ℂ) := by
    rw [hww]
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg (p:ℕ)) (-σ)).symm
  have hP2 : ((p:ℕ):ℂ) ^ (-((σ:ℂ) + (t:ℂ) * Complex.I)) = (ww:ℂ) * Z := by
    rw [show -((σ:ℂ) + (t:ℂ) * Complex.I) = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) by ring,
      Complex.cpow_add _ _ hc, hP1, hZ]
  have hP3 : ((p:ℕ):ℂ) ^ (-((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)) = (ww:ℂ) * Z * Z := by
    rw [show -((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)
          = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) + (-((t:ℂ) * Complex.I)) by push_cast; ring,
      Complex.cpow_add _ _ hc, Complex.cpow_add _ _ hc, hP1, hZ]
  have hX1 : ((((p:ℕ):ℂ) ^ (-(σ:ℂ)))^2) = ((ww^2 : ℝ) : ℂ) := by
    rw [hP1, ← Complex.ofReal_pow]
  have hX2 : ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + (t:ℂ) * Complex.I)))^2)
      = ((ww^2 : ℝ) : ℂ) * Z^2 := by
    rw [hP2, mul_pow, ← Complex.ofReal_pow]
  have hX3 : ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)))^2)
      = ((ww^2 : ℝ) : ℂ) * Z^2 * Z^2 := by
    rw [hP3, mul_pow, mul_pow, ← Complex.ofReal_pow]
  have hQ1 : (1 * ((((p:ℕ):ℂ) ^ (-(σ:ℂ)))^2) / (1 - 1 * ((((p:ℕ):ℂ) ^ (-(σ:ℂ)))^2))).re
      = ww^2/(1-ww^2) := by
    rw [hX1]
    simp only [one_mul]
    rw [show (1:ℂ) - ((ww^2 : ℝ):ℂ) = ((1 - ww^2 : ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_div, Complex.ofReal_re]
  have hQ2 : (w * ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + (t:ℂ) * Complex.I)))^2)
        / (1 - w * ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + (t:ℂ) * Complex.I)))^2))).re
      = (((ww^2 : ℝ) : ℂ) * Zc / (1 - ((ww^2 : ℝ) : ℂ) * Zc)).re := by
    rw [hX2,
      show w * (((ww^2 : ℝ) : ℂ) * Z^2) = ((ww^2 : ℝ) : ℂ) * Zc by rw [hZc]; ring]
  have hQ3 : (w^2 * ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)))^2)
        / (1 - w^2 * ((((p:ℕ):ℂ) ^ (-((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)))^2))).re
      = (((ww^2 : ℝ) : ℂ) * Zc^2 / (1 - ((ww^2 : ℝ) : ℂ) * Zc^2)).re := by
    rw [hX3,
      show w^2 * (((ww^2 : ℝ) : ℂ) * Z^2 * Z^2) = ((ww^2 : ℝ) : ℂ) * Zc^2 by rw [hZc]; ring]
  rw [hQ1, hQ2, hQ3]
  have hfin : 3 * (2 * Real.log ((p:ℕ):ℝ) * (ww^2/(1-ww^2)))
      + 4 * (2 * Real.log ((p:ℕ):ℝ)
          * ((((ww^2 : ℝ) : ℂ) * Zc / (1 - ((ww^2 : ℝ) : ℂ) * Zc)).re))
      + (2 * Real.log ((p:ℕ):ℝ)
          * ((((ww^2 : ℝ) : ℂ) * Zc^2 / (1 - ((ww^2 : ℝ) : ℂ) * Zc^2)).re))
      = 2 * Real.log ((p:ℕ):ℝ) * local341 (ww^2) Zc := by
    rw [local341]
    rw [show (((ww^2 : ℝ) : ℂ) * Zc) = Zc * ((ww^2 : ℝ) : ℂ) by ring,
        show (((ww^2 : ℝ) : ℂ) * Zc^2) = Zc^2 * ((ww^2 : ℝ) : ℂ) by ring]
    ring
  rw [hfin]
  refine mul_nonneg (by positivity) (local341_nonneg (by positivity) ?_ ?_)
  · nlinarith [ht2, ht1]
  · rw [hZc, norm_mul, norm_pow, norm_cpow_neg_I, one_pow, mul_one]; exact hw

end

end Work.FIArea6Hecke.R
