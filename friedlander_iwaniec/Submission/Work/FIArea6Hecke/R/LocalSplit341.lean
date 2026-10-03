/-
# `Submission.Work.FIArea6Hecke.R.LocalSplit341`

The **split-prime local `(3,4,1)` bound**.  At a split prime `p` the local Euler factor of the
Hecke `L`-function `L(s,ψ)`, `ψ(z) = χ(z)(z/|z|)^m`, is a product of two geometric factors
`(1 - ζ x p^{-s})^{-1}`, `(1 - ζ y p^{-s})^{-1}` (with `x,y` the Satake parameters, `|x|,|y| ≤ 1`),
and the local factor of the principal Hecke series is the square `(1 - p^{-s})^{-2}`.

This file proves that the corresponding logarithmic-derivative combination

  `3·Re(-L'_1/L_1)(σ) + 4·Re(-L'_2/L_2)(σ+it) + Re(-L'_3/L_3)(σ+2it)`

(with `L_2` carrying the Satake parameters `x,y` and `L_3` carrying their squares `x²,y²`) is
`≥ 0`, for every `σ > 1`.  Expanding every factor as a geometric series turns the combination into

  `log p · Σ_j p^{-jσ} · [ (3 + 4 Re u_j + Re u_j²) + (3 + 4 Re v_j + Re v_j²) ]`,

`u_j = (x p^{-it})^j`, `v_j = (y p^{-it})^j`, whose summands are non-negative by the elementary
trigonometric inequality `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0` (`three_four_one_aux` in
`HeckeLDerivDefs`), via `local341_nonneg`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.HeckeLDerivDefs
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

lemma one_sub_ne_zero (p : Nat.Primes) (x : ℂ) {s : ℂ} (hx : ‖x‖ ≤ 1) (hs : 0 < s.re) :
    1 - x * (((p:ℕ):ℂ) ^ (-s)) ≠ 0 := by
  intro h0
  have hxT : x * (((p:ℕ):ℂ) ^ (-s)) = 1 := (sub_eq_zero.mp h0).symm
  have h1 : ‖x * (((p:ℕ):ℂ) ^ (-s))‖ = 1 := by rw [hxT, norm_one]
  have h2 : ‖x * (((p:ℕ):ℂ) ^ (-s))‖ ≤ ((p:ℕ):ℝ) ^ (-s.re) := by
    rw [norm_mul, norm_cpow_neg_nat]
    calc ‖x‖ * ((p:ℕ):ℝ) ^ (-s.re) ≤ 1 * ((p:ℕ):ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := one_mul _
  have hp1 : (1:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.prop.one_lt
  have h3 : ((p:ℕ):ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

lemma logDeriv_geom (p : Nat.Primes) (x : ℂ) {s : ℂ} (hx : ‖x‖ ≤ 1) (hs : 0 < s.re) :
    logDeriv (fun w : ℂ => (1 - x * (((p:ℕ):ℂ) ^ (-w)))⁻¹) s
      = -(x * (((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ) ^ (-s)))
          / (1 - x * (((p:ℕ):ℂ) ^ (-s)))) := by
  have hne := one_sub_ne_zero p x hx hs
  have hd : DifferentiableAt ℂ (fun y : ℂ => y⁻¹) (1 - x * (((p:ℕ):ℂ)^(-s))) :=
    differentiableAt_inv hne
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => 1 - x * (((p:ℕ):ℂ)^(-w))) s :=
    (((hasDerivAt_natCast_cpow_neg p s).const_mul x).const_sub 1).differentiableAt
  have hcomp := logDeriv_comp (f := fun y : ℂ => y⁻¹)
    (g := fun w : ℂ => 1 - x * (((p:ℕ):ℂ)^(-w))) hd hd2
  have hfun : (fun w : ℂ => (1 - x * (((p:ℕ):ℂ)^(-w)))⁻¹)
      = (fun y : ℂ => y⁻¹) ∘ (fun w : ℂ => 1 - x * (((p:ℕ):ℂ)^(-w))) := rfl
  rw [hfun, hcomp, logDeriv_inv]
  have hderiv : deriv (fun w : ℂ => 1 - x * (((p:ℕ):ℂ)^(-w))) s
      = x * (((Real.log ((p:ℕ):ℝ)) : ℂ) * (((p:ℕ):ℂ)^(-s))) := by
    rw [((hasDerivAt_natCast_cpow_neg p s).const_mul x).const_sub 1 |>.deriv]; ring
  rw [hderiv]
  field_simp

lemma differentiableAt_geom (p : Nat.Primes) (x : ℂ) {s : ℂ} (hx : ‖x‖ ≤ 1) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w : ℂ => (1 - x * (((p:ℕ):ℂ) ^ (-w)))⁻¹) s := by
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - x * (((p:ℕ):ℂ) ^ (-w))) s :=
    (((hasDerivAt_natCast_cpow_neg p s).const_mul x).const_sub 1).differentiableAt
  exact (differentiableAt_inv (one_sub_ne_zero p x hx hs)).comp s hd

lemma geom_ne_zero (p : Nat.Primes) (x : ℂ) {s : ℂ} (hx : ‖x‖ ≤ 1) (hs : 0 < s.re) :
    (1 - x * (((p:ℕ):ℂ) ^ (-s)))⁻¹ ≠ 0 :=
  inv_ne_zero (one_sub_ne_zero p x hx hs)

lemma neg_logDeriv_splitModel (p : Nat.Primes) (x y : ℂ) {s : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hs : 0 < s.re) :
    -logDeriv (fun z : ℂ => (1 - x * (((p:ℕ):ℂ) ^ (-z)))⁻¹
        * (1 - y * (((p:ℕ):ℂ) ^ (-z)))⁻¹) s
      = ((Real.log ((p:ℕ):ℝ) : ℝ) : ℂ)
        * (x * (((p:ℕ):ℂ) ^ (-s)) / (1 - x * (((p:ℕ):ℂ) ^ (-s)))
           + y * (((p:ℕ):ℂ) ^ (-s)) / (1 - y * (((p:ℕ):ℂ) ^ (-s)))) := by
  have h1 := logDeriv_geom p x hx hs
  have h2 := logDeriv_geom p y hy hs
  have hmul := Submission.Port.logDeriv_mul_fun (f := fun z : ℂ => (1 - x * (((p:ℕ):ℂ) ^ (-z)))⁻¹)
    (g := fun z : ℂ => (1 - y * (((p:ℕ):ℂ) ^ (-z)))⁻¹) s
    (geom_ne_zero p x hx hs) (geom_ne_zero p y hy hs)
    (differentiableAt_geom p x hx hs) (differentiableAt_geom p y hy hs)
  rw [hmul, h1, h2]
  field_simp
  ring

theorem LocalSplit341 (p : Nat.Primes) {σ t : ℝ} (hσ : 1 < σ) {x y : ℂ}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    0 ≤ 3 * (-logDeriv (fun z : ℂ => (1 - (1:ℂ) * (((p:ℕ):ℂ) ^ (-z)))⁻¹
              * (1 - (1:ℂ) * (((p:ℕ):ℂ) ^ (-z)))⁻¹) ((σ:ℂ))).re
      + 4 * (-logDeriv (fun z : ℂ => (1 - x * (((p:ℕ):ℂ) ^ (-z)))⁻¹
              * (1 - y * (((p:ℕ):ℂ) ^ (-z)))⁻¹) ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      + (-logDeriv (fun z : ℂ => (1 - x^2 * (((p:ℕ):ℂ) ^ (-z)))⁻¹
              * (1 - y^2 * (((p:ℕ):ℂ) ^ (-z)))⁻¹) ((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by
  have hs1 : (0:ℝ) < ((σ:ℂ)).re := by simp; linarith
  have hs2 : (0:ℝ) < (((σ:ℂ) + (t:ℂ) * Complex.I)).re := by simp; linarith
  have hs3 : (0:ℝ) < (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by simp; linarith
  have hx2 : ‖x^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg x) hx
  have hy2 : ‖y^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg y) hy
  have e1 := neg_logDeriv_splitModel p (1:ℂ) (1:ℂ) (s := (σ:ℂ)) (by simp) (by simp) hs1
  have e2 := neg_logDeriv_splitModel p x y (s := (σ:ℂ) + (t:ℂ)*Complex.I) hx hy hs2
  have e3 := neg_logDeriv_splitModel p (x^2) (y^2) (s := (σ:ℂ) + ((2*t:ℝ):ℂ)*Complex.I)
    hx2 hy2 hs3
  rw [e1, e2, e3]
  set w : ℝ := ((p:ℕ):ℝ) ^ (-σ) with hw
  set Z : ℂ := ((p:ℕ):ℂ) ^ (-((t:ℂ) * Complex.I)) with hZ
  set X : ℂ := x * Z with hX
  set Y : ℂ := y * Z with hY
  have hc : (((p:ℕ):ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact p.prop.pos.ne'
  have hP1 : ((p:ℕ):ℂ) ^ (-(σ:ℂ)) = (w:ℂ) := by
    rw [hw]
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg (p:ℕ)) (-σ)).symm
  have hP2 : ((p:ℕ):ℂ) ^ (-((σ:ℂ) + (t:ℂ) * Complex.I)) = (w:ℂ) * Z := by
    rw [show -((σ:ℂ) + (t:ℂ) * Complex.I) = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) by ring,
      Complex.cpow_add _ _ hc, hP1, hZ]
  have hP3 : ((p:ℕ):ℂ) ^ (-((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)) = (w:ℂ) * Z * Z := by
    rw [show -((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)
          = (-(σ:ℂ)) + (-((t:ℂ) * Complex.I)) + (-((t:ℂ) * Complex.I)) by push_cast; ring,
      Complex.cpow_add _ _ hc, Complex.cpow_add _ _ hc, hP1, hZ]
  rw [hP1, hP2, hP3]
  simp only [one_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hq1 : (((w:ℂ) / (1 - (w:ℂ)) + (w:ℂ) / (1 - (w:ℂ))).re) = 2 * (w/(1-w)) := by
    rw [Complex.add_re, re_ratio]; ring
  have hq2 : ((x * ((w:ℂ) * Z) / (1 - x * ((w:ℂ) * Z))
        + y * ((w:ℂ) * Z) / (1 - y * ((w:ℂ) * Z))).re)
      = ((X * (w:ℂ)) / (1 - X * (w:ℂ))).re + ((Y * (w:ℂ)) / (1 - Y * (w:ℂ))).re := by
    rw [Complex.add_re]
    congr 1
    · rw [show x * ((w:ℂ) * Z) = (x * Z) * (w:ℂ) by ring, ← hX]
    · rw [show y * ((w:ℂ) * Z) = (y * Z) * (w:ℂ) by ring, ← hY]
  have hq3 : ((x^2 * ((w:ℂ) * Z * Z) / (1 - x^2 * ((w:ℂ) * Z * Z))
        + y^2 * ((w:ℂ) * Z * Z) / (1 - y^2 * ((w:ℂ) * Z * Z))).re)
      = ((X^2 * (w:ℂ)) / (1 - X^2 * (w:ℂ))).re + ((Y^2 * (w:ℂ)) / (1 - Y^2 * (w:ℂ))).re := by
    rw [Complex.add_re]
    congr 1
    · rw [show x^2 * ((w:ℂ) * Z * Z) = (x * Z)^2 * (w:ℂ) by ring, ← hX]
    · rw [show y^2 * ((w:ℂ) * Z * Z) = (y * Z)^2 * (w:ℂ) by ring, ← hY]
  rw [hq1, hq2, hq3]
  have hfin : 3 * (Real.log ((p:ℕ):ℝ) * (2 * (w/(1-w))))
      + 4 * (Real.log ((p:ℕ):ℝ)
          * (((X * (w:ℂ)) / (1 - X * (w:ℂ))).re + ((Y * (w:ℂ)) / (1 - Y * (w:ℂ))).re))
      + Real.log ((p:ℕ):ℝ)
          * (((X^2 * (w:ℂ)) / (1 - X^2 * (w:ℂ))).re + ((Y^2 * (w:ℂ)) / (1 - Y^2 * (w:ℂ))).re)
      = Real.log ((p:ℕ):ℝ) * (local341 w X + local341 w Y) := by
    rw [local341, local341]; ring
  rw [hfin]
  refine mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (add_nonneg ?_ ?_)
  · refine local341_nonneg ?_ ?_ ?_
    · rw [hw]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [hw]; exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    · rw [hX, norm_mul, norm_cpow_neg_I, mul_one]; exact hx
  · refine local341_nonneg ?_ ?_ ?_
    · rw [hw]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [hw]; exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    · rw [hY, norm_mul, norm_cpow_neg_I, mul_one]; exact hy

end

end Work.FIArea6Hecke.R
