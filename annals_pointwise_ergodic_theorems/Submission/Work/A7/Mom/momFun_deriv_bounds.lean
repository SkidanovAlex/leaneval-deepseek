/-
# Derivative bounds for the §6 oscillatory phase `momFun` (Area A7, `Mom`)

This module proves `Work.A7.Mom.momFun_deriv_bounds`: the pointwise `C⁰`/`C¹`/`C²` estimate for
the oscillatory phase

  `momFun P ξ₁ ξ₂ t = e(ξ₁ t + ξ₂ P(t)) = exp(2πi (ξ₁ t + ξ₂ P(t)))`

of the §6 model approximation of Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Ann. of Math. 195 (3) 2022, under the frequency
window constraints

  `|ξ₁| ≤ 2^{k₁+1}/N`,  `|ξ₂| ≤ 2^{d(k₂+1)}/N^d`   (`d = P.natDegree`),

uniformly for `t ∈ [0,N]`.

Unlike `Work.A7.osc_deriv_bounds`, which proves the same estimates with an explicit positive
constant and on the slightly larger interval `[-1, N+1]`, **this file is self-contained with
respect to the two chain-rule identities**: the identities
`deriv (momFun) = momFun · 2πi(ξ₁ + ξ₂P')` and
`iteratedDeriv 2 (momFun) = momFun · ((2πi(ξ₁ + ξ₂P'))² + 2πiξ₂P'')`
(the statements `Work.A7.momFun_deriv_formula` and `Work.A7.momFun_iteratedDeriv_two_formula`,
which are only stubbed (unproved) in the workspace) are *proved here* as
`momFun_deriv_formula_aux` and `momFun_iteratedDeriv_two_formula_aux`, so that the present
theorem rests on no unproved import.

The estimates themselves are the elementary ones: with the real phase `φ t = ξ₁t + ξ₂P(t)` one has
`f = exp ∘ (2πi φ)`, hence `f' = f · 2πi φ'` and `f'' = f · ((2πi φ')² + 2πi φ'')`, with
`φ' = ξ₁ + ξ₂P'`, `φ'' = ξ₂P''`; everything reduces to the polynomial growth bounds
`|P'(t)| ≤ K₁ (max 1 |t|)^{e₁}`, `|P''(t)| ≤ K₂ (max 1 |t|)^{e₂}` (`Kᵢ` the sum of the absolute
values of the coefficients) on `[-1,N+1] ⊆ [-3N,3N]`, plus `e₁+1 ≤ d`, `e₂+2 ≤ d` and the
arithmetic lemmas `mul_pow_div_le`, `mul_pow_div_le_sq`.

The two hypotheses `hP1`, `hP2` of the target statement (which bound `deriv PevalR` and
`iteratedDeriv 2 PevalR` by `A N^d/N` and `A N^d/N²` on `[0,N]`) are not needed: the coefficient
sums give the same growth bounds unconditionally, so the conclusion is proved without them.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs
import Submission.Work.KMTPlan.A6.IntegIdent
import Submission.Work.A7.poly_eval_abs_le_coeffSum
import Submission.Work.A7.mul_pow_div_le
import Submission.Work.A7.mul_pow_div_le_sq

set_option maxHeartbeats 1000000

namespace Work.A7.Mom

noncomputable section

open Polynomial Finset
open scoped BigOperators

/-! ## The coefficient function `2πi (ξ₁ + ξ₂ P')` and its derivative -/

/-- The coefficient `2πi(ξ₁ + ξ₂ P'(t))` multiplying `momFun` in the first derivative. -/
noncomputable def Acoef (P : Polynomial ℤ) (ξ₁ ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => (2 : ℂ) * (Real.pi : ℂ) * Complex.I
    * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))

/-- The derivative `2πi ξ₂ P''(t)` of `Acoef`. -/
noncomputable def AcoefD (P : Polynomial ℤ) (ξ₂ : ℝ) : ℝ → ℂ :=
  fun t => (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((ξ₂ : ℂ)
    * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ))

/-- **Chain rule for `momFun`.**  `momFun P ξ₁ ξ₂ = e ∘ φ` with `φ t = ξ₁t + ξ₂P(t)`, and `e` has
derivative `e · 2πi`; the chain rule gives the stated form. -/
lemma momFun_hasDerivAt (P : Polynomial ℤ) (ξ₁ ξ₂ t : ℝ) :
    HasDerivAt (Work.A7.momFun P ξ₁ ξ₂) (Work.A7.momFun P ξ₁ ξ₂ t * Acoef P ξ₁ ξ₂ t) t := by
  have hφ : HasDerivAt (fun s : ℝ => ξ₁ * s + ξ₂ * Work.KMTAreas.A7.PevalR P s)
      (ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P t) t := by
    have h1 := hasDerivAt_const_mul (x := t) ξ₁
    have h2 := (Work.KMTPlan.A6.hasDerivAt_PevalR P t).const_mul ξ₂
    exact h1.add h2
  have hφc : HasDerivAt (fun s : ℝ => ((ξ₁ * s + ξ₂ * Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ))
      (((ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P t : ℝ)) : ℂ) t :=
    HasDerivAt.ofReal_comp hφ
  have hψ := hφc.const_mul ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
  have h := hψ.cexp
  have hfun : (fun x : ℝ => Complex.exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
      * ((ξ₁ * x + ξ₂ * Work.KMTAreas.A7.PevalR P x : ℝ) : ℂ))) = Work.A7.momFun P ξ₁ ξ₂ := rfl
  rw [hfun] at h
  convert h using 1
  · simp only [Work.A7.momFun, Work.KMTAreas.A7.ee, Acoef]
    push_cast
    ring

/-- The coefficient function `Acoef` has derivative `AcoefD`. -/
lemma Acoef_hasDerivAt (P : Polynomial ℤ) (ξ₁ ξ₂ t : ℝ) :
    HasDerivAt (Acoef P ξ₁ ξ₂) (AcoefD P ξ₂ t) t := by
  have hA : HasDerivAt (fun s : ℝ => ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P s)
      (ξ₂ * Work.KMTPlan.A6.Pderiv2R P t) t := by
    have h1 : HasDerivAt (fun s : ℝ => ξ₂ * Work.KMTPlan.A6.PderivR P s)
        (ξ₂ * Work.KMTPlan.A6.Pderiv2R P t) t := by
      have h := Work.KMTPlan.A6.hasDerivAt_PevalR P.derivative t
      simpa only [Work.KMTAreas.A7.PevalR, Work.KMTPlan.A6.PderivR, Work.KMTPlan.A6.Pderiv2R]
        using h.const_mul ξ₂
    have hc : HasDerivAt (fun _ : ℝ => ξ₁) 0 t := hasDerivAt_const (x := t) (c := ξ₁)
    have hh := hc.add h1
    rw [show ((fun _ : ℝ => ξ₁) + fun s : ℝ => ξ₂ * Work.KMTPlan.A6.PderivR P s : ℝ → ℝ)
        = fun s => ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P s from rfl] at hh
    simpa using hh
  have h2 : HasDerivAt (fun s : ℝ => ((ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P s : ℝ) : ℂ))
      (((ξ₂ * Work.KMTPlan.A6.Pderiv2R P t : ℝ)) : ℂ) t := HasDerivAt.ofReal_comp hA
  have h3 := h2.const_mul ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
  have hfac : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I
      * (((ξ₂ * Work.KMTPlan.A6.Pderiv2R P t : ℝ)) : ℂ)) = AcoefD P ξ₂ t := by
    rw [AcoefD]; push_cast; ring
  rw [hfac] at h3
  have hfun : (fun y : ℝ => (2 : ℂ) * (Real.pi : ℂ) * Complex.I
      * ((ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P y : ℝ) : ℂ)) = Acoef P ξ₁ ξ₂ := by
    ext y; rw [Acoef]; push_cast; ring
  rw [hfun] at h3
  exact h3

/-- **The first derivative of `momFun`**, in the explicit form used below. -/
lemma momFun_deriv_formula_aux (P : Polynomial ℤ) (ξ₁ ξ₂ : ℝ) (t : ℝ) :
    deriv (Work.A7.momFun P ξ₁ ξ₂) t
      = Work.A7.momFun P ξ₁ ξ₂ t
          * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I
              * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))) := by
  rw [(momFun_hasDerivAt P ξ₁ ξ₂ t).deriv]
  simp only [Acoef]

/-- **The second iterate of `deriv` on `momFun`**, in terms of `Acoef`, `AcoefD`. -/
lemma momFun_iteratedDeriv_two_formula' (P : Polynomial ℤ) (ξ₁ ξ₂ t : ℝ) :
    iteratedDeriv 2 (Work.A7.momFun P ξ₁ ξ₂) t
      = Work.A7.momFun P ξ₁ ξ₂ t * (Acoef P ξ₁ ξ₂ t ^ 2 + AcoefD P ξ₂ t) := by
  have hderiv : deriv (Work.A7.momFun P ξ₁ ξ₂)
      = fun s => Work.A7.momFun P ξ₁ ξ₂ s * Acoef P ξ₁ ξ₂ s := by
    funext s
    exact (momFun_hasDerivAt P ξ₁ ξ₂ s).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  have hmul := (momFun_hasDerivAt P ξ₁ ξ₂ t).mul (Acoef_hasDerivAt P ξ₁ ξ₂ t)
  convert hmul.deriv using 1
  ring

/-- **The second derivative of `momFun`**, in the explicit form used below. -/
lemma momFun_iteratedDeriv_two_formula_aux (P : Polynomial ℤ) (ξ₁ ξ₂ : ℝ) (t : ℝ) :
    iteratedDeriv 2 (Work.A7.momFun P ξ₁ ξ₂) t
      = Work.A7.momFun P ξ₁ ξ₂ t
          * (((2 : ℂ) * (Real.pi : ℂ) * Complex.I
                * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))) ^ 2
              + (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)
                * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)) := by
  rw [momFun_iteratedDeriv_two_formula']
  simp only [Acoef, AcoefD]
  ring

/-! ## The coefficient sum of a real polynomial -/

/-- The sum of the absolute values of the coefficients of a real polynomial. -/
noncomputable def coeffAbsSum (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

lemma coeffAbsSum_nonneg (p : Polynomial ℝ) : 0 ≤ coeffAbsSum p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-! ## The constants of the two derivative bounds -/

/-- The constant of the first-derivative bound. -/
noncomputable def oscB1 (P : Polynomial ℤ) : ℝ :=
  2 * Real.pi * (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
      * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))

/-- The constant of the second-derivative bound. -/
noncomputable def oscB2 (P : Polynomial ℤ) : ℝ :=
  oscB1 P ^ 2 + 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
      * (2 : ℝ) ^ P.natDegree
      * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree))

/-! ## Degree bookkeeping for the derivatives of `P` -/

lemma natDegree_map_derivative_le (P : Polynomial ℤ) :
    (P.derivative.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree - 1 :=
  Polynomial.natDegree_map_le.trans (Polynomial.natDegree_derivative_le P)

lemma natDegree_map_derivative2_le (P : Polynomial ℤ) :
    (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree - 2 := by
  refine Polynomial.natDegree_map_le.trans ?_
  have h := Polynomial.natDegree_iterate_derivative P 2
  rwa [Function.iterate_succ_apply', Function.iterate_one] at h

lemma derivative_map_eq_zero_of_natDegree_eq_zero (P : Polynomial ℤ) (h : P.natDegree = 0) :
    P.derivative.map (Int.castRingHom ℝ) = 0 := by
  rw [Polynomial.derivative_eq_zero.mpr h, Polynomial.map_zero]

lemma derivative2_map_eq_zero_of_natDegree_le_one (P : Polynomial ℤ) (h : P.natDegree ≤ 1) :
    P.derivative.derivative.map (Int.castRingHom ℝ) = 0 := by
  have h2 : P.derivative.derivative = 0 := by
    have hh := Polynomial.iterate_derivative_eq_zero (p := P) (x := 2) (by omega)
    rwa [Function.iterate_succ_apply', Function.iterate_one] at hh
  rw [h2, Polynomial.map_zero]

lemma PderivR_eq_zero_of_natDegree_eq_zero (P : Polynomial ℤ) (h : P.natDegree = 0) (t : ℝ) :
    Work.KMTPlan.A6.PderivR P t = 0 := by
  simp [Work.KMTPlan.A6.PderivR, derivative_map_eq_zero_of_natDegree_eq_zero P h]

lemma Pderiv2R_eq_zero_of_natDegree_le_one (P : Polynomial ℤ) (h : P.natDegree ≤ 1) (t : ℝ) :
    Work.KMTPlan.A6.Pderiv2R P t = 0 := by
  simp [Work.KMTPlan.A6.Pderiv2R, derivative2_map_eq_zero_of_natDegree_le_one P h]

/-! ## Polynomial evaluation bounds -/

lemma PderivR_abs_le (P : Polynomial ℤ) (t : ℝ) :
    |Work.KMTPlan.A6.PderivR P t| ≤ coeffAbsSum (P.derivative.map (Int.castRingHom ℝ))
        * (max 1 |t|) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree) := by
  have h := poly_eval_abs_le_coeffSum (P.derivative.map (Int.castRingHom ℝ)) t
  simpa [coeffAbsSum, Work.KMTPlan.A6.PderivR] using h

lemma Pderiv2R_abs_le (P : Polynomial ℤ) (t : ℝ) :
    |Work.KMTPlan.A6.Pderiv2R P t|
      ≤ coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
        * (max 1 |t|) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree) := by
  have h := poly_eval_abs_le_coeffSum (P.derivative.derivative.map (Int.castRingHom ℝ)) t
  simpa [coeffAbsSum, Work.KMTPlan.A6.Pderiv2R] using h

/-! ## Complex norm bookkeeping -/

lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

lemma norm_two_pi_I_mul (z : ℂ) : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * z‖
    = 2 * Real.pi * ‖z‖ := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hp : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt Real.pi_pos)]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, h2, hp]

/-! ## The `ξ₂ P'(t)` and `ξ₂ P''(t)` estimates -/

/-- **The `ξ₂ P'(t)` term.**  Under the frequency window `|ξ₂| ≤ 2^{d(k₂+1)}/N^d` and for
`t ∈ [-1, N+1]` with `N ≥ 1`,
`|ξ₂ P'(t)| ≤ K₁ 2^d 3^{e₁} (2^{k₁}+2^{dk₂})/N`, where `K₁` is the coefficient sum of `P'` and
`e₁ = natDegree P'`. -/
lemma abs_mul_PderivR_le (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree)
          * Sval P k₁ k₂ / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  by_cases hd : P.natDegree = 0
  · have hP' : Work.KMTPlan.A6.PderivR P t = 0 := PderivR_eq_zero_of_natDegree_eq_zero P hd t
    have hK : coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) = 0 := by
      rw [derivative_map_eq_zero_of_natDegree_eq_zero P hd]
      simp [coeffAbsSum]
    rw [hP', abs_zero, mul_zero, hK]
    simp
  · have hd1 : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hd
    set e := (P.derivative.map (Int.castRingHom ℝ)).natDegree with he
    set K1 := coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) with hK1
    have hK1nn : 0 ≤ K1 := by rw [hK1]; exact coeffAbsSum_nonneg _
    have he1 : e + 1 ≤ P.natDegree := by
      have h := natDegree_map_derivative_le P
      rw [he]; omega
    have hM1 : 1 ≤ max 1 |t| := le_max_left _ _
    have hM3 : max 1 |t| ≤ 3 * N := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hm1 : (-1 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ (N : ℝ) + 1 := ht.2
      have h3 : |t| ≤ (N : ℝ) + 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have h4 : max 1 |t| ≤ (N : ℝ) + 1 := max_le (by linarith) h3
      linarith
    have hP' : |Work.KMTPlan.A6.PderivR P t| ≤ K1 * (max 1 |t|) ^ e := by
      have h := PderivR_abs_le P t
      rw [← hK1, ← he] at h
      exact h
    have hA : 0 ≤ (2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1 :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK1nn
    have hstep : ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
          * (max 1 |t|) ^ e / (N : ℝ) ^ P.natDegree
        ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
          * (3 : ℝ) ^ e / (N : ℝ) :=
      mul_pow_div_le hN hM1 hM3 hA he1
    have hSk₂ : (2 : ℝ) ^ (P.natDegree * k₂) ≤ Sval P k₁ k₂ := by
      rw [Sval]
      exact le_add_of_nonneg_left (by positivity)
    have hZ : 0 ≤ K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e :=
      mul_nonneg (mul_nonneg hK1nn (by positivity)) (by positivity)
    calc |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
        ≤ ((2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
            * (K1 * (max 1 |t|) ^ e) :=
          mul_le_mul hξ₂ hP' (abs_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
            * (max 1 |t|) ^ e / (N : ℝ) ^ P.natDegree := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1)
            * (3 : ℝ) ^ e / (N : ℝ) := hstep
      _ ≤ K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e * Sval P k₁ k₂ / (N : ℝ) := by
          rw [show ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K1) * (3 : ℝ) ^ e
                = (K1 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e)
                    * (2 : ℝ) ^ (P.natDegree * k₂) by ring]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSk₂ hZ) hN0

/-- **The `ξ₂ P''(t)` term.**  Under the frequency window `|ξ₂| ≤ 2^{d(k₂+1)}/N^d` and for
`t ∈ [-1, N+1]` with `N ≥ 1`,
`|ξ₂ P''(t)| ≤ K₂ 2^d 3^{e₂} ((2^{k₁}+2^{dk₂})/N)²`, where `K₂` is the coefficient sum of `P''` and
`e₂ = natDegree P''`. -/
lemma abs_mul_Pderiv2R_le (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
      ≤ coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree)
          * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  by_cases hd : P.natDegree ≤ 1
  · have hP' : Work.KMTPlan.A6.Pderiv2R P t = 0 := Pderiv2R_eq_zero_of_natDegree_le_one P hd t
    have hK : coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) = 0 := by
      rw [derivative2_map_eq_zero_of_natDegree_le_one P hd]
      simp [coeffAbsSum]
    rw [hP', abs_zero, mul_zero, hK]
    simp
  · have hd2 : 2 ≤ P.natDegree := by omega
    set e2 := (P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree with he2
    set K2 := coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ)) with hK2
    have hK2nn : 0 ≤ K2 := by rw [hK2]; exact coeffAbsSum_nonneg _
    have he2' : e2 + 2 ≤ P.natDegree := by
      have h := natDegree_map_derivative2_le P
      rw [he2]; omega
    have hM1 : 1 ≤ max 1 |t| := le_max_left _ _
    have hM3 : max 1 |t| ≤ 3 * N := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hm1 : (-1 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ (N : ℝ) + 1 := ht.2
      have h3 : |t| ≤ (N : ℝ) + 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have h4 : max 1 |t| ≤ (N : ℝ) + 1 := max_le (by linarith) h3
      linarith
    have hP' : |Work.KMTPlan.A6.Pderiv2R P t| ≤ K2 * (max 1 |t|) ^ e2 := by
      have h := Pderiv2R_abs_le P t
      rw [← hK2, ← he2] at h
      exact h
    have hA : 0 ≤ (2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2 :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hK2nn
    have hstep : ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
          * (max 1 |t|) ^ e2 / (N : ℝ) ^ P.natDegree
        ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
          * (3 : ℝ) ^ e2 / (N : ℝ) ^ 2 :=
      mul_pow_div_le_sq hN hM1 hM3 hA he2'
    have hS1 : 1 ≤ Sval P k₁ k₂ := by
      have h : (1 : ℝ) ≤ (2 : ℝ) ^ k₁ := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) := by positivity
      rw [Sval]; linarith
    have hSk₂ : (2 : ℝ) ^ (P.natDegree * k₂) ≤ Sval P k₁ k₂ := by
      rw [Sval]
      exact le_add_of_nonneg_left (by positivity)
    have hSk₂2 : (2 : ℝ) ^ (P.natDegree * k₂) ≤ (Sval P k₁ k₂) ^ 2 :=
      le_trans hSk₂ (le_self_pow₀ hS1 (by norm_num))
    have hZ : 0 ≤ K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2 :=
      mul_nonneg (mul_nonneg hK2nn (by positivity)) (by positivity)
    calc |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
        ≤ ((2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
            * (K2 * (max 1 |t|) ^ e2) :=
          mul_le_mul hξ₂ hP' (abs_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
            * (max 1 |t|) ^ e2 / (N : ℝ) ^ P.natDegree := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2)
            * (3 : ℝ) ^ e2 / (N : ℝ) ^ 2 := hstep
      _ ≤ K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2 * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
          rw [show ((2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree * K2) * (3 : ℝ) ^ e2
                = (K2 * (2 : ℝ) ^ P.natDegree * (3 : ℝ) ^ e2)
                    * (2 : ℝ) ^ (P.natDegree * k₂) by ring]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSk₂2 hZ) (by positivity)

/-! ## The derivative bounds for the phase -/

/-- **The linear part of the derivative of the phase.** -/
lemma phase_deriv_bound (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₁ ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))
          * Sval P k₁ k₂ / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hSk₁ : (2 : ℝ) ^ k₁ ≤ Sval P k₁ k₂ := by
    rw [Sval]
    exact le_add_of_nonneg_right (by positivity)
  have hξ₁' : |ξ₁| ≤ 2 * Sval P k₁ k₂ / (N : ℝ) := by
    calc |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) := hξ₁
      _ = 2 * (2 : ℝ) ^ k₁ / (N : ℝ) := by rw [pow_succ]; ring
      _ ≤ 2 * Sval P k₁ k₂ / (N : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hN0
  have hP' := abs_mul_PderivR_le (k₁ := k₁) P hN hξ₂ ht
  calc |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|
      ≤ 2 * Sval P k₁ k₂ / (N : ℝ)
        + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree) * Sval P k₁ k₂
          / (N : ℝ) :=
        add_le_add hξ₁' hP'
    _ = (2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ)) * (2 : ℝ) ^ P.natDegree
          * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree)) * Sval P k₁ k₂
          / (N : ℝ) := by ring

/-- **The first-derivative bound.** -/
lemma norm_deriv_momFun_le (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₁ ξ₂ t : ℝ} (hN : 1 ≤ N)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    ‖deriv (Work.A7.momFun P ξ₁ ξ₂) t‖ ≤ oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
  rw [momFun_deriv_formula_aux P ξ₁ ξ₂ t]
  rw [norm_mul, norm_two_pi_I_mul, Work.A7.momFun_norm_eq_one, one_mul]
  have hc : ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      ≤ |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
    calc ‖(ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖
        ≤ ‖(ξ₁ : ℂ)‖ + ‖(ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
          rw [norm_mul]; simp
  have hpd := phase_deriv_bound P hN hξ₁ hξ₂ ht
  have hmain : 2 * Real.pi
        * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      ≤ oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
    calc 2 * Real.pi
          * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
        ≤ 2 * Real.pi * (|ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ 2 * Real.pi * ((2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ))
              * (2 : ℝ) ^ P.natDegree
              * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))
            * Sval P k₁ k₂ / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hpd (by positivity)
      _ = oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
          rw [oscB1]; ring
  exact hmain

/-- **The second-derivative bound.** -/
lemma norm_iteratedDeriv_two_momFun_le (P : Polynomial ℤ) {N k₁ k₂ : ℕ} {ξ₁ ξ₂ t : ℝ}
    (hN : 1 ≤ N)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree)
    (ht : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1)) :
    ‖iteratedDeriv 2 (Work.A7.momFun P ξ₁ ξ₂) t‖ ≤ oscB2 P * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  rw [momFun_iteratedDeriv_two_formula_aux P ξ₁ ξ₂ t]
  rw [norm_mul, Work.A7.momFun_norm_eq_one, one_mul]
  have hc : ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      ≤ |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
    calc ‖(ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖
        ≤ ‖(ξ₁ : ℂ)‖ + ‖(ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = |ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t| := by
          rw [norm_mul]; simp
  have hpd := phase_deriv_bound P hN hξ₁ hξ₂ ht
  have hK : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I
        * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
      = 2 * Real.pi
        * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖ :=
    norm_two_pi_I_mul _
  have hK2 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)
        * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)‖
      = 2 * Real.pi * |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t| := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)
          * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)
        = (2 : ℂ) * (Real.pi : ℂ) * Complex.I
          * ((ξ₂ : ℂ) * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)) by ring]
    rw [norm_two_pi_I_mul, norm_mul,
      show ‖(ξ₂ : ℂ)‖ = |ξ₂| from by simp,
      show ‖((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)‖
        = |Work.KMTPlan.A6.Pderiv2R P t| from by simp]
    ring
  have hfirst : (2 * Real.pi
        * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖) ^ 2
      ≤ oscB1 P ^ 2 * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
    have hb : 2 * Real.pi
          * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
        ≤ oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by
      calc 2 * Real.pi
            * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖
          ≤ 2 * Real.pi * (|ξ₁| + |ξ₂| * |Work.KMTPlan.A6.PderivR P t|) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ ≤ 2 * Real.pi * ((2 + coeffAbsSum (P.derivative.map (Int.castRingHom ℝ))
                * (2 : ℝ) ^ P.natDegree
                * (3 : ℝ) ^ ((P.derivative.map (Int.castRingHom ℝ)).natDegree))
              * Sval P k₁ k₂ / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hpd (by positivity)
        _ = oscB1 P * Sval P k₁ k₂ / (N : ℝ) := by rw [oscB1]; ring
    calc (2 * Real.pi
          * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖) ^ 2
        ≤ (oscB1 P * Sval P k₁ k₂ / (N : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = oscB1 P ^ 2 * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by rw [div_pow]; ring
  have hsecond : 2 * Real.pi * |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
      ≤ 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
            * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree))
          * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by
    have hP'' := abs_mul_Pderiv2R_le (k₁ := k₁) P hN hξ₂ ht
    calc 2 * Real.pi * |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|
        = 2 * Real.pi * (|ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t|) := by ring
      _ ≤ 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
            * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree)
            * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hP'' (by positivity)
      _ = 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
            * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree))
          * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by ring
  calc ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I
          * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)
          * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)‖
      ≤ ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I
            * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))) ^ 2‖
        + ‖2 * (Real.pi : ℂ) * Complex.I * (ξ₂ : ℂ)
            * ((Work.KMTPlan.A6.Pderiv2R P t : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = (2 * Real.pi
          * ‖((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))‖) ^ 2
        + 2 * Real.pi * |ξ₂| * |Work.KMTPlan.A6.Pderiv2R P t| := by
        rw [norm_pow, hK, hK2]
    _ ≤ oscB1 P ^ 2 * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2
        + 2 * Real.pi * (coeffAbsSum (P.derivative.derivative.map (Int.castRingHom ℝ))
            * (2 : ℝ) ^ P.natDegree
            * (3 : ℝ) ^ ((P.derivative.derivative.map (Int.castRingHom ℝ)).natDegree))
          * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := add_le_add hfirst hsecond
    _ = oscB2 P * (Sval P k₁ k₂) ^ 2 / (N : ℝ) ^ 2 := by rw [oscB2]; ring

/-! ## The target -/

theorem momFun_deriv_bounds (P : Polynomial ℤ) {A : ℝ} (hA : 0 < A)
    (hP1 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |deriv (Work.KMTAreas.A7.PevalR P) t| ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ))
    (hP2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
      |iteratedDeriv 2 (Work.KMTAreas.A7.PevalR P) t|
        ≤ A * (N : ℝ) ^ P.natDegree / (N : ℝ) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k₁ k₂ : ℕ) (ξ₁ ξ₂ : ℝ), 1 ≤ N →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ),
        ‖Work.A7.momFun P ξ₁ ξ₂ t‖ ≤ 1 ∧
        ‖deriv (Work.A7.momFun P ξ₁ ξ₂) t‖ ≤ C * Work.A7.Sval P k₁ k₂ / (N : ℝ) ∧
        ‖iteratedDeriv 2 (Work.A7.momFun P ξ₁ ξ₂) t‖
          ≤ C * (1 + Work.A7.Sval P k₁ k₂ + (Work.A7.Sval P k₁ k₂) ^ 2) / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC1, hC2, hCpos⟩ : ∃ C : ℝ, oscB1 P ≤ C ∧ oscB2 P ≤ C ∧ 0 < C :=
    ⟨max 1 (max (oscB1 P) (oscB2 P)),
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _),
      lt_of_lt_of_le one_pos (le_max_left _ _)⟩
  refine ⟨C, hCpos, ?_⟩
  intro N k₁ k₂ ξ₁ ξ₂ hN hξ₁ hξ₂ t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) ((N : ℝ) + 1) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hSnn : 0 ≤ Work.A7.Sval P k₁ k₂ := by
    rw [Work.A7.Sval]; positivity
  have hSsq : 0 ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := by positivity
  refine ⟨le_of_eq (Work.A7.momFun_norm_eq_one P ξ₁ ξ₂ t), ?_, ?_⟩
  · refine (norm_deriv_momFun_le P hN hξ₁ hξ₂ ht').trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hSnn) hNpos.le
  · have hsq : (Work.A7.Sval P k₁ k₂) ^ 2
        ≤ 1 + Work.A7.Sval P k₁ k₂ + (Work.A7.Sval P k₁ k₂) ^ 2 := by linarith
    refine (norm_iteratedDeriv_two_momFun_le P hN hξ₁ hξ₂ ht').trans ?_
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hSsq)
      (by positivity)).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCpos.le) (by positivity)

end

end Work.A7.Mom
