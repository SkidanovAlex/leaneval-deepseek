import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17

open Polynomial

noncomputable section

/-! # Local exponent data of the order-two operator `M` at the roots of `Q₄`

`M = P2x ∂² + P1x ∂ + P0x` is the paper's eq. (ODE) (see `seventeen_indep`), whose leading
coefficient is `P2x = (X−1)·X·(X+1)·Q4x`.  We record the local data at a root `z` of the quartic

  `Q4x = 1 − 4abX + (4a²+4b²−2)X² − 4abX³ + X⁴`

whose four roots are the singularities `(a±√(a²−1))(b±√(b²−1))` of `M`:

* `P2x(z) = 0` (the leading coefficient vanishes, `z` is a singularity of `M`);
* `P1x(z) = (P2x)'(z)`, i.e. the two indicial exponents of `M` at `z` are `(0,0)`
  (equivalently: the residue of `P1x/P2x` at `z` is `0`, so the singularity is logarithmic);
* `(P2x)'(z) ≠ 0`, i.e. `z` is a *simple* root of the leading coefficient.

The last two together are exactly the replacement for "local exponents `(0,0)`" in the paper's
Riccati/analytic argument (`CT17_design.lean.txt`, condition (I1)).

## Proof shape

Everything is a computation on the explicit quartic.  Write `D = (a²−1)(b²−1) ≥ 0` and

  `ledC a b = 2ab + 2√D`,  `ledD a b = 2ab − 2√D`   (`led_real_data`, `led_factor`),

so that over `ℂ`

  `Q4x = (X² − ledC·X + 1)·(X² − ledD·X + 1)`,

with `2 < ledC`, `2 < ledD` (the latter is where `a ≠ b` is used) and `ledC ≠ ledD`.
Since both quadratics have two distinct real roots, every complex root of `Q4x` is a real number
satisfying one of them; `led_quad_root` records the resulting elementary facts.
-/

/-- `2ab + 2√((a²−1)(b²−1))`: the larger `t = z + 1/z` for a root `z` of `Q4x`. -/
def ledC (a b : ℚ) : ℝ :=
  2 * (a : ℝ) * (b : ℝ) + 2 * Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1))

/-- `2ab − 2√((a²−1)(b²−1))`: the smaller `t = z + 1/z` for a root `z` of `Q4x`. -/
def ledD (a b : ℚ) : ℝ :=
  2 * (a : ℝ) * (b : ℝ) - 2 * Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1))

/-- The derivative of the quartic `Q4x`, written in the form produced by differentiating
`1 − C(4ab)X + C(4a²+4b²−2)X² − C(4ab)X³ + X⁴` term by term. -/
def ledD4 (a b : ℚ) : Polynomial ℚ :=
  - C (4 * a * b) + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * (2 * X)
    - C (4 * a * b) * (3 * X ^ 2) + 4 * X ^ 3

/-- `ledD4` is the derivative of `Q4x`. -/
lemma Q4x_derivative (a b : ℚ) : (Q4x a b).derivative = ledD4 a b := by
  unfold Q4x ledD4
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C, derivative_X,
    derivative_pow, derivative_one, Polynomial.C_ofNat, Polynomial.C_eq_natCast, map_ofNat,
    map_natCast]
  norm_num

/-- The `P₁` coefficient of `M` is congruent to `(X−1)X(X+1)·Q4x'` modulo `Q4x`:
`P1x = (X−1)X(X+1)·Q4x' − (X²+1)·Q4x`.  Evaluated at a root of `Q4x`, this is precisely the
statement that the two indicial exponents of `M` there are both `0`. -/
lemma P1x_eq (a b : ℚ) :
    P1x a b = (X - 1) * X * (X + 1) * ledD4 a b - (X ^ 2 + 1) * Q4x a b := by
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_one, eval_neg,
    eval_ofNat, ledD4, Q4x, P1x]
  ring

/-- Derivative of the two quadratics in the factorisation of `Q4x`. -/
lemma quad_deriv (e : ℂ) : (X ^ 2 - C e * X + 1 : Polynomial ℂ).derivative = 2 * X - C e := by
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C, derivative_X,
    derivative_pow, derivative_one, map_natCast, map_ofNat]
  ring

/-- **Roots of the two quadratics.**  If `c, d` are real with `2 < c`, `2 < d`, `c ≠ d` and
`z ∈ ℂ` is a root of `(X²−cX+1)(X²−dX+1)`, then `z` is a root of one of the two quadratics,
`2z − c ≠ 0` (resp. `2z − d ≠ 0`), the *other* quadratic does not vanish at `z`, and
`z ∉ {0, 1, −1}`. -/
lemma led_quad_root (c d : ℝ) (hc : 2 < c) (hd : 2 < d) (hcd : c ≠ d) (z : ℂ)
    (hz : (z ^ 2 - (c : ℂ) * z + 1) * (z ^ 2 - (d : ℂ) * z + 1) = 0) :
    ((z ^ 2 - (c : ℂ) * z + 1 = 0) ∧ 2 * z - (c : ℂ) ≠ 0 ∧ z ^ 2 - (d : ℂ) * z + 1 ≠ 0
        ∧ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1) ∨
      ((z ^ 2 - (d : ℂ) * z + 1 = 0) ∧ 2 * z - (d : ℂ) ≠ 0 ∧ z ^ 2 - (c : ℂ) * z + 1 ≠ 0
        ∧ z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -1) := by
  rcases mul_eq_zero.mp hz with h | h
  · left
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at h; norm_num at h
      have h2 : ((c : ℂ)) = 2 := by linear_combination -h
      have h3 : c = 2 := Complex.ofReal_inj.mp h2
      linarith
    have hzm1 : z ≠ -1 := by
      intro h1; rw [h1] at h; norm_num at h
      have h2 : ((c + 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
      have h3 : c + 2 = 0 := Complex.ofReal_eq_zero.mp h2
      linarith
    have h2c : 2 * z - (c : ℂ) ≠ 0 := by
      intro h2
      have h2' : (c : ℂ) = 2 * z := by linear_combination -h2
      have h4 : ((c : ℂ)) ^ 2 = 4 := by
        rw [h2']
        have h' := h
        rw [h2'] at h'
        linear_combination (-4) * h'
      have hc2 : c ^ 2 = 4 := by
        have h5 : ((c ^ 2 : ℝ) : ℂ) = ((4 : ℝ) : ℂ) := by push_cast; exact h4
        exact Complex.ofReal_inj.mp h5
      nlinarith [hc]
    have h1d : z ^ 2 - (d : ℂ) * z + 1 ≠ 0 := by
      intro h2
      have key : ((c : ℂ) - (d : ℂ)) * z = 0 := by linear_combination h2 - h
      rcases mul_eq_zero.mp key with h3 | h3
      · have : c = d := Complex.ofReal_inj.mp (sub_eq_zero.mp h3)
        exact hcd this
      · exact hz0 h3
    exact ⟨h, h2c, h1d, hz0, hz1, hzm1⟩
  · right
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at h; norm_num at h
      have h2 : ((d : ℂ)) = 2 := by linear_combination -h
      have h3 : d = 2 := Complex.ofReal_inj.mp h2
      linarith
    have hzm1 : z ≠ -1 := by
      intro h1; rw [h1] at h; norm_num at h
      have h2 : ((d + 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h
      have h3 : d + 2 = 0 := Complex.ofReal_eq_zero.mp h2
      linarith
    have h2d : 2 * z - (d : ℂ) ≠ 0 := by
      intro h2
      have h2' : (d : ℂ) = 2 * z := by linear_combination -h2
      have h4 : ((d : ℂ)) ^ 2 = 4 := by
        rw [h2']
        have h' := h
        rw [h2'] at h'
        linear_combination (-4) * h'
      have hd2 : d ^ 2 = 4 := by
        have h5 : ((d ^ 2 : ℝ) : ℂ) = ((4 : ℝ) : ℂ) := by push_cast; exact h4
        exact Complex.ofReal_inj.mp h5
      nlinarith [hd]
    have h1c : z ^ 2 - (c : ℂ) * z + 1 ≠ 0 := by
      intro h2
      have key : ((d : ℂ) - (c : ℂ)) * z = 0 := by linear_combination h2 - h
      rcases mul_eq_zero.mp key with h3 | h3
      · have : d = c := Complex.ofReal_inj.mp (sub_eq_zero.mp h3)
        exact hcd this.symm
      · exact hz0 h3
    exact ⟨h, h2d, h1c, hz0, hz1, hzm1⟩

/-- Auxiliary real data on `ledC`, `ledD`, used below; the same statement is also available as the
standalone lemma `Work.C17.led_real_data` (module `Submission.Work.C17.led_real_data`). -/
private theorem led_real_data_local (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) :
    (2 : ℝ) < ledC a b ∧ (2 : ℝ) < ledD a b ∧ ledC a b ≠ ledD a b := by
  have hA : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hB : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have habR : (a : ℝ) ≠ (b : ℝ) := by exact_mod_cast hab
  have hDpos : 0 < ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) :=
    mul_pos (by nlinarith) (by nlinarith)
  have hspos : 0 < Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) :=
    Real.sqrt_pos.mpr hDpos
  have hC : (2 : ℝ) < ledC a b := by
    unfold ledC
    have : (2 : ℝ) < 2 * (a : ℝ) * (b : ℝ) := by nlinarith
    nlinarith [Real.sqrt_nonneg (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1))]
  have hD2 : (2 : ℝ) < ledD a b := by
    have hsq : 0 < ((a : ℝ) - (b : ℝ)) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr habR)
    have hlt : ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) < ((a : ℝ) * (b : ℝ) - 1) ^ 2 := by
      nlinarith [hsq]
    have hposy : (0 : ℝ) < (a : ℝ) * (b : ℝ) - 1 := by nlinarith
    have hslt : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) < (a : ℝ) * (b : ℝ) - 1 :=
      (Real.sqrt_lt' hposy).mpr hlt
    unfold ledD
    linarith
  have hne : ledC a b ≠ ledD a b := by
    intro h
    have hzero : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) = 0 := by
      unfold ledC ledD at h
      linarith
    linarith [hspos, hzero]
  exact ⟨hC, hD2, hne⟩

/-- Auxiliary factorisation of `Q4x` over `ℂ`, used below; the same statement is also available as
the standalone lemma `Work.C17.led_factor` (module `Submission.Work.C17.led_factor`). -/
private theorem led_factor_local (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (Q4x a b).map (algebraMap ℚ ℂ)
      = (X ^ 2 - C (((ledC a b : ℝ)) : ℂ) * X + 1)
          * (X ^ 2 - C (((ledD a b : ℝ)) : ℂ) * X + 1) := by
  have hA : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hB : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hD : 0 ≤ ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) :=
    le_of_lt (mul_pos (by nlinarith) (by nlinarith))
  have hs : Real.sqrt (((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1)) ^ 2
      = ((a : ℝ) ^ 2 - 1) * ((b : ℝ) ^ 2 - 1) := Real.sq_sqrt hD
  have hsum : ledC a b + ledD a b = 4 * (a : ℝ) * (b : ℝ) := by unfold ledC ledD; ring
  have hprod : ledC a b * ledD a b + 2 = 4 * (a : ℝ) ^ 2 + 4 * (b : ℝ) ^ 2 - 2 := by
    unfold ledC ledD
    nlinarith [hs]
  have hsumC : (((ledC a b : ℝ)) : ℂ) + (((ledD a b : ℝ)) : ℂ) = 4 * (a : ℂ) * (b : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hsum
    push_cast at h ⊢
    exact h
  have hprodC : (((ledC a b : ℝ)) : ℂ) * (((ledD a b : ℝ)) : ℂ) + 2
      = 4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 2 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hprod
    push_cast at h ⊢
    exact h
  apply Polynomial.funext
  intro z
  rw [← Polynomial.eval₂_eq_eval_map]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, Q4x,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  push_cast
  norm_num
  linear_combination (z ^ 3 + z) * hsumC - z ^ 2 * hprodC

theorem local_exp_data (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b) (z : ℂ)
    (hz : (Q4x a b).eval₂ (algebraMap ℚ ℂ) z = 0) :
    (P2x a b).eval₂ (algebraMap ℚ ℂ) z = 0 ∧
      (P1x a b).eval₂ (algebraMap ℚ ℂ) z
        = (Polynomial.derivative (P2x a b)).eval₂ (algebraMap ℚ ℂ) z ∧
      (Polynomial.derivative (P2x a b)).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  -- the real data on `ledC`, `ledD`
  obtain ⟨hc, hd, hcd⟩ := led_real_data_local a b ha hb hab
  -- the factorisation of `Q4x` over `ℂ`
  have hfac := led_factor_local a b ha hb
  have hP2 : (P2x a b).eval₂ (algebraMap ℚ ℂ) z = 0 := by
    rw [show P2x a b = (X - 1) * X * (X + 1) * Q4x a b from rfl, Polynomial.eval₂_mul,
      Polynomial.eval₂_mul, Polynomial.eval₂_mul, hz, mul_zero]
  have hD4x : (Polynomial.derivative (Q4x a b)).eval₂ (algebraMap ℚ ℂ) z
      = (ledD4 a b).eval₂ (algebraMap ℚ ℂ) z := by rw [Q4x_derivative]
  have hfac3 : ((X - 1) * X * (X + 1) : Polynomial ℚ).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) * z * (z + 1) := by
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_one, Polynomial.eval₂_add]
  have hP2deriv : (Polynomial.derivative (P2x a b)).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) * z * (z + 1) * (ledD4 a b).eval₂ (algebraMap ℚ ℂ) z := by
    rw [show P2x a b = (X - 1) * X * (X + 1) * Q4x a b from rfl, Polynomial.derivative_mul]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hz, hD4x, hfac3, mul_zero, zero_add]
  have h12 : (P1x a b).eval₂ (algebraMap ℚ ℂ) z
      = (Polynomial.derivative (P2x a b)).eval₂ (algebraMap ℚ ℂ) z := by
    rw [hP2deriv, P1x_eq]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, hz]
    ring
  refine ⟨hP2, h12, ?_⟩
  rw [hP2deriv]
  have hzQ : ((Q4x a b).map (algebraMap ℚ ℂ)).eval z = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]; exact hz
  have hprod : (z ^ 2 - (ledC a b : ℂ) * z + 1) * (z ^ 2 - (ledD a b : ℂ) * z + 1) = 0 := by
    rw [hfac] at hzQ
    simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_ofNat] using hzQ
  have hDm : ((Q4x a b).map (algebraMap ℚ ℂ)).derivative
      = (ledD4 a b).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.derivative_map, Q4x_derivative]
  have hderiv : ((Q4x a b).map (algebraMap ℚ ℂ)).derivative.eval z
      = (2 * z - ((ledC a b : ℝ) : ℂ)) * (z ^ 2 - ((ledD a b : ℝ) : ℂ) * z + 1)
        + (z ^ 2 - ((ledC a b : ℝ) : ℂ) * z + 1) * (2 * z - ((ledD a b : ℝ) : ℂ)) := by
    rw [hfac, Polynomial.derivative_mul, quad_deriv, quad_deriv]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    try ring
  have hDeval : (ledD4 a b).eval₂ (algebraMap ℚ ℂ) z
      = ((Q4x a b).map (algebraMap ℚ ℂ)).derivative.eval z := by
    rw [Polynomial.eval₂_eq_eval_map, hDm]
  have hDne : (ledD4 a b).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
    rw [hDeval, hderiv]
    rcases led_quad_root (ledC a b) (ledD a b) hc hd hcd z hprod with
      ⟨h1, h2c, h1d, -, -, -⟩ | ⟨h1, h2d, h1c, -, -, -⟩
    · rw [h1]; simp only [zero_mul, add_zero]; exact mul_ne_zero h2c h1d
    · rw [h1]; simp only [mul_zero, zero_add]; exact mul_ne_zero h1c h2d
  rcases led_quad_root (ledC a b) (ledD a b) hc hd hcd z hprod with
    ⟨-, -, -, hz0, hz1, hzm1⟩ | ⟨-, -, -, hz0, hz1, hzm1⟩
  · have hzp1 : z + 1 ≠ 0 := by intro hh; exact hzm1 (by linear_combination hh)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz1) hz0) hzp1) hDne
  · have hzp1 : z + 1 ≠ 0 := by intro hh; exact hzm1 (by linear_combination hh)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz1) hz0) hzp1) hDne

end

end Work.C17
