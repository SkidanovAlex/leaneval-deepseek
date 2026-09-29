import Mathlib
import Submission.Work.TMC7Core.Avalanche.dframe

set_option maxHeartbeats 1000000

open Matrix

/-!
# `TMC7Core.Avalanche.lambda_pair_bound`

For a unitary `2×2` complex matrix `W` and real `s, s'` with `s², s'² ≥ μ² - 1`, `μ ≥ 2`, the
hypothesis

`(s² + (s²)⁻¹) (s'² + (s'²)⁻¹) < μ ‖Dm s' · W · Dm s‖_F²`

forces `‖W 0 0‖² > 1/μ - 2/(μ²-1)²`.

This is the "λ-pair" bound of the avalanche principle: a lower bound for a diagonal entry of a
unitary, in terms of the Frobenius norm of `Dm s' · W · Dm s`.

The proof has three ingredients:

* `frob_pair_expand`: the exact expansion
  `‖Dm s' · W · Dm s‖_F² = s'²s²x + (1-x)(s'²(s²)⁻¹ + (s'²)⁻¹s²) + x(s²)⁻¹(s'²)⁻¹`
  where `x = ‖W 0 0‖²` (uses unitarity: the row and column square-sums of `W` equal `1`).
* `pair_key_arith`: the real inequality
  `(μ-2)(A/B + B/A) ≤ 2μ (A - A⁻¹)(B - B⁻¹)/(μ²-1)²` for `A, B ≥ μ²-1`, `μ ≥ 2`.
* `x_bound_of_key`: the final one-line inference from the two displayed inequalities.
-/

namespace Work.TMC7Core.Avalanche

/-! ## 1. Expansion of `frob (Dm s' * W * Dm s) ^ 2` for unitary `W` -/

private lemma frob_pair_expand (s s' : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1) :
    frob (Dm s' * W * Dm s) ^ 2
      = s' ^ 2 * s ^ 2 * ‖W 0 0‖ ^ 2
        + (1 - ‖W 0 0‖ ^ 2) * (s' ^ 2 * (s ^ 2)⁻¹ + (s' ^ 2)⁻¹ * s ^ 2)
        + ‖W 0 0‖ ^ 2 * ((s ^ 2)⁻¹ * (s' ^ 2)⁻¹) := by
  have hconj (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
    rw [Complex.star_def, mul_comm]
    exact (Complex.normSq_eq_conj_mul_self (z := z)).symm
  have hconj' (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
    rw [Complex.star_def]
    exact (Complex.normSq_eq_conj_mul_self (z := z)).symm
  have hrow : ‖W 0 0‖ ^ 2 + ‖W 0 1‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hW' 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at h
    rw [hconj, hconj] at h
    simp only [Matrix.one_apply_eq] at h
    rw [Complex.sq_norm, Complex.sq_norm]
    exact_mod_cast h
  have hcol : ‖W 0 0‖ ^ 2 + ‖W 1 0‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hW 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at h
    rw [hconj', hconj'] at h
    simp only [Matrix.one_apply_eq] at h
    rw [Complex.sq_norm, Complex.sq_norm]
    exact_mod_cast h
  have hrow1 : ‖W 1 0‖ ^ 2 + ‖W 1 1‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hW' 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at h
    rw [hconj, hconj] at h
    simp only [Matrix.one_apply_eq] at h
    rw [Complex.sq_norm, Complex.sq_norm]
    exact_mod_cast h
  rw [frob, Real.sq_sqrt (by positivity)]
  have e0 : (Dm s' * W * Dm s) 0 0 = ((s':ℝ):ℂ) * W 0 0 * ((s:ℝ):ℂ) := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (Dm s' * W * Dm s) 0 1 = ((s':ℝ):ℂ) * W 0 1 * (((s⁻¹:ℝ)):ℂ) := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : (Dm s' * W * Dm s) 1 0 = (((s'⁻¹:ℝ)):ℂ) * W 1 0 * ((s:ℝ):ℂ) := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
  have e3 : (Dm s' * W * Dm s) 1 1 = (((s'⁻¹:ℝ)):ℂ) * W 1 1 * (((s⁻¹:ℝ)):ℂ) := by
    simp [Dm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e0, e1, e2, e3]
  have n0 : ‖((s':ℝ):ℂ) * W 0 0 * ((s:ℝ):ℂ)‖ ^ 2 = s' ^ 2 * s ^ 2 * ‖W 0 0‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal, Complex.sq_norm]
    ring
  have n1 : ‖((s':ℝ):ℂ) * W 0 1 * (((s⁻¹:ℝ)):ℂ)‖ ^ 2
      = s' ^ 2 * (s ^ 2)⁻¹ * ‖W 0 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal, Complex.sq_norm]
    rw [← inv_pow]
    ring
  have n2 : ‖(((s'⁻¹:ℝ)):ℂ) * W 1 0 * ((s:ℝ):ℂ)‖ ^ 2
      = (s' ^ 2)⁻¹ * s ^ 2 * ‖W 1 0‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal, Complex.sq_norm]
    rw [← inv_pow]
    ring
  have n3 : ‖(((s'⁻¹:ℝ)):ℂ) * W 1 1 * (((s⁻¹:ℝ)):ℂ)‖ ^ 2
      = (s' ^ 2)⁻¹ * (s ^ 2)⁻¹ * ‖W 1 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal, Complex.sq_norm]
    rw [← inv_pow, ← inv_pow]
    ring
  rw [n0, n1, n2, n3]
  have k1 : ‖W 0 1‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by linarith
  have k2 : ‖W 1 0‖ ^ 2 = 1 - ‖W 0 0‖ ^ 2 := by linarith
  have k3 : ‖W 1 1‖ ^ 2 = ‖W 0 0‖ ^ 2 := by linarith
  rw [k1, k2, k3]
  ring

/-! ## 2. The arithmetic core -/

private lemma pair_key_arith (μ A B : ℝ) (hμ : 2 ≤ μ)
    (hA : μ ^ 2 - 1 ≤ A) (hB : μ ^ 2 - 1 ≤ B) :
    (μ - 2) * (A / B + B / A) ≤ 2 * μ * ((A - A⁻¹) * (B - B⁻¹)) / (μ ^ 2 - 1) ^ 2 := by
  have hC3 : (3 : ℝ) ≤ μ ^ 2 - 1 := by nlinarith [hμ]
  have hCpos : 0 < μ ^ 2 - 1 := by linarith
  have hC2pos : 0 < (μ ^ 2 - 1) ^ 2 := by positivity
  have hμpos : 0 < μ := by linarith
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := by linarith
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hBne : B ≠ 0 := ne_of_gt hBpos
  -- square bounds
  have hA2 : (μ ^ 2 - 1) ^ 2 ≤ A ^ 2 := by
    have h1 : 0 ≤ A - (μ ^ 2 - 1) := by linarith
    have h2 : 0 ≤ A + (μ ^ 2 - 1) := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hB2 : (μ ^ 2 - 1) ^ 2 ≤ B ^ 2 := by
    have h1 : 0 ≤ B - (μ ^ 2 - 1) := by linarith
    have h2 : 0 ≤ B + (μ ^ 2 - 1) := by linarith
    nlinarith [mul_nonneg h1 h2]
  -- the quartic bound `μ (2 C² - 1) ≤ 2 C⁴` for `C = μ² - 1 ≥ 3`
  have hmuC : μ ≤ (μ ^ 2 - 1) + 1 := by nlinarith
  have hquartic : μ * (2 * (μ ^ 2 - 1) ^ 2 - 1) ≤ 2 * (μ ^ 2 - 1) ^ 4 := by
    have h2 : 0 ≤ 2 * (μ ^ 2 - 1) ^ 2 - 1 := by nlinarith [hC3]
    have hs1 : μ * (2 * (μ ^ 2 - 1) ^ 2 - 1)
        ≤ ((μ ^ 2 - 1) + 1) * (2 * (μ ^ 2 - 1) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hmuC h2
    have hs2 : ((μ ^ 2 - 1) + 1) * (2 * (μ ^ 2 - 1) ^ 2 - 1) ≤ 2 * (μ ^ 2 - 1) ^ 4 := by
      have h1 : 0 ≤ (μ ^ 2 - 1) ^ 2 - (μ ^ 2 - 1) - 1 := by nlinarith [hC3]
      have h2' : 0 ≤ 2 * (μ ^ 2 - 1) ^ 2 := by nlinarith [hC3]
      have h3 : 0 ≤ (μ ^ 2 - 1) + 1 := by nlinarith [hC3]
      have hid : 2 * (μ ^ 2 - 1) ^ 4 - ((μ ^ 2 - 1) + 1) * (2 * (μ ^ 2 - 1) ^ 2 - 1)
          = 2 * (μ ^ 2 - 1) ^ 2 * ((μ ^ 2 - 1) ^ 2 - (μ ^ 2 - 1) - 1) + ((μ ^ 2 - 1) + 1) := by
        ring
      have hnn : 0 ≤ 2 * (μ ^ 2 - 1) ^ 2 * ((μ ^ 2 - 1) ^ 2 - (μ ^ 2 - 1) - 1) :=
        mul_nonneg h2' h1
      linarith [hid, hnn, h3]
    linarith [hs1, hs2]
  -- coefficient of the linear terms
  have hcoeff : 0 ≤ μ * (μ ^ 2 - 1) ^ 2 + 2 * (μ ^ 2 - 1) ^ 2 - 2 * μ := by nlinarith [hC3]
  -- core inequality: `(μ-2)(v+t)C² ≤ 2μ(v-1)(t-1)` with `v = A²`, `t = B²`, `C = μ²-1`
  have hcore : (μ - 2) * (A ^ 2 + B ^ 2) * (μ ^ 2 - 1) ^ 2
      ≤ 2 * μ * ((A ^ 2 - 1) * (B ^ 2 - 1)) := by
    have hid : 2 * μ * (A ^ 2 - 1) * (B ^ 2 - 1) - (μ - 2) * (A ^ 2 + B ^ 2) * (μ ^ 2 - 1) ^ 2
        = 2 * (2 * (μ ^ 2 - 1) ^ 4 - μ * (2 * (μ ^ 2 - 1) ^ 2 - 1))
          + (A ^ 2 - (μ ^ 2 - 1) ^ 2 + (B ^ 2 - (μ ^ 2 - 1) ^ 2))
              * (μ * (μ ^ 2 - 1) ^ 2 + 2 * (μ ^ 2 - 1) ^ 2 - 2 * μ)
          + 2 * μ * ((A ^ 2 - (μ ^ 2 - 1) ^ 2) * (B ^ 2 - (μ ^ 2 - 1) ^ 2)) := by
      ring
    have hα : 0 ≤ A ^ 2 - (μ ^ 2 - 1) ^ 2 := by linarith
    have hβ : 0 ≤ B ^ 2 - (μ ^ 2 - 1) ^ 2 := by linarith
    have t1 : 0 ≤ 2 * (2 * (μ ^ 2 - 1) ^ 4 - μ * (2 * (μ ^ 2 - 1) ^ 2 - 1)) := by linarith
    have t2 : 0 ≤ (A ^ 2 - (μ ^ 2 - 1) ^ 2)
        * (μ * (μ ^ 2 - 1) ^ 2 + 2 * (μ ^ 2 - 1) ^ 2 - 2 * μ) := mul_nonneg hα hcoeff
    have t3 : 0 ≤ (B ^ 2 - (μ ^ 2 - 1) ^ 2)
        * (μ * (μ ^ 2 - 1) ^ 2 + 2 * (μ ^ 2 - 1) ^ 2 - 2 * μ) := mul_nonneg hβ hcoeff
    have t4 : 0 ≤ 2 * μ * ((A ^ 2 - (μ ^ 2 - 1) ^ 2) * (B ^ 2 - (μ ^ 2 - 1) ^ 2)) :=
      mul_nonneg (by linarith) (mul_nonneg hα hβ)
    linarith [hid, t1, t2, t3, t4]
  -- clear denominators
  rw [le_div_iff₀ hC2pos, div_eq_mul_inv, div_eq_mul_inv]
  have hAB : 0 < A * B := mul_pos hApos hBpos
  have h1 : (A * B⁻¹ + B * A⁻¹) * (A * B) = A ^ 2 + B ^ 2 := by
    field_simp
  have h2 : (A - A⁻¹) * (B - B⁻¹) * (A * B) = (A ^ 2 - 1) * (B ^ 2 - 1) := by
    field_simp
  have key : (μ - 2) * (A * B⁻¹ + B * A⁻¹) * (μ ^ 2 - 1) ^ 2 * (A * B)
      ≤ 2 * μ * ((A - A⁻¹) * (B - B⁻¹)) * (A * B) := by
    have hL : (μ - 2) * (A * B⁻¹ + B * A⁻¹) * (μ ^ 2 - 1) ^ 2 * (A * B)
        = (μ - 2) * (A ^ 2 + B ^ 2) * (μ ^ 2 - 1) ^ 2 := by
      rw [show (μ - 2) * (A * B⁻¹ + B * A⁻¹) * (μ ^ 2 - 1) ^ 2 * (A * B)
            = (μ - 2) * ((A * B⁻¹ + B * A⁻¹) * (A * B)) * (μ ^ 2 - 1) ^ 2
            from by ring, h1]
    have hR : 2 * μ * ((A - A⁻¹) * (B - B⁻¹)) * (A * B)
        = 2 * μ * ((A ^ 2 - 1) * (B ^ 2 - 1)) := by
      rw [show 2 * μ * ((A - A⁻¹) * (B - B⁻¹)) * (A * B)
            = 2 * μ * (((A - A⁻¹) * (B - B⁻¹)) * (A * B)) from by ring, h2]
    rw [hL, hR]
    exact hcore
  exact le_of_mul_le_mul_right key hAB

/-! ## 3. From the two inequalities to the bound on `x = ‖W 0 0‖²` -/

private lemma x_bound_of_key (μ p q x : ℝ) (hμ : 2 ≤ μ) (hpq : 0 < q - p)
    (h2 : q - (μ - 1) * p < μ * x * (q - p))
    (hkey : (μ - 2) * p ≤ 2 * μ * (q - p) / (μ ^ 2 - 1) ^ 2) :
    1 / μ - 2 / (μ ^ 2 - 1) ^ 2 < x := by
  have hμpos : 0 < μ := by linarith
  have hC1 : 0 < μ ^ 2 - 1 := by nlinarith [hμ]
  have hC2pos : 0 < (μ ^ 2 - 1) ^ 2 := pow_pos hC1 2
  have hkey' : (μ - 2) * p * (μ ^ 2 - 1) ^ 2 ≤ 2 * μ * (q - p) := by
    rw [le_div_iff₀ hC2pos] at hkey
    linarith [hkey]
  -- multiply the strict inequality by the positive constant `C²`
  have hA : ((q - p) - (μ - 2) * p) * (μ ^ 2 - 1) ^ 2
      < (μ * x * (q - p)) * (μ ^ 2 - 1) ^ 2 := by
    have h := mul_lt_mul_of_pos_right h2 hC2pos
    linarith [h]
  have hB : ((q - p) - (μ - 2) * p) * (μ ^ 2 - 1) ^ 2
      ≥ (q - p) * ((μ ^ 2 - 1) ^ 2 - 2 * μ) := by
    have hexp : ((q - p) - (μ - 2) * p) * (μ ^ 2 - 1) ^ 2
        - (q - p) * ((μ ^ 2 - 1) ^ 2 - 2 * μ)
        = 2 * μ * (q - p) - (μ - 2) * p * (μ ^ 2 - 1) ^ 2 := by ring
    linarith [hexp, hkey']
  have hC : (q - p) * ((μ ^ 2 - 1) ^ 2 - 2 * μ) < (μ * x * (q - p)) * (μ ^ 2 - 1) ^ 2 :=
    lt_of_le_of_lt hB hA
  have hD : (μ ^ 2 - 1) ^ 2 - 2 * μ < μ * x * (μ ^ 2 - 1) ^ 2 := by
    nlinarith [hC, hpq]
  have hE : ((μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2) < x := by
    rw [div_lt_iff₀ (mul_pos hμpos hC2pos)]
    nlinarith [hD]
  have hF : ((μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2)
      = 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have hCne : μ ^ 2 - 1 ≠ 0 := ne_of_gt hC1
    field_simp
  rw [← hF]
  exact hE

/-! ## 4. The bound -/

theorem lambda_pair_bound (s s' μ : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ)
    (hW : W.conjTranspose * W = 1) (hW' : W * W.conjTranspose = 1)
    (hs : μ ^ 2 - 1 ≤ s ^ 2) (hs' : μ ^ 2 - 1 ≤ s' ^ 2) (hμ : 2 ≤ μ)
    (hpair : (s ^ 2 + (s ^ 2)⁻¹) * (s' ^ 2 + (s' ^ 2)⁻¹) < μ * frob (Dm s' * W * Dm s) ^ 2) :
    1 / μ - 2 / (μ ^ 2 - 1) ^ 2 < ‖W 0 0‖ ^ 2 := by
  have hfrob := frob_pair_expand s s' W hW hW'
  set A : ℝ := s ^ 2 with hAdef
  set B : ℝ := s' ^ 2 with hBdef
  set xx : ℝ := ‖W 0 0‖ ^ 2 with hxdef
  have hsA : μ ^ 2 - 1 ≤ A := hs
  have hsB : μ ^ 2 - 1 ≤ B := hs'
  set p : ℝ := A / B + B / A with hpdef
  set q : ℝ := A * B + A⁻¹ * B⁻¹ with hqdef
  have hAB : (A + A⁻¹) * (B + B⁻¹) = q + p := by
    rw [hqdef, hpdef]
    ring
  have hqp : q - p = (A - A⁻¹) * (B - B⁻¹) := by
    rw [hqdef, hpdef]
    ring
  have hfp : frob (Dm s' * W * Dm s) ^ 2 = p + xx * (q - p) := by
    rw [hfrob, hpdef, hqdef]
    ring
  rw [hAB, hfp] at hpair
  have h2 : q - (μ - 1) * p < μ * xx * (q - p) := by nlinarith [hpair]
  have hCpos : 0 < μ ^ 2 - 1 := by nlinarith [hμ]
  have hA1 : 1 < A := by
    have : (3 : ℝ) ≤ μ ^ 2 - 1 := by nlinarith [hμ]
    linarith
  have hB1 : 1 < B := by
    have : (3 : ℝ) ≤ μ ^ 2 - 1 := by nlinarith [hμ]
    linarith
  have hp_pos : 0 < q - p := by
    rw [hqp]
    exact mul_pos (by linarith [inv_lt_one_of_one_lt₀ hA1])
      (by linarith [inv_lt_one_of_one_lt₀ hB1])
  have hka : (μ - 2) * p ≤ 2 * μ * (q - p) / (μ ^ 2 - 1) ^ 2 := by
    have h := pair_key_arith μ A B hμ hsA hsB
    rw [← hpdef, ← hqp] at h
    exact h
  exact x_bound_of_key μ p q xx hμ hp_pos h2 hka

end Work.TMC7Core.Avalanche
