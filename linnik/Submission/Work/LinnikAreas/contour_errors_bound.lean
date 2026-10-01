import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_circleExcess_le
import Submission.Work.LinnikAreas.LFunction_eighth_line
import Submission.Work.LinnikAreas.LFunction_quarter_strip
import Submission.Work.LinnikAreas.contour_assembly_arith
import Submission.Work.LinnikAreas.contour_horizontal_edge

/-!
# Bounding the two contour-shift error integrals of the triangle-kernel Perron argument

`Work.LinnikAreas.contour_errors_bound` estimates the two error terms produced by shifting the
Perron contour for `triFun ψ β x s = ζ(s+β)L(s+β,ψ)x^s/(s(s+1))` from `Re s = 1` down to
`Re s = 5/8 - β`:

* the integral along the vertical line `Re s = 5/8 - β`, where `|ζ(5/8+it)L(5/8+it,ψ)|` is
  controlled by `(1+|t|)^{7/16}·N^{1/4}(1+|t|)^{1/4}` (convexity), and the kernel `1/(s(s+1))`
  supplies the decay `|y|^{-21/16}`;
* the integrals along the two horizontal segments of height `±T`, where `x^u` is bounded by
  `x + x^{5/8-β}` resp. `x + x^{1-β}` and the `L`-function by `N^{1/4}(1+T)^{1/4}` (for
  `5/8 ≤ Re ≤ 1`) or by `log(2N) + log(2+T) + 6` (for `Re ≥ 1`).
-/

set_option maxHeartbeats 1600000

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory intervalIntegral Filter
open scoped Real BigOperators

noncomputable section

/-- The two ways of writing `5/8` as a complex number agree. -/
private lemma c58_conv : (5 / 8 : ℂ) = (((5 : ℝ) / 8 : ℝ) : ℂ) := by push_cast; ring

/-! ### Analytic inputs -/

/-- Uniform bound for `ζ` on the strip `5/8 ≤ Re s ≤ 2`, `|Im s| ≥ 1`, with exponent `7/16`.
This is the classical convexity-type strip bound `ζ(σ+it) = O((1+|t|)^{1/2-δ/2})` at `δ = 1/8`,
valid on the whole strip `1/2 + δ ≤ Re s ≤ 2`. -/
theorem zeta_strip_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 5 / 8 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ ((7 : ℝ) / 16) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Zeta.zeta_strip_growth
  refine ⟨C * 9 * 4 ^ ((7 : ℝ) / 16),
    mul_pos (mul_pos hCpos (by norm_num))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) _), ?_⟩
  intro σ t hσlo hσhi ht
  have h := hC (1 / 8) σ t (by norm_num) (by norm_num) (by linarith) hσhi ht
  rw [show (1 : ℝ) + 1 / (1 / 8) = 9 by norm_num,
      show (1 / 2 - (1 / 8) / 2 : ℝ) = 7 / 16 by norm_num] at h
  have hpow : (|t| + 3) ^ ((7 : ℝ) / 16)
      ≤ 4 ^ ((7 : ℝ) / 16) * (1 + |t|) ^ ((7 : ℝ) / 16) := by
    have hbase : |t| + 3 ≤ 4 * (1 + |t|) := by nlinarith [ht]
    have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ |t| + 3) hbase
      (by norm_num : (0 : ℝ) ≤ (7 : ℝ) / 16)
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ 1 + |t|)] at hr
  calc
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by rw [mul_comm]
    _ ≤ C * 9 * (|t| + 3) ^ ((7 : ℝ) / 16) := h
    _ ≤ C * 9 * (4 ^ ((7 : ℝ) / 16) * (1 + |t|) ^ ((7 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (C * 9 * 4 ^ ((7 : ℝ) / 16)) * (1 + |t|) ^ ((7 : ℝ) / 16) := by ring

/-- Bound for `ζ` on the `5/8` line, `(1+|t|)^{7/16}`, valid for **all** real `t`
(the small-`t` range is handled by the Euler–Maclaurin bound `zeta_strip_smallIm_bound`). -/
theorem zeta_line_58 :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ C * (1 + |y|) ^ ((7 : ℝ) / 16) := by
  obtain ⟨CZ, hCZpos, hCZ⟩ := zeta_strip_uniform
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound
  refine ⟨max CZ (C₂ * 9 * (1 + 8 / 3)) + 1, by positivity, ?_⟩
  intro y
  have hone : (1 : ℝ) ≤ (1 + |y|) ^ ((7 : ℝ) / 16) :=
    Real.one_le_rpow (by linarith [abs_nonneg y]) (by norm_num)
  have hC1 : CZ ≤ max CZ (C₂ * 9 * (1 + 8 / 3)) + 1 := by
    linarith [le_max_left CZ (C₂ * 9 * (1 + 8 / 3))]
  have hC2le : C₂ * 9 * (1 + 8 / 3) ≤ max CZ (C₂ * 9 * (1 + 8 / 3)) + 1 := by
    linarith [le_max_right CZ (C₂ * 9 * (1 + 8 / 3))]
  rcases lt_or_ge (|y|) 1 with hy | hy
  · -- small imaginary part: the Euler–Maclaurin bound
    have hy2 : |y| ≤ 2 := by linarith
    have hs : ((((5 : ℝ) / 8 : ℝ)) : ℂ) + Complex.I * (y : ℂ) ≠ 1 := by
      intro hcon
      have h2 : (5 : ℝ) / 8 = 1 := by
        have := congrArg Complex.re hcon
        simpa using this
      norm_num at h2
    have hb := hC₂ (1 / 8) (5 / 8) y (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hy2 hs
    have hnorm : (3 / 8 : ℝ) ≤ ‖((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1‖ := by
      have h := abs_re_le_norm (((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1)
      have hre : (((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1).re = -(3 / 8) := by
        simp
        norm_num
      rw [hre, abs_neg] at h
      have h2 : |(3 : ℝ) / 8| = 3 / 8 := abs_of_nonneg (by norm_num)
      rwa [h2] at h
    have hden : (0 : ℝ) < ‖((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1‖ :=
      lt_of_lt_of_le (by norm_num) hnorm
    have hinv : 1 / ‖((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1‖ ≤ 8 / 3 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 8) hnorm
      simpa using this
    have hval : ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ C₂ * 9 * (1 + 8 / 3) := by
      have hbr : Complex.I * (y : ℂ) = (y : ℂ) * Complex.I := mul_comm _ _
      have hb' : ‖riemannZeta ((((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖
          ≤ C₂ * 9 * (1 + 1 / ‖((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1‖) := by
        have h9 : (1 : ℝ) + 1 / (1 / 8) = 9 := by norm_num
        rw [h9] at hb
        simpa only [hbr] using hb
      calc ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
          ≤ C₂ * 9 * (1 + 1 / ‖((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I - 1‖) := hb'
        _ ≤ C₂ * 9 * (1 + 8 / 3) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ C₂ * 9 * (1 + 8 / 3) := hval
      _ ≤ max CZ (C₂ * 9 * (1 + 8 / 3)) + 1 := hC2le
      _ = (max CZ (C₂ * 9 * (1 + 8 / 3)) + 1) * 1 := by ring
      _ ≤ (max CZ (C₂ * 9 * (1 + 8 / 3)) + 1) * (1 + |y|) ^ ((7 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
  · -- large imaginary part: the strip bound
    have hb := hCZ (5 / 8) y (by norm_num) (by norm_num) hy
    have hb' : ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ CZ * (1 + |y|) ^ ((7 : ℝ) / 16) := hb
    calc ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ CZ * (1 + |y|) ^ ((7 : ℝ) / 16) := hb'
      _ ≤ (max CZ (C₂ * 9 * (1 + 8 / 3)) + 1) * (1 + |y|) ^ ((7 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (by positivity) _)

/-- From `LFunction_log_le_right`: for `Re z ≥ 1` the `L`-function of a non-trivial character is
bounded by `log(2N) + log(2 + |Im z|) + 6`. -/
theorem LFunction_log_bound {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (z : ℂ) (hz : 1 ≤ z.re) :
    ‖DirichletCharacter.LFunction ψ z‖ ≤ Real.log (2 * N) + Real.log (2 + |z.im|) + 6 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog := Commons.NumberTheory.DirichletCharacter.LFunction_log_le_right ψ hψ hz
  have hApos : 0 < Real.log (N : ℝ) + Real.log (2 + |z.im|) + 6 := by
    have h1 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have h2 : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    linarith
  have hle : ‖DirichletCharacter.LFunction ψ z‖
      ≤ Real.log (N : ℝ) + Real.log (2 + |z.im|) + 6 := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction ψ z)) with h0 | h0
    · rw [← h0]; linarith
    · rw [← Real.exp_log h0, ← Real.exp_log hApos]
      exact Real.exp_le_exp.mpr hlog
  have h3 : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    refine Real.log_le_log (by linarith) ?_
    linarith
  linarith

/-! ### The vertical edge -/

/-- Denominator estimate on the vertical line `Re s = 5/8 - β`: `|s(s+1)| ≥ (5/128)(1+y²)`. -/
lemma vertical_denom (β y : ℝ) (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) :
    (5 / 128 : ℝ) * (1 + y ^ 2) ≤
      ‖((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖
        * ‖((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) + 1‖ := by
  set s : ℂ := ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) with hs
  have hsre : s.re = 5 / 8 - β := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hs1re : (s + 1).re = 13 / 8 - β := by
    rw [Complex.add_re, hsre, Complex.one_re]; ring
  have hA : (1 / 8 : ℝ) ≤ ‖s‖ := by
    have h := abs_re_le_norm s
    rw [hsre, abs_of_nonpos (by linarith)] at h
    linarith
  have hA2 : |y| ≤ ‖s‖ := by
    have h := abs_im_le_norm s
    rwa [hsim] at h
  have hB : (5 / 8 : ℝ) ≤ ‖s + 1‖ := by
    have h := abs_re_le_norm (s + 1)
    rw [hs1re, abs_of_nonneg (by linarith)] at h
    linarith
  have hB2 : |y| ≤ ‖s + 1‖ := by
    have h := abs_im_le_norm (s + 1)
    simpa [Complex.add_im, hsim] using h
  rcases le_or_gt (|y|) (5 / 8) with h | h
  · have h1 : (1 / 8 : ℝ) * (5 / 8) ≤ ‖s‖ * ‖s + 1‖ :=
      mul_le_mul hA hB (by norm_num) (norm_nonneg _)
    have hs2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [h1, hs2, h, abs_nonneg y]
  · have h5 : (5 / 8 : ℝ) ≤ |y| := le_of_lt h
    have h1 : (5 / 8 : ℝ) * (5 / 8) ≤ ‖s‖ * ‖s + 1‖ :=
      mul_le_mul (le_trans h5 hA2) (le_trans h5 hB2) (by norm_num) (norm_nonneg _)
    have hs2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [h1, hs2, h5, abs_nonneg y]

/-- Kills the rational factor: `(1+|y|)^{11/16}/(1+y²) ≤ 2(1+|y|)^{-21/16}`. -/
lemma rpow_ratio_le (y : ℝ) :
    (1 + |y|) ^ ((11 : ℝ) / 16) / (1 + y ^ 2) ≤ 2 * (1 + |y|) ^ (-(21 : ℝ) / 16) := by
  have hbase : (0 : ℝ) < 1 + |y| := by positivity
  have hsq : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hkey : (1 + |y|) ^ 2 ≤ 2 * (1 + y ^ 2) := by
    have hs2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [sq_nonneg (|y| - 1), hs2, abs_nonneg y]
  have hexp : (1 + |y|) ^ ((11 : ℝ) / 16)
      = (1 + |y|) ^ (2 : ℝ) * (1 + |y|) ^ (-(21 : ℝ) / 16) := by
    rw [← Real.rpow_add hbase]
    norm_num
  rw [hexp, Real.rpow_two, div_le_iff₀ hsq]
  calc (1 + |y|) ^ 2 * (1 + |y|) ^ (-(21 : ℝ) / 16)
      ≤ (2 * (1 + y ^ 2)) * (1 + |y|) ^ (-(21 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg (le_of_lt hbase) _)
    _ = 2 * (1 + |y|) ^ (-(21 : ℝ) / 16) * (1 + y ^ 2) := by ring

/-- Pointwise bound for the integrand on the vertical line `Re s = 5/8 - β`, given strip bounds
for `ζ` (exponent `7/16`) and for the primitive `L`-function (exponent `1/4`). -/
lemma norm_triFun_vertical {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {β x y zc lc : ℝ}
    (hzc : 0 ≤ zc) (hlc : 0 ≤ lc)
    (hζ : ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ zc * (1 + |y|) ^ ((7 : ℝ) / 16))
    (hL : ‖DirichletCharacter.LFunction ψ ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((1 : ℝ) / 4))
    (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) :
    ‖triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ zc * lc * (256 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * (1 + |y|) ^ (-(21 : ℝ) / 16) := by
  set s : ℂ := ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I) with hs
  have hsre : s.re = 5 / 8 - β := by simp [hs]
  have hsplus : s + (β : ℂ) = ((((5 : ℝ) / 8 : ℝ)) : ℂ) + (y : ℂ) * Complex.I := by
    rw [hs]
    push_cast
    ring
  have hxrpow : ‖(x : ℂ) ^ s‖ = x ^ ((5 / 8 - β : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx s, hsre]
  have hden : (5 / 128 : ℝ) * (1 + y ^ 2) ≤ ‖s * (s + 1)‖ := by
    have h := vertical_denom β y hβ hβ1
    rw [norm_mul]
    exact h
  have h11 : (1 + |y|) ^ ((7 : ℝ) / 16) * (1 + |y|) ^ ((1 : ℝ) / 4)
      = (1 + |y|) ^ ((11 : ℝ) / 16) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |y|)]
    norm_num
  have hnum : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
      ≤ zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((11 : ℝ) / 16) := by
    rw [hsplus]
    calc ‖riemannZeta ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
          * ‖DirichletCharacter.LFunction ψ ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ (zc * (1 + |y|) ^ ((7 : ℝ) / 16))
            * (lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul hζ hL (norm_nonneg _)
            (mul_nonneg hzc (Real.rpow_nonneg (by positivity) _))
      _ = zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4)
            * ((1 + |y|) ^ ((7 : ℝ) / 16) * (1 + |y|) ^ ((1 : ℝ) / 4)) := by ring
      _ = zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((11 : ℝ) / 16) := by rw [h11]
  have hmain : ‖triFun ψ β x s‖
      = ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
          * ‖(x : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
    simp only [triFun, zlFun, norm_div, norm_mul]
  rw [hmain, hxrpow]
  have hposden : (0 : ℝ) < (5 / 128) * (1 + y ^ 2) := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hxe : (0 : ℝ) ≤ x ^ ((5 / 8 - β : ℝ)) := Real.rpow_nonneg (le_of_lt hx) _
  have hnum2 : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        * x ^ ((5 / 8 - β : ℝ))
      ≤ zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((11 : ℝ) / 16)
          * x ^ ((5 / 8 - β : ℝ)) :=
    mul_le_mul_of_nonneg_right hnum hxe
  have hnum2nn : (0 : ℝ) ≤ zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4)
      * (1 + |y|) ^ ((11 : ℝ) / 16) * x ^ ((5 / 8 - β : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hzc hlc) hN0)
      (Real.rpow_nonneg (by positivity) _)) hxe
  have hstep : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        * x ^ ((5 / 8 - β : ℝ)) / ‖s * (s + 1)‖
      ≤ (zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((11 : ℝ) / 16)
          * x ^ ((5 / 8 - β : ℝ))) / ((5 / 128) * (1 + y ^ 2)) := by
    refine le_trans (div_le_div_of_nonneg_right hnum2 (norm_nonneg _)) ?_
    exact div_le_div_of_nonneg_left hnum2nn hposden hden
  refine hstep.trans ?_
  have hratio : (1 + |y|) ^ ((11 : ℝ) / 16) / (1 + y ^ 2)
      ≤ 2 * (1 + |y|) ^ (-(21 : ℝ) / 16) := rpow_ratio_le y
  have hbase : 0 ≤ zc * lc * (128 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hzc hlc) (by norm_num)) (mul_nonneg hN0 hxe)
  have hdeninv : (((5 / 128 : ℝ) * (1 + y ^ 2)))⁻¹ = (128 / 5) * (1 + y ^ 2)⁻¹ := by
    rw [mul_inv, show ((5 / 128 : ℝ))⁻¹ = 128 / 5 by norm_num]
  have hrewrite : (zc * lc * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((11 : ℝ) / 16)
        * x ^ ((5 / 8 - β : ℝ))) / ((5 / 128) * (1 + y ^ 2))
      = zc * lc * (128 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * ((1 + |y|) ^ ((11 : ℝ) / 16) / (1 + y ^ 2)) := by
    rw [div_eq_mul_inv, hdeninv]
    ring
  rw [hrewrite]
  calc zc * lc * (128 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
        * ((1 + |y|) ^ ((11 : ℝ) / 16) / (1 + y ^ 2))
      ≤ zc * lc * (128 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * (2 * (1 + |y|) ^ (-(21 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_left hratio hbase
    _ = zc * lc * (256 / 5) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * (1 + |y|) ^ (-(21 : ℝ) / 16) := by ring

/-- The integral of the majorant: `∫_{-T}^{T} (1+|y|)^{-21/16} dy ≤ 42/5`. -/
lemma integral_one_add_abs_rpow_neg (T : ℝ) (hT : 0 ≤ T) :
    (∫ y in (-T)..T, (1 + |y|) ^ (-(21 : ℝ) / 16)) ≤ 42 / 5 := by
  set f : ℝ → ℝ := fun z => (1 + |z|) ^ (-(21 : ℝ) / 16) with hf
  have hcont : Continuous f := by
    rw [hf]
    exact (continuous_const.add continuous_abs).rpow_const
      (fun z => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + |z|)))
  have hInt1 : IntervalIntegrable f volume (-T) 0 := hcont.intervalIntegrable _ _
  have hInt2 : IntervalIntegrable f volume 0 T := hcont.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
  have hhalf : (∫ x in (1 : ℝ)..(1 + T), x ^ (-(21 : ℝ) / 16)) ≤ 16 / 5 := by
    have hnotin : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + T) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro h
      linarith [h.1]
    have hne : (-(21 : ℝ) / 16) ≠ -1 := by norm_num
    rw [integral_rpow (Or.inr ⟨hne, hnotin⟩), Real.one_rpow]
    have hexp : (-(21 : ℝ) / 16) + 1 = -(5 : ℝ) / 16 := by norm_num
    rw [hexp]
    have hq : (1 + T) ^ (-(5 : ℝ) / 16) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hq0 : (0 : ℝ) ≤ (1 + T) ^ (-(5 : ℝ) / 16) := Real.rpow_nonneg (by linarith) _
    have hrw : ((1 + T) ^ (-(5 : ℝ) / 16) - 1) / (-(5 : ℝ) / 16)
        = (1 - (1 + T) ^ (-(5 : ℝ) / 16)) * (16 / 5) := by
      field_simp
      ring
    rw [hrw]
    nlinarith [hq, hq0]
  have hleft : (∫ y in (-T)..(0 : ℝ), f y) = ∫ x in (1 : ℝ)..(1 + T), x ^ (-(21 : ℝ) / 16) := by
    have hcn := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := (0 : ℝ))
    rw [show -(0 : ℝ) = 0 by norm_num, neg_neg] at hcn
    have hcongr : (∫ x in (-T)..(0 : ℝ), f (-x)) = ∫ x in (-T)..(0 : ℝ), f x := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      show (1 + |(-x)|) ^ (-(21 : ℝ) / 16) = (1 + |x|) ^ (-(21 : ℝ) / 16)
      rw [abs_neg]
    rw [← hcongr, hcn]
    have hcongr2 : (∫ x in (0 : ℝ)..T, f x) = ∫ x in (0 : ℝ)..T, (1 + x) ^ (-(21 : ℝ) / 16) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hT] at hx
      show (1 + |x|) ^ (-(21 : ℝ) / 16) = (1 + x) ^ (-(21 : ℝ) / 16)
      rw [abs_of_nonneg hx.1]
    rw [hcongr2]
    simpa using intervalIntegral.integral_comp_add_left
      (f := fun u : ℝ => u ^ (-(21 : ℝ) / 16)) (d := 1) (a := (0 : ℝ)) (b := T)
  have hright : (∫ x in (0 : ℝ)..T, f x) = ∫ x in (1 : ℝ)..(1 + T), x ^ (-(21 : ℝ) / 16) := by
    have hcongr2 : (∫ x in (0 : ℝ)..T, f x) = ∫ x in (0 : ℝ)..T, (1 + x) ^ (-(21 : ℝ) / 16) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hT] at hx
      show (1 + |x|) ^ (-(21 : ℝ) / 16) = (1 + x) ^ (-(21 : ℝ) / 16)
      rw [abs_of_nonneg hx.1]
    rw [hcongr2]
    simpa using intervalIntegral.integral_comp_add_left
      (f := fun u : ℝ => u ^ (-(21 : ℝ) / 16)) (d := 1) (a := (0 : ℝ)) (b := T)
  linarith [hsplit, hleft, hright, hhalf]

/-- The vertical-error term of `contour_errors_bound`. -/
theorem contour_vertical_edge :
    ∃ KV : ℝ, 0 < KV ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
      (hprim : ψ.IsPrimitive) {β x T : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x)
      (hT : 1 ≤ T),
      ‖(1 / (2 * Real.pi)) * (∫ y in (-T)..T,
          triFun ψ β x (((5 / 8 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        ≤ KV * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) := by
  obtain ⟨CZ, hCZpos, hCZ⟩ := zeta_line_58
  obtain ⟨CL, hCLpos, hCL⟩ := LFunction_eighth_line
  refine ⟨(1 / (2 * Real.pi)) * (CZ * CL * (256 / 5)) * (42 / 5) + 1, by positivity, ?_⟩
  intro N _inst ψ hψ hprim β x T hβ hβ1 hx hT
  have hpt : ∀ y ∈ Set.Ioc (-T) T,
      ‖triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
            * (1 + |y|) ^ (-(21 : ℝ) / 16) := by
    intro y _
    have hLy : ‖DirichletCharacter.LFunction ψ ((((5 : ℝ) / 8 : ℝ)) + (y : ℂ) * Complex.I)‖
        ≤ CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |y|) ^ ((1 : ℝ) / 4) := by
      have h := hCL N ψ hψ hprim y
      simpa only [c58_conv] using h
    exact norm_triFun_vertical ψ (le_of_lt hCZpos) (le_of_lt hCLpos) (hCZ y) hLy hβ hβ1 hx
  have hcont : Continuous (fun y : ℝ => (1 + |y|) ^ (-(21 : ℝ) / 16)) :=
    (continuous_const.add continuous_abs).rpow_const
      (fun z => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + |z|)))
  have hmajInt : IntervalIntegrable
      (fun y : ℝ => (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
        * (1 + |y|) ^ (-(21 : ℝ) / 16)) volume (-T) T :=
    (continuous_const.mul hcont).intervalIntegrable _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun y : ℝ => triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I))
    (g := fun y : ℝ => (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
        * (1 + |y|) ^ (-(21 : ℝ) / 16))
    (by linarith : -T ≤ T) (Filter.Eventually.of_forall (fun t ht => hpt t ht)) hmajInt
  have hCnneg : (0 : ℝ) ≤ (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCZpos) (le_of_lt hCLpos)) (by norm_num))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (le_of_lt hx) _))
  have hval : (∫ y in (-T)..T,
        (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * (1 + |y|) ^ (-(21 : ℝ) / 16))
      ≤ (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
          * (42 / 5) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_one_add_abs_rpow_neg T (le_trans zero_le_one hT)) hCnneg
  have hfac : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖(∫ y in (-T)..T, triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ (CZ * CL * (256 / 5)) * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) * (42 / 5) :=
    le_trans hnorm hval
  have h2 : ‖(1 / (2 * (Real.pi : ℂ))) * (∫ y in (-T)..T,
        triFun ψ β x ((((5 / 8 - β : ℝ)) : ℂ) + (y : ℂ) * Complex.I))‖
      ≤ (1 / (2 * Real.pi)) * ((CZ * CL * (256 / 5))
          * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) * (42 / 5)) := by
    rw [norm_mul, hfac]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans ?_
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (le_of_lt hx) _)
  calc (1 / (2 * Real.pi)) * ((CZ * CL * (256 / 5))
        * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) * (42 / 5))
      = ((1 / (2 * Real.pi)) * (CZ * CL * (256 / 5)) * (42 / 5))
          * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) := by ring
    _ ≤ ((1 / (2 * Real.pi)) * (CZ * CL * (256 / 5)) * (42 / 5) + 1)
          * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        linarith

/-- **The requested lemma**: combining the two edge estimates with the arithmetic assembly. -/
theorem contour_errors_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
      (hprim : ψ.IsPrimitive) {β x T : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (hT : 1 ≤ T),
      ‖(1 / (2 * Real.pi)) * (∫ y in (-T)..T,
          Work.LinnikAreas.triFun ψ β x (((5 / 8 - β : ℝ)) + (y : ℂ) * Complex.I))‖
        + ‖(1 / (2 * Real.pi * Complex.I)) *
            ((∫ u in ((5 / 8 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
              - (∫ u in ((5 / 8 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I)))‖
        ≤ K * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))
                + (N : ℝ) * x * (1 + T) ^ ((23 : ℝ) / 16) / T ^ 2) := by
  obtain ⟨CZ, hCZpos, hCZ⟩ := zeta_strip_uniform
  obtain ⟨CL, hCLpos, hCL⟩ := LFunction_quarter_strip
  have hLlog : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 → ∀ z : ℂ, 1 ≤ z.re →
      ‖DirichletCharacter.LFunction ψ z‖
        ≤ Real.log (2 * N) + Real.log (2 + |z.im|) + 6 := by
    intro N _inst ψ hψ z hz
    exact LFunction_log_bound ψ hψ z hz
  obtain ⟨KH, hKHpos, hH⟩ := contour_horizontal_edge CZ CL hCZpos hCLpos hCZ hCL hLlog
  obtain ⟨KV, hKVpos, hV⟩ := contour_vertical_edge
  obtain ⟨K, hKpos, hK⟩ := contour_assembly_arith KV KH hKVpos hKHpos
  refine ⟨K, hKpos, ?_⟩
  intro N _inst ψ hψ hprim β x T hβ hβ1 hx hT
  have h1 := hV ψ hψ hprim hβ hβ1 hx hT
  have h2 := hH ψ hψ hprim hβ hβ1 hx hT
  exact (add_le_add h1 h2).trans (hK hβ hβ1 hx hT)

end

end Work.LinnikAreas
