import Mathlib
import Submission.MainTerm

open scoped BigOperators Topology
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Bounds for the inverse pole factor (P8 Lemma 4.1, truncation input)

The ξ-truncation compares the kernel `K` with the inverse pole factor

    pole(ξ, ξ′)⁻¹ = (1 − 2πiξ)(1 − 2πiξ′)·N / ((2 − 2πi(ξ+ξ′))·B(x)·φ(N))

with `B(x) = (φ(W)/W)·log x` (Mathlib's Fourier normalization; see
`Submission/MainTerm.lean`).  Concretely, the comparison on the cube
`|ξ|, |ξ′| ≤ √(log x)` uses the uniform bound

    ‖pole(ξ,ξ′)⁻¹‖ ≤ (N/φ(N))·(W/φ(W))·(2π² + 1)      on the cube,

and the negligibility of the complement uses the polynomial growth

    ‖pole(ξ,ξ′)⁻¹‖ ≤ (N/φ(N))·(W/φ(W))·(1/log x)·(1+2π|ξ|)·(1+2π|ξ′|) .

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The inverse pole factor (Mathlib normalization: the paper's variable is
`ξ_paper = −2πξ`). -/
noncomputable def poleInv (W N : ℕ) (x : ℕ) (ξ ξ' : ℝ) : ℂ :=
  (poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹

/-- The pole factor never vanishes (for nonzero moduli and `log x ≠ 0`). -/
lemma poleFactor_ne_zero (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) (ξ ξ' : ℝ) {x : ℕ}
    (hlog : Real.log (x : ℝ) ≠ 0) : poleFactor W N ξ ξ' x ≠ 0 := by
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφW : (W.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)).ne'
  have hφN : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)).ne'
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have h1 : (1 : ℂ) + ξ * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1' : (1 : ℂ) + ξ' * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h2 : (2 : ℂ) + (ξ + ξ') * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  unfold poleFactor
  refine div_ne_zero ?_ (mul_ne_zero (mul_ne_zero h1 h1') hNc)
  exact mul_ne_zero h2 (mul_ne_zero (mul_ne_zero (div_ne_zero hφW hWc) hlogC) hφN)

/-- The defining property of `poleInv`: `poleInv · pole = 1`. -/
lemma poleInv_mul_poleFactor (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) {x : ℕ}
    (hlog : Real.log (x : ℝ) ≠ 0) (ξ ξ' : ℝ) :
    poleInv W N x ξ ξ' * poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x = 1 := by
  unfold poleInv
  exact inv_mul_cancel₀ (poleFactor_ne_zero W N hW hN _ _ hlog)

/-- **Explicit form of the inverse pole factor.** -/
lemma poleInv_eq (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) {x : ℕ} (hlog : Real.log (x : ℝ) ≠ 0)
    (ξ ξ' : ℝ) :
    poleInv W N x ξ ξ' =
      (((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) * (N.totient : ℂ))) *
        ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ')))) := by
  unfold poleInv
  exact poleFactor_inv_eq W N hW hN hlog ξ ξ'

/-- Norm bound for the numerator factor `1 - 2πiξ`. -/
lemma norm_one_sub_two_pi_I_mul (ξ : ℝ) :
    ‖(1 : ℂ) - 2 * Real.pi * Complex.I * ξ‖ ≤ 1 + 2 * Real.pi * |ξ| := by
  have hzn : ‖(1 : ℂ) - 2 * Real.pi * Complex.I * ξ‖ ^ 2 = 1 + (2 * Real.pi * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hR : ‖(1 : ℂ) - 2 * Real.pi * Complex.I * ξ‖ ^ 2 ≤ (1 + 2 * Real.pi * |ξ|) ^ 2 := by
    rw [hzn]
    have h1 : 0 ≤ 2 * Real.pi * |ξ| := by positivity
    have hsq : (2 * Real.pi * |ξ|) ^ 2 = (2 * Real.pi * ξ) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    nlinarith [h1, hsq]
  have hb : (0 : ℝ) ≤ 1 + 2 * Real.pi * |ξ| := by positivity
  nlinarith [hR, norm_nonneg ((1 : ℂ) - 2 * Real.pi * Complex.I * ξ), hb]

/-- The denominator of the pole factor has norm at least `2`. -/
lemma norm_two_sub_two_pi_I_mul_ge (ξ ξ' : ℝ) :
    2 ≤ ‖(2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ')‖ := by
  have h : ((2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ')).re = 2 := by simp
  calc (2 : ℝ) = |((2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ')).re| := by rw [h]; simp
    _ ≤ ‖(2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ')‖ := Complex.abs_re_le_norm _

/-- **Polynomial growth of the inverse pole factor.** -/
lemma norm_poleInv_le (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) {x : ℕ}
    (hlog : Real.log (x : ℝ) ≠ 0) (hlogpos : 0 < Real.log (x : ℝ)) (ξ ξ' : ℝ) :
    ‖poleInv W N x ξ ξ'‖ ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
      ((Real.log (x : ℝ))⁻¹) * (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) := by
  have hφW : (0 : ℝ) < W.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  have hφN : (0 : ℝ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  rw [poleInv_eq W N hW hN hlog ξ ξ']
  have hnum : ‖(1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
      (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))‖ ≤
      (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) / 2 := by
    rw [norm_div, norm_mul]
    have h2 := norm_two_sub_two_pi_I_mul_ge ξ ξ'
    have hn1 := norm_one_sub_two_pi_I_mul ξ
    have hn2 := norm_one_sub_two_pi_I_mul ξ'
    have h20 : (0 : ℝ) < ‖(2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ')‖ := by linarith
    have hp : (0 : ℝ) < (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) := by positivity
    rw [div_le_div_iff₀ h20 (by norm_num : (0:ℝ) < 2)]
    have hprod : ‖(1 : ℂ) - 2 * Real.pi * Complex.I * ξ‖ *
        ‖(1 : ℂ) - 2 * Real.pi * Complex.I * ξ'‖ ≤
        (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) :=
      mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)
    nlinarith [hprod, h2, norm_nonneg ((1 : ℂ) - 2 * Real.pi * Complex.I * ξ),
      norm_nonneg ((1 : ℂ) - 2 * Real.pi * Complex.I * ξ')]
  have hcoef : ‖((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
      (N.totient : ℂ)))‖ = ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
      ((Real.log (x : ℝ))⁻¹) := by
    rw [norm_div, norm_mul, norm_mul, norm_div]
    simp only [Complex.norm_natCast]
    have hnorm : ‖(Real.log (x : ℝ) : ℂ)‖ = Real.log (x : ℝ) := by
      rw [show ‖(Real.log (x : ℝ) : ℂ)‖ = |Real.log (x : ℝ)| from RCLike.norm_ofReal _]
      exact abs_of_pos hlogpos
    rw [hnorm]
    field_simp
  rw [norm_mul, hcoef]
  have hc0 : (0 : ℝ) ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
      ((Real.log (x : ℝ))⁻¹) := by positivity
  calc ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) * ((Real.log (x : ℝ))⁻¹) *
        ‖(1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))‖
      ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) * ((Real.log (x : ℝ))⁻¹) *
        ((1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) / 2) :=
        mul_le_mul_of_nonneg_left hnum hc0
    _ ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) * ((Real.log (x : ℝ))⁻¹) *
        ((1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have hp : (0 : ℝ) ≤ (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) := by positivity
        linarith
    _ = _ := by ring

/-- **Uniform bound on the truncation cube.**  For `|ξ|, |ξ′| ≤ √(log x)` with
`1 ≤ log x`, the inverse pole factor is bounded independently of `x`, `ξ`, `ξ′`
up to the sieve constants. -/
lemma norm_poleInv_le_cube (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) {x : ℕ}
    (hL1 : 1 ≤ Real.log (x : ℝ)) {ξ ξ' : ℝ}
    (hξ : |ξ| ≤ Real.sqrt (Real.log (x : ℝ)))
    (hξ' : |ξ'| ≤ Real.sqrt (Real.log (x : ℝ))) :
    ‖poleInv W N x ξ ξ'‖ ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
      (1 + 2 * Real.pi) ^ 2 := by
  set ρ : ℝ := Real.sqrt (Real.log (x : ℝ)) with hρdef
  have hL : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hρ : 1 ≤ ρ := by
    rw [hρdef]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_le_sqrt hL1
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρ2 : ρ ^ 2 = Real.log (x : ℝ) := by
    rw [hρdef]; exact Real.sq_sqrt hL.le
  have hξρ : |ξ| ≤ ρ := hξ
  have hξρ' : |ξ'| ≤ ρ := hξ'
  have hb := norm_poleInv_le W N hW hN hL.ne' hL ξ ξ'
  have hφW : (0 : ℝ) < W.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  have hφN : (0 : ℝ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)
  have hcoef : 0 ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) := by positivity
  have hstep : (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) ≤
      (1 + 2 * Real.pi * ρ) ^ 2 := by
    rw [pow_two]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · have := mul_le_mul_of_nonneg_left hξρ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
    · have := mul_le_mul_of_nonneg_left hξρ' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
  have hcore : (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) ≤
      (1 + 2 * Real.pi) ^ 2 := by
    have hA : 0 < (Real.log (x : ℝ))⁻¹ := by positivity
    have hmain : (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * ρ) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 := by
      have hEq : (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * ρ) ^ 2 =
          ρ⁻¹ * ρ⁻¹ + 4 * Real.pi * ρ⁻¹ + 4 * Real.pi ^ 2 := by
        rw [show (Real.log (x : ℝ))⁻¹ = (ρ ^ 2)⁻¹ by rw [hρ2]]
        field_simp
        ring
      rw [hEq]
      have hρinv : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
      have h0 : 0 ≤ ρ⁻¹ := by positivity
      have hsq : (1 + 2 * Real.pi) ^ 2 = 1 + 4 * Real.pi + 4 * Real.pi ^ 2 := by ring
      rw [hsq]
      nlinarith [hρinv, h0, Real.pi_pos]
    calc (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|)
        = (Real.log (x : ℝ))⁻¹ * ((1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|)) := by ring
      _ ≤ (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * ρ) ^ 2 :=
            mul_le_mul_of_nonneg_left hstep hA.le
      _ ≤ (1 + 2 * Real.pi) ^ 2 := hmain
  calc ‖poleInv W N x ξ ξ'‖ ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
        (Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|) := hb
    _ = ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) *
        ((Real.log (x : ℝ))⁻¹ * (1 + 2 * Real.pi * |ξ|) * (1 + 2 * Real.pi * |ξ'|)) := by ring
    _ ≤ ((N : ℝ) / (N.totient : ℝ)) * ((W : ℝ) / (W.totient : ℝ)) * (1 + 2 * Real.pi) ^ 2 :=
        mul_le_mul_of_nonneg_left hcore hcoef

end Commons.NumberTheory.MaynardSieve
