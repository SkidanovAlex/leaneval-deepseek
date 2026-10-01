import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.lamRealNonneg
import Submission.Work.LinnikAreas.LFunctionImprimitiveZero
import Submission.Work.LinnikAreas.efunBound
import Submission.Work.LinnikAreas.lamAbelIntegral
import Submission.Work.LinnikAreas.efunContinuation
import Submission.Work.LinnikAreas.smoothedMainError
import Submission.Work.LinnikAreas.smoothedBounds
import Submission.Work.LinnikAreas.LFunctionOneBound
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one

/-!
# BGTZ Lemma 2.8 (`RatioLone`)

For a real quadratic Dirichlet character `χ₁` modulo `q > 400000` with a real zero `β₁` of
`L(s,χ₁)` in the "Siegel range" `1 - 1/(10 log q) < β₁ < 1`, the value `L(1,χ₁)` is comparable
to `1 - β₁`, up to a factor `(log q)²`:

`c (1-β₁) ≤ ‖L(1,χ₁)‖ ≤ C (log q)² (1-β₁)`

for absolute constants `c, C > 0`.  This is Lemma 2.8 of Benli–Goel–Twiss–Zaman, "Explicit
Deuring–Heilbronn phenomenon for Dirichlet L-functions" (arXiv:2410.06082), stated there with
`0.72` and `0.18`.

## Route

The proof is the classical Hecke/Friedlander–Iwaniec argument for the ratio `L(1,χ)/(1-β)`:

* `λ(n) = Σ_{d|n} χ₁(d) ≥ 0` are the coefficients of `ζ(s)L(s,χ₁)`;
* the triangle-weighted sum `S(x) = Σ_{n≤x} λ(n) n^{-β₁}(1-n/x)` satisfies
  `1 - 1/x ≤ S(x) ≤ x^{1-β₁}(1+log x)²` (`smoothedBounds`, elementary);
* the truncated Perron/Mellin identity `∫_1^∞ E(x)x^{-1-β₁}dx = L(1,χ₁)/(1-β₁)`
  (`efunContinuation`, valid because `β₁` is a genuine zero of `L(s,χ₁)`) together with the
  hyperbola-method bound `‖E(x)‖ ≤ C√q log(2q+2)√x` (`efunBound`) gives
  `S(x) = L(1,χ₁)x^{1-β₁}/((1-β₁)(2-β₁)) + O(√q log(2q+2) x^{1/2-β₁})`
  (`smoothedMainError`);
* choosing the comparison point `x = q^M` with `M` large enough that the error is `< 1/2`
  (the absolute constant of `efunBound` is absorbed into `M`) gives both inequalities.

This argument needs no primitivity: `λ(n) ≥ 0` holds for every real character, `E` is bounded by
`efunBound` for every non-principal character, and `zeroMult χ₁ β₁ ≠ 0` implies
`L(β₁,χ₁) = 0` for imprimitive `χ₁` as well (`LFunctionImprimitiveZero`).
-/

set_option maxHeartbeats 1000000

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

/-! ## 1. Elementary numeric input -/

/-- Arithmetic bookkeeping: for `q ≥ 1`, `log q + log 2 + 6 ≤ 20 log (2q+2)`. -/
private lemma log_q_add_log_two_add_six_le (q : ℕ) (hq : 1 ≤ q) :
    Real.log (q : ℝ) + Real.log 2 + 6 ≤ 20 * Real.log (2 * (q : ℝ) + 2) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (by omega : q ≠ 0))
  have hsplit : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hqpos)
  have hmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (q : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog4 : Real.log 4 ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2 : (1 : ℝ) < Real.log (2 * (q : ℝ) + 2) := by
    have := Real.log_two_gt_d9
    linarith
  linarith [hsplit, hmono, hlog4, hlog4', hlog2]

/-- **Explicit bound for `L(1,χ)`**: `‖L(1,χ)‖ ≤ 20 log(2q+2)` for every non-principal
character `χ` mod `q` (the explicit form of `LFunctionOneBound`). -/
private lemma LFunction_one_le_twenty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤ 20 * Real.log (2 * (q : ℝ) + 2) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlib :=
    Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ (1 : ℂ) le_rfl
  have hbound : ‖DirichletCharacter.LFunction χ (1 : ℂ)‖ ≤ Real.log (q : ℝ) + Real.log 2 + 6 := by
    simpa using hlib
  exact hbound.trans (log_q_add_log_two_add_six_le q hq)

/-- `q > 400000` forces `1 ≤ log q` (indeed `log q > 1.38`). -/
private lemma one_le_log {q : ℕ} (hq : 400000 < q) : 1 ≤ Real.log (q : ℝ) := by
  have h4 : (4 : ℝ) ≤ (q : ℝ) := by
    have : (4 : ℕ) ≤ q := by omega
    exact_mod_cast this
  have h1 : Real.log (4 : ℝ) ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) h4
  have h2 : (1 : ℝ) ≤ Real.log (4 : ℝ) := by
    have h4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4']
    linarith [Real.log_two_gt_d9]
  linarith

/-- `c √q / q = c / √q` for `q > 0`. -/
private lemma mul_sqrt_div_self {c : ℝ} {q : ℕ} (hq : 0 < (q : ℝ)) :
    c * Real.sqrt (q : ℝ) / (q : ℝ) = c / Real.sqrt (q : ℝ) := by
  rw [div_eq_div_iff hq.ne' (Real.sqrt_pos.mpr hq).ne']
  rw [show c * Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)
      = c * (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)) by ring, Real.mul_self_sqrt hq.le]

/-! ## 2. The error term at the comparison point `x = q^M`

The absolute constant of `efunBound` is absorbed into a (large) choice of `M`. -/

/-- **The error term of the Perron/Mellin formula is `< 1/2` at `x = q^M`** for a suitable
`M = M(C₁)` depending only on the constant `C₁` of the hyperbola-method bound, uniformly over
`q > 400000` and `β ∈ (1/2,1)` with `(1-β) log q ≤ 1/10`. -/
private lemma RatioLoneError (C₁ : ℝ) (hC₁ : 0 < C₁) :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (β : ℝ),
      1 / 2 < β → β < 1 → (1 - β) * Real.log (q : ℝ) ≤ 1 / 10 →
      C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          * ((((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β))
          * (β / (β - 1 / 2) + (1 - β) / (3 / 2 - β))
        + 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) / ((((q ^ M : ℕ) : ℝ)) * (2 - β))
        ≤ 1 / 2 := by
  set y : ℝ := Real.log (16 * C₁ + 1) with hydef
  set M : ℕ := 100 * (2 + Nat.ceil y) with hMdef
  have hM4 : 4 ≤ M := by rw [hMdef]; omega
  -- the size of `C₁` in terms of `M`
  have hMkey : Real.log (16 * C₁) ≤ (M : ℝ) / 100 - 2 := by
    have hpos : 0 < 16 * C₁ := by linarith
    have h1 : Real.log (16 * C₁) ≤ Real.log (16 * C₁ + 1) :=
      Real.log_le_log hpos (by linarith)
    have h2 : Real.log (16 * C₁ + 1) ≤ ((Nat.ceil y : ℕ) : ℝ) := by
      rw [hydef]; exact Nat.le_ceil y
    have h3 : ((M : ℕ) : ℝ) = 100 * (2 + ((Nat.ceil y : ℕ) : ℝ)) := by
      rw [hMdef]; push_cast; ring
    have : (0 : ℝ) ≤ ((Nat.ceil y : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨M, hM4, ?_⟩
  intro q _inst hq β hβhalf hβ1 hlam
  have hqR : (400000 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := one_le_log hq
  have hC1nn : 0 ≤ C₁ := le_of_lt hC₁
  have hsq_nn : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hlognn2 : 0 ≤ Real.log (q : ℝ) := le_trans zero_le_one hlogq1
  have hεnn : 0 ≤ 1 - β := by linarith
  have hε : 1 - β ≤ 1 / 10 := by
    have h := mul_le_mul_of_nonneg_left hlogq1 hεnn
    linarith
  have hβge : 9 / 10 ≤ β := by linarith
  -- `log (2q+2) ≤ 2 log q`
  have hlog2q : Real.log (2 * (q : ℝ) + 2) ≤ 2 * Real.log (q : ℝ) := by
    have hle : (2 * (q : ℝ) + 2) ≤ (q : ℝ) ^ 2 := by nlinarith
    have h0 : (0 : ℝ) < 2 * (q : ℝ) + 2 := by linarith
    have h := Real.log_le_log h0 hle
    rw [Real.log_pow] at h
    simpa using h
  have hlognn : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_nonneg
    linarith
  -- `log q ≤ 2 √q`
  have hlogsqrt : Real.log (q : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := by
    have hsq : (0 : ℝ) < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqpos
    have h := Real.log_le_sub_one_of_pos hsq
    rw [Real.log_sqrt hqpos.le] at h
    linarith
  -- the decaying power
  have hrpow : ((((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β)) ≤ (q : ℝ) ^ (-(2 * (M : ℝ) / 5)) := by
    have hcast : (((q ^ M : ℕ) : ℝ)) = (q : ℝ) ^ M := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (q : ℝ) M, ← Real.rpow_mul hqpos.le (M : ℝ) (1 / 2 - β)]
    apply Real.rpow_le_rpow_of_exponent_le hq1R
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith [hβge, hMnn]
  have hrpow_nn : 0 ≤ (q : ℝ) ^ (-(2 * (M : ℝ) / 5)) := Real.rpow_nonneg hqpos.le _
  have hXpow_nn : 0 ≤ (((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β) :=
    Real.rpow_nonneg (by positivity) _
  -- the ratio of the two denominators
  have hratio : β / (β - 1 / 2) + (1 - β) / (3 / 2 - β) ≤ 3 := by
    have h1 : 0 < β - 1 / 2 := by linarith
    have h2 : 0 < 3 / 2 - β := by linarith
    have hA : β / (β - 1 / 2) ≤ 5 / 2 := by
      rw [div_le_iff₀ h1]; linarith
    have hB : (1 - β) / (3 / 2 - β) ≤ 1 / 6 := by
      rw [div_le_iff₀ h2]; linarith
    linarith
  have hratio_nn : 0 ≤ β / (β - 1 / 2) + (1 - β) / (3 / 2 - β) := by
    have h1 : 0 < β - 1 / 2 := by linarith
    have h2 : 0 < 3 / 2 - β := by linarith
    exact add_nonneg (div_nonneg (by linarith) h1.le) (div_nonneg hεnn h2.le)
  -- `q · q^{-2M/5} = q^{1-2M/5} ≤ e^{1-2M/5}`
  have hqpow : (q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) = (q : ℝ) ^ (1 - 2 * (M : ℝ) / 5) := by
    calc (q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5)))
        = (q : ℝ) ^ (1 : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ ((1 : ℝ) + (-(2 * (M : ℝ) / 5))) :=
            (Real.rpow_add hqpos 1 (-(2 * (M : ℝ) / 5))).symm
      _ = (q : ℝ) ^ (1 - 2 * (M : ℝ) / 5) := by
            congr 1
  have hexp_decay : (q : ℝ) ^ (1 - 2 * (M : ℝ) / 5) ≤ Real.exp (1 - 2 * (M : ℝ) / 5) := by
    rw [Real.rpow_def_of_pos hqpos]
    apply Real.exp_le_exp.mpr
    have hexp_le : 1 - 2 * (M : ℝ) / 5 ≤ 0 := by
      have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
      linarith
    have h1 : (1 - 2 * (M : ℝ) / 5) * Real.log (q : ℝ)
        ≤ (1 - 2 * (M : ℝ) / 5) * 1 := mul_le_mul_of_nonpos_left hlogq1 hexp_le
    linarith
  -- `C₁ ≤ e^{M/100-2}/16`
  have hC1le : C₁ ≤ Real.exp ((M : ℝ) / 100 - 2) / 16 := by
    have h16 : 16 * C₁ ≤ Real.exp ((M : ℝ) / 100 - 2) :=
      (Real.log_le_iff_le_exp (by linarith : (0 : ℝ) < 16 * C₁)).mp hMkey
    linarith
  have hlog3 : Real.log 3 ≤ 1 + 0.39 * (M : ℝ) := by
    have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
    have h3 : Real.log (3 : ℝ) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    linarith
  have hexpsmall : Real.exp (-1 - 0.39 * (M : ℝ)) ≤ 1 / 3 := by
    have h1 : Real.exp (-1 - 0.39 * (M : ℝ)) ≤ Real.exp (-(Real.log 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (show (0 : ℝ) < 3 by norm_num)] at h1
    simpa using h1
  -- the two error terms are each `< 1/4`
  have hterm1 : C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
      * ((((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β))
      * (β / (β - 1 / 2) + (1 - β) / (3 / 2 - β)) ≤ 1 / 4 := by
    have hb : 0 ≤ C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
        * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC1nn hsq_nn) (by linarith)) hrpow_nn
    have hb0 : 0 ≤ C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)) :=
      mul_nonneg (mul_nonneg hC1nn hsq_nn) (by linarith)
    have hstep1 : C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
        * ((((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β))
        * (β / (β - 1 / 2) + (1 - β) / (3 / 2 - β))
        ≤ C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
          * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3 := by
      have hA : C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          ≤ C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2q (mul_nonneg hC1nn hsq_nn)
      have hB : C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          * ((((q ^ M : ℕ) : ℝ)) ^ (1 / 2 - β))
          ≤ (C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)))
            * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) :=
        mul_le_mul hA hrpow hXpow_nn hb0
      exact mul_le_mul hB hratio hratio_nn hb
    have hstep2 : C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
          * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3
        ≤ 12 * C₁ * Real.exp (1 - 2 * (M : ℝ) / 5) := by
      have hsqrt2 : Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)) ≤ 4 * (q : ℝ) := by
        have h1 : 2 * Real.log (q : ℝ) ≤ 2 * (2 * Real.sqrt (q : ℝ)) := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 hsq_nn
        calc Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
            ≤ Real.sqrt (q : ℝ) * (2 * (2 * Real.sqrt (q : ℝ))) := h2
          _ = 4 * (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)) := by ring
          _ = 4 * (q : ℝ) := by rw [Real.mul_self_sqrt hqpos.le]
      have h3 : 4 * (q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3
          = 12 * (q : ℝ) ^ (1 - 2 * (M : ℝ) / 5) := by
        rw [show 4 * (q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3
            = 12 * ((q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5)))) by ring, hqpow]
      calc C₁ * Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
            * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3
          = C₁ * (Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ))
            * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3) := by ring
        _ ≤ C₁ * (4 * (q : ℝ) * ((q : ℝ) ^ (-(2 * (M : ℝ) / 5))) * 3) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqrt2 hrpow_nn) (by norm_num))
                hC1nn
        _ = C₁ * (12 * (q : ℝ) ^ (1 - 2 * (M : ℝ) / 5)) := by rw [h3]
        _ ≤ C₁ * (12 * Real.exp (1 - 2 * (M : ℝ) / 5)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_decay (by norm_num)) hC1nn
        _ = 12 * C₁ * Real.exp (1 - 2 * (M : ℝ) / 5) := by ring
    have hsmall : 12 * C₁ * Real.exp (1 - 2 * (M : ℝ) / 5) ≤ 1 / 4 := by
      have h1 : 12 * C₁ * Real.exp (1 - 2 * (M : ℝ) / 5)
          ≤ 12 * (Real.exp ((M : ℝ) / 100 - 2) / 16)
            * Real.exp (1 - 2 * (M : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1le (by norm_num))
          (Real.exp_nonneg _)
      have h2 : 12 * (Real.exp ((M : ℝ) / 100 - 2) / 16)
            * Real.exp (1 - 2 * (M : ℝ) / 5)
          = (3 / 4) * Real.exp (-1 - 0.39 * (M : ℝ)) := by
        have harg : (M : ℝ) / 100 - 2 + (1 - 2 * (M : ℝ) / 5) = -1 - 0.39 * (M : ℝ) := by ring
        calc 12 * (Real.exp ((M : ℝ) / 100 - 2) / 16) * Real.exp (1 - 2 * (M : ℝ) / 5)
            = (3 / 4) * (Real.exp ((M : ℝ) / 100 - 2)
                * Real.exp (1 - 2 * (M : ℝ) / 5)) := by ring
          _ = (3 / 4) * Real.exp ((M : ℝ) / 100 - 2 + (1 - 2 * (M : ℝ) / 5)) := by
                rw [Real.exp_add]
          _ = (3 / 4) * Real.exp (-1 - 0.39 * (M : ℝ)) := by rw [harg]
      have h3 : (3 / 4 : ℝ) * Real.exp (-1 - 0.39 * (M : ℝ)) ≤ (3 / 4) * (1 / 3) :=
        mul_le_mul_of_nonneg_left hexpsmall (by norm_num)
      linarith [h1, h2, h3]
    exact le_trans (le_trans hstep1 hstep2) hsmall
  have hterm2 : 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β)
      / ((((q ^ M : ℕ) : ℝ)) * (2 - β)) ≤ 1 / 4 := by
    have hqM_ge : (q : ℝ) ≤ ((q ^ M : ℕ) : ℝ) := by
      have hcast : (((q ^ M : ℕ) : ℝ)) = (q : ℝ) ^ M := by push_cast; ring
      rw [hcast]
      calc (q : ℝ) = (q : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (q : ℝ) ^ M := pow_le_pow_right₀ hq1R (by omega)
    have hXpos : (0 : ℝ) < ((q ^ M : ℕ) : ℝ) := by linarith
    have hq32 : (32 : ℝ) ≤ Real.sqrt (q : ℝ) := by
      have h1024 : (1024 : ℝ) ≤ (q : ℝ) := by
        have : (1024 : ℕ) ≤ q := by omega
        exact_mod_cast this
      calc (32 : ℝ) = Real.sqrt 1024 := by
            rw [show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt h1024
    have hnum_nn : 0 ≤ 20 * Real.log (2 * (q : ℝ) + 2) := mul_nonneg (by norm_num) hlognn
    have hnum_nn' : 0 ≤ 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) :=
      mul_nonneg hnum_nn hεnn
    have hstepA : 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β)
        / ((((q ^ M : ℕ) : ℝ)) * (2 - β))
        ≤ 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) / (((q ^ M : ℕ) : ℝ)) := by
      refine div_le_div_of_nonneg_left hnum_nn' hXpos ?_
      nlinarith [hXpos, hβ1]
    have hstepB : 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) / (((q ^ M : ℕ) : ℝ))
        ≤ 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) / (q : ℝ) := by
      exact div_le_div_of_nonneg_left hnum_nn' hqpos hqM_ge
    have hstepC : 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β) / (q : ℝ)
        ≤ 2 * Real.log (2 * (q : ℝ) + 2) / (q : ℝ) := by
      have hnumle : 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β)
          ≤ 20 * Real.log (2 * (q : ℝ) + 2) * (1 / 10) := by nlinarith [hε, hlognn]
      have h1 := div_le_div_of_nonneg_right hnumle hqpos.le
      rw [show 20 * Real.log (2 * (q : ℝ) + 2) * (1 / 10)
          = 2 * Real.log (2 * (q : ℝ) + 2) by ring] at h1
      exact h1
    have hstepD : 2 * Real.log (2 * (q : ℝ) + 2) / (q : ℝ)
        ≤ 4 * Real.log (q : ℝ) / (q : ℝ) := by
      apply div_le_div_of_nonneg_right _ hqpos.le
      linarith [hlog2q]
    have hstepE : 4 * Real.log (q : ℝ) / (q : ℝ) ≤ 8 / Real.sqrt (q : ℝ) := by
      have h4 : 4 * Real.log (q : ℝ) ≤ 4 * (2 * Real.sqrt (q : ℝ)) := by linarith [hlogsqrt]
      have h5 := div_le_div_of_nonneg_right h4 hqpos.le
      rw [show (4 : ℝ) * (2 * Real.sqrt (q : ℝ)) = 8 * Real.sqrt (q : ℝ) by ring] at h5
      rw [mul_sqrt_div_self (c := 8) hqpos] at h5
      exact h5
    have hstepF : 8 / Real.sqrt (q : ℝ) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (q : ℝ))]
      linarith [hq32]
    exact le_trans (le_trans (le_trans (le_trans (le_trans hstepA hstepB) hstepC) hstepD)
      hstepE) hstepF
  linarith [hterm1, hterm2]

/-! ## 3. The two-sided conclusion from the smoothed-sum bounds -/

/-- The norm of the main term `L(1,χ)·x^{1-β}/((1-β)(2-β))` factors as the norm of `L(1,χ)`
times the positive real number `x^{1-β}/((1-β)(2-β))`. -/
private lemma mainTerm_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {β x : ℝ}
    (hx : 0 < x) (hβ : β < 1) :
    ‖Work.LinnikAreas.mainTerm χ β x‖
      = ‖DirichletCharacter.LFunction χ 1‖ * (x ^ (1 - β) / ((1 - β) * (2 - β))) := by
  have hb1 : (0 : ℝ) ≤ 1 - β := by linarith
  have hb2 : (0 : ℝ) ≤ 2 - β := by linarith
  rw [Work.LinnikAreas.mainTerm_apply, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_re, norm_mul]
  have h1n : ‖(((1 - β : ℝ)) : ℂ)‖ = 1 - β := by
    rw [Complex.norm_def, Complex.normSq_ofReal, show (1 - β) * (1 - β) = (1 - β) ^ 2 by ring,
        Real.sqrt_sq hb1]
  have h2n : ‖(((2 - β : ℝ)) : ℂ)‖ = 2 - β := by
    rw [Complex.norm_def, Complex.normSq_ofReal, show (2 - β) * (2 - β) = (2 - β) ^ 2 by ring,
        Real.sqrt_sq hb2]
  rw [h1n, h2n]
  ring

/-- **From the smoothed sum to the two-sided bound for `L(1,χ)`.**  If
`S = Ssm χ β X` satisfies `1 - 1/X ≤ S ≤ X^{1-β}(1+log X)²` and is within `1/2` of the main term,
and if `X^{1-β} ≤ e^T`, then `e^{-T}(1-β)/4 ≤ ‖L(1,χ)‖ ≤ (2L2+1)(1-β)` whenever
`(1+log X)² ≤ L2`. -/
private lemma RatioLoneTwoSided {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {β X T L2 : ℝ}
    (hX1 : 1 ≤ X) (hX4 : 4 ≤ X) (hβhalf : 1 / 2 < β) (hβ1 : β < 1)
    (hXexp : X ^ (1 - β) ≤ Real.exp T)
    (hlog : (1 + Real.log X) ^ 2 ≤ L2)
    (hSlo : 1 - 1 / X ≤ Work.LinnikAreas.Ssm χ β X)
    (hShi : Work.LinnikAreas.Ssm χ β X ≤ X ^ (1 - β) * (1 + Real.log X) ^ 2)
    (herr : ‖((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ) - Work.LinnikAreas.mainTerm χ β X‖ ≤ 1 / 2) :
    Real.exp (-T) / 4 * (1 - β) ≤ ‖DirichletCharacter.LFunction χ 1‖ ∧
      ‖DirichletCharacter.LFunction χ 1‖ ≤ (2 * L2 + 1) * (1 - β) := by
  have hXpos : 0 < X := by linarith
  have hb1pos : 0 < 1 - β := by linarith
  have hb1nn : 0 ≤ 1 - β := le_of_lt hb1pos
  have hb2pos : 0 < 2 - β := by linarith
  have hb2one : 1 ≤ 2 - β := by linarith
  have hDpos : 0 < (1 - β) * (2 - β) := mul_pos hb1pos hb2pos
  have hD0 : (1 - β) * (2 - β) ≠ 0 := ne_of_gt hDpos
  have hXp_pos : 0 < X ^ (1 - β) := Real.rpow_pos_of_pos hXpos _
  have hXp_one : 1 ≤ X ^ (1 - β) := Real.one_le_rpow hX1 hb1nn
  have hL2nn : 0 ≤ L2 := le_trans (sq_nonneg _) hlog
  have hSnn : 0 ≤ Work.LinnikAreas.Ssm χ β X := by
    have h : (0 : ℝ) ≤ 1 - 1 / X := by
      rw [sub_nonneg, div_le_one hXpos]
      exact hX1
    linarith
  have hnormS : ‖((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ)‖ = Work.LinnikAreas.Ssm χ β X := by
    rw [Complex.norm_def, Complex.normSq_ofReal,
      show Work.LinnikAreas.Ssm χ β X * Work.LinnikAreas.Ssm χ β X
        = (Work.LinnikAreas.Ssm χ β X) ^ 2 by ring, Real.sqrt_sq hSnn]
  have hnormM := mainTerm_norm χ hXpos hβ1
  have hMub : ‖Work.LinnikAreas.mainTerm χ β X‖ ≤ Work.LinnikAreas.Ssm χ β X + 1 / 2 := by
    have h := norm_add_le
      (Work.LinnikAreas.mainTerm χ β X - ((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ))
      ((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ)
    have he : (Work.LinnikAreas.mainTerm χ β X - ((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ))
        + ((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ) = Work.LinnikAreas.mainTerm χ β X := by ring
    rw [he, norm_sub_rev, hnormS] at h
    linarith
  have hMlb : Work.LinnikAreas.Ssm χ β X - 1 / 2 ≤ ‖Work.LinnikAreas.mainTerm χ β X‖ := by
    have h := abs_norm_sub_norm_le ((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ)
      (Work.LinnikAreas.mainTerm χ β X)
    rw [hnormS] at h
    have h1 : Work.LinnikAreas.Ssm χ β X - ‖Work.LinnikAreas.mainTerm χ β X‖
        ≤ ‖((Work.LinnikAreas.Ssm χ β X : ℝ) : ℂ) - Work.LinnikAreas.mainTerm χ β X‖ :=
      le_trans (le_abs_self _) h
    linarith
  have hkey : ‖DirichletCharacter.LFunction χ 1‖ * X ^ (1 - β)
      = ‖Work.LinnikAreas.mainTerm χ β X‖ * ((1 - β) * (2 - β)) := by
    rw [hnormM, mul_assoc, div_mul_cancel₀ _ hD0]
  have hexp_le : Real.exp (-T) ≤ 1 / X ^ (1 - β) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos T) hXp_pos).mpr hXexp
  constructor
  · -- lower bound
    have hSge : (3 : ℝ) / 4 ≤ Work.LinnikAreas.Ssm χ β X := by
      have h1X : 1 / X ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hX4
      linarith
    have hMge : (1 : ℝ) / 4 ≤ ‖Work.LinnikAreas.mainTerm χ β X‖ := by linarith
    have h2 : (1 / 4) * ((1 - β) * (2 - β)) ≤ ‖DirichletCharacter.LFunction χ 1‖ * X ^ (1 - β) := by
      rw [hkey]
      exact mul_le_mul_of_nonneg_right hMge hDpos.le
    have h3 : (1 / 4) * ((1 - β) * (2 - β)) / X ^ (1 - β) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
      rw [div_le_iff₀ hXp_pos]
      exact h2
    have h4 : Real.exp (-T) * (1 - β) ≤ ((1 - β) * (2 - β)) / X ^ (1 - β) := by
      have hb2' : (1 - β) ≤ (1 - β) * (2 - β) := by nlinarith [hb1nn, hb2pos]
      calc Real.exp (-T) * (1 - β)
          ≤ (1 / X ^ (1 - β)) * (1 - β) := mul_le_mul_of_nonneg_right hexp_le hb1nn
        _ = (1 - β) * (X ^ (1 - β))⁻¹ := by rw [one_div]; ring
        _ ≤ ((1 - β) * (2 - β)) * (X ^ (1 - β))⁻¹ :=
              mul_le_mul_of_nonneg_right hb2' (by positivity)
        _ = (1 - β) * (2 - β) / X ^ (1 - β) := by rw [div_eq_mul_inv]
    have h5 : Real.exp (-T) / 4 * (1 - β) = Real.exp (-T) * (1 - β) / 4 := by ring
    rw [h5]
    have h6 : Real.exp (-T) * (1 - β) / 4 ≤ ((1 - β) * (2 - β)) / X ^ (1 - β) / 4 :=
      div_le_div_of_nonneg_right h4 (by norm_num)
    have h7 : ((1 - β) * (2 - β)) / X ^ (1 - β) / 4
        = (1 / 4) * ((1 - β) * (2 - β)) / X ^ (1 - β) := by ring
    rw [h7] at h6
    exact h6.trans h3
  · -- upper bound
    have h1 : ‖DirichletCharacter.LFunction χ 1‖ * X ^ (1 - β)
        ≤ (X ^ (1 - β) * (1 + Real.log X) ^ 2 + 1 / 2) * ((1 - β) * (2 - β)) := by
      rw [hkey]
      have h := le_trans hMub (by linarith [hShi] :
        Work.LinnikAreas.Ssm χ β X + 1 / 2
          ≤ X ^ (1 - β) * (1 + Real.log X) ^ 2 + 1 / 2)
      exact mul_le_mul_of_nonneg_right h hDpos.le
    have h2 : ‖DirichletCharacter.LFunction χ 1‖
        ≤ (X ^ (1 - β) * (1 + Real.log X) ^ 2 + 1 / 2) * ((1 - β) * (2 - β))
          / X ^ (1 - β) := by
      rw [le_div_iff₀ hXp_pos]
      exact h1
    refine h2.trans ?_
    have h3 : (X ^ (1 - β) * (1 + Real.log X) ^ 2 + 1 / 2) * ((1 - β) * (2 - β)) / X ^ (1 - β)
        = (1 + Real.log X) ^ 2 * ((1 - β) * (2 - β))
          + ((1 - β) * (2 - β)) / (2 * X ^ (1 - β)) := by
      field_simp
    rw [h3]
    have h4 : (1 + Real.log X) ^ 2 * ((1 - β) * (2 - β)) ≤ L2 * (2 * (1 - β)) := by
      calc (1 + Real.log X) ^ 2 * ((1 - β) * (2 - β))
          ≤ L2 * ((1 - β) * 2) := by
            apply mul_le_mul
            · exact hlog
            · exact mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) - β ≤ 2) hb1nn
            · positivity
            · exact hL2nn
        _ = L2 * (2 * (1 - β)) := by ring
    have h5 : ((1 - β) * (2 - β)) / (2 * X ^ (1 - β)) ≤ (1 - β) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * X ^ (1 - β))]
      have hb2' : (1 - β) ≤ (1 - β) * (2 - β) := by nlinarith [hb1nn, hb2pos]
      have h' : (1 - β) * (2 - β) ≤ (1 - β) * 2 := mul_le_mul_of_nonneg_left (by linarith) hb1nn
      have h'' : (1 - β) * 2 ≤ (1 - β) * (2 * X ^ (1 - β)) := by nlinarith [hb1nn, hXp_one]
      linarith
    linarith [h4, h5]

/-! ## 4. BGTZ Lemma 2.8 -/

/-- **BGTZ Lemma 2.8** (arXiv:2410.06082): for a real quadratic character `χ₁` mod `q > 400000`
with a real zero `β₁ ∈ (1 - 1/(10 log q), 1)` of `L(s,χ₁)`, the value `L(1,χ₁)` is comparable to
`1 - β₁` up to `(log q)²`. -/
theorem RatioLone :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
      χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      1 - 1 / (10 * Real.log q) < β₁ →
      c * (1 - β₁) ≤ ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ ∧
        ‖DirichletCharacter.LFunction χ₁ (1 : ℂ)‖ ≤ C * (Real.log q) ^ 2 * (1 - β₁) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.LinnikAreas.efunBound
  set C₁' : ℝ := max C₁ 1 with hC₁'def
  have hC₁'pos : 0 < C₁' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₁'ge : C₁ ≤ C₁' := le_max_left _ _
  obtain ⟨M, hM4, hMerr⟩ := RatioLoneError C₁' hC₁'pos
  refine ⟨Real.exp (-((M : ℝ) / 10)) / 4, 2 * ((M : ℝ) + 1) ^ 2 + 1,
    by positivity, by positivity, ?_⟩
  intro q _inst hq χ₁ hχsq hχne β₁ hβ1 hzm hβhyp
  have hqR : (400000 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := one_le_log hq
  have hlogqpos : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hlogq1
  -- the Siegel-range hypothesis, quantitatively
  have hlam_lt : (1 - β₁) * Real.log (q : ℝ) < 1 / 10 := by
    have h1 : 1 - β₁ < 1 / (10 * Real.log (q : ℝ)) := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 hlogqpos
    have h3 : (1 / (10 * Real.log (q : ℝ))) * Real.log (q : ℝ) = 1 / 10 := by
      field_simp
    linarith [h2, h3.le]
  have hlam_le : (1 - β₁) * Real.log (q : ℝ) ≤ 1 / 10 := le_of_lt hlam_lt
  have hεnn : 0 ≤ 1 - β₁ := by linarith
  have hε : 1 - β₁ ≤ 1 / 10 := by
    have h := mul_le_mul_of_nonneg_left hlogq1 hεnn
    linarith
  have hβhalf : 1 / 2 < β₁ := by linarith
  have hβpos : 0 < β₁ := by linarith
  -- `β₁` is a genuine zero of `L(s,χ₁)`
  have hL0 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 :=
    Work.LinnikAreas.LFunctionImprimitiveZero χ₁ hχne (by simpa using hβpos)
      (by simpa using hβ1) hzm
  -- the hyperbola-method bound for `E(x)`
  set K : ℝ := C₁' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg hC₁'pos.le (Real.sqrt_nonneg _))
      (Real.log_nonneg (by linarith))
  have hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ₁ x‖ ≤ K * Real.sqrt x := by
    intro x hx
    have h₁ := hC₁ q χ₁ hχne x hx
    have hle : C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
        ≤ C₁' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
      have hsq : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
      have hlog : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
        apply Real.log_nonneg
        linarith
      calc C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          = C₁ * (Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) := by ring
        _ ≤ C₁' * (Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_right hC₁'ge (mul_nonneg hsq hlog)
        _ = C₁' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by ring
    calc ‖Work.LinnikAreas.Efun χ₁ x‖
        ≤ C₁ * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x := h₁
      _ ≤ C₁' * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg x)
      _ = K * Real.sqrt x := by rw [hKdef]
  -- the Mellin identity `∫ E(x) x^{-1-β₁} dx = L(1,χ₁)/(1-β₁)`
  have hfac : (∫ x in Set.Ioi (1 : ℝ),
        Work.LinnikAreas.Efun χ₁ x * (x : ℂ) ^ (-(((1 + β₁ : ℝ)) : ℂ)))
      = DirichletCharacter.LFunction χ₁ 1 / (1 - ↑β₁) :=
    Work.LinnikAreas.efunContinuation χ₁ hχne hE
      (fun s hs => Work.LinnikAreas.lamAbelIntegral χ₁ hχne hE hs) hβhalf hβ1 hL0
  have hχre : ∀ n : ℕ, (Work.LinnikAreas.lam χ₁ n).im = 0 :=
    (Work.LinnikAreas.lamRealNonneg χ₁ hχsq).1
  have hpow1 : 1 ≤ q ^ M := by
    have := pow_pos (by omega : 0 < q) M
    omega
  have herr0 := Work.LinnikAreas.smoothedMainError χ₁ hχre hKnn hE hβhalf hβ1 hfac
    (x := q ^ M) hpow1
  -- the numeric error bound
  have hnum := hMerr q hq β₁ hβhalf hβ1 hlam_le
  have hR := LFunction_one_le_twenty χ₁ hχne
  have hfrac : ‖DirichletCharacter.LFunction χ₁ 1‖ * (1 - β₁)
        / ((((q ^ M : ℕ) : ℝ)) * (2 - β₁))
      ≤ 20 * Real.log (2 * (q : ℝ) + 2) * (1 - β₁)
        / ((((q ^ M : ℕ) : ℝ)) * (2 - β₁)) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right hR hεnn
    · exact mul_nonneg (by positivity) (by linarith)
  have herr2 : ‖((Work.LinnikAreas.Ssm χ₁ β₁ (((q ^ M : ℕ) : ℝ)) : ℝ) : ℂ)
      - Work.LinnikAreas.mainTerm χ₁ β₁ (((q ^ M : ℕ) : ℝ))‖ ≤ 1 / 2 := by
    refine le_trans herr0 ?_
    rw [hKdef]
    linarith [hnum, hfrac]
  -- the elementary bounds for the smoothed sum
  have hX1r : (1 : ℝ) ≤ (((q ^ M : ℕ) : ℝ)) := by
    have h := hpow1
    exact_mod_cast h
  have hbond := Work.LinnikAreas.smoothedBounds χ₁
    (Work.LinnikAreas.lamRealNonneg χ₁ hχsq).2.1
    (fun n => le_trans (Complex.re_le_norm _) ((Work.LinnikAreas.lamRealNonneg χ₁ hχsq).2.2 n))
    β₁ (le_of_lt hβ1) (x := (((q ^ M : ℕ) : ℝ))) hX1r
  -- the exponent bookkeeping
  have hXexp : ((((q ^ M : ℕ) : ℝ)) ^ (1 - β₁)) ≤ Real.exp ((M : ℝ) / 10) := by
    have hcast : (((q ^ M : ℕ) : ℝ)) = (q : ℝ) ^ M := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (q : ℝ) M, ← Real.rpow_mul hqpos.le (M : ℝ) (1 - β₁)]
    rw [Real.rpow_def_of_pos hqpos]
    apply Real.exp_le_exp.mpr
    have h1 : (M : ℝ) * ((1 - β₁) * Real.log (q : ℝ)) ≤ (M : ℝ) * (1 / 10) :=
      mul_le_mul_of_nonneg_left hlam_le (Nat.cast_nonneg M)
    nlinarith [h1]
  have hlogX : (1 + Real.log ((((q ^ M : ℕ) : ℝ)))) ^ 2
      ≤ ((M : ℝ) + 1) ^ 2 * (Real.log (q : ℝ)) ^ 2 := by
    have hcast : (((q ^ M : ℕ) : ℝ)) = (q : ℝ) ^ M := by push_cast; ring
    rw [hcast, Real.log_pow]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have h1 : 1 + (M : ℝ) * Real.log (q : ℝ) ≤ ((M : ℝ) + 1) * Real.log (q : ℝ) := by
      nlinarith [hlogq1, hMnn]
    have h0 : 0 ≤ 1 + (M : ℝ) * Real.log (q : ℝ) := by
      nlinarith [hlogq1, hMnn]
    have h2 : 0 ≤ ((M : ℝ) + 1) * Real.log (q : ℝ) :=
      mul_nonneg (by positivity) (by linarith)
    calc (1 + (M : ℝ) * Real.log (q : ℝ)) ^ 2
        ≤ (((M : ℝ) + 1) * Real.log (q : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = ((M : ℝ) + 1) ^ 2 * (Real.log (q : ℝ)) ^ 2 := by ring
  have hX4r : (4 : ℝ) ≤ (((q ^ M : ℕ) : ℝ)) := by
    have hq4R : (4 : ℝ) ≤ (q : ℝ) := by linarith
    have hcast : (((q ^ M : ℕ) : ℝ)) = (q : ℝ) ^ M := by push_cast; ring
    rw [hcast]
    calc (4 : ℝ) ≤ (q : ℝ) := hq4R
      _ = (q : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (q : ℝ) ^ M := pow_le_pow_right₀ hq1R (by omega)
  obtain ⟨hlo, hhi⟩ := RatioLoneTwoSided χ₁ hX1r hX4r hβhalf hβ1 hXexp hlogX
    hbond.1 hbond.2 herr2
  refine ⟨hlo, ?_⟩
  calc ‖DirichletCharacter.LFunction χ₁ 1‖
      ≤ (2 * (((M : ℝ) + 1) ^ 2 * (Real.log (q : ℝ)) ^ 2) + 1) * (1 - β₁) := hhi
    _ ≤ (2 * ((M : ℝ) + 1) ^ 2 + 1) * (Real.log (q : ℝ)) ^ 2 * (1 - β₁) := by
        have hLsq : 1 ≤ (Real.log (q : ℝ)) ^ 2 := by nlinarith [hlogq1]
        have h1 : 2 * (((M : ℝ) + 1) ^ 2 * (Real.log (q : ℝ)) ^ 2) + 1
            ≤ (2 * ((M : ℝ) + 1) ^ 2 + 1) * (Real.log (q : ℝ)) ^ 2 := by
          nlinarith [hLsq]
        exact mul_le_mul_of_nonneg_right h1 hεnn

end

end Work.LinnikAreas.BGTZ
