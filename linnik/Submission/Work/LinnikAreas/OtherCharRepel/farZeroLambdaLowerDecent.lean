import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.farZeroArith
import Submission.Work.LinnikAreas.OtherCharRepel.fourTermPointwise
import Submission.Work.LinnikAreas.OtherCharRepel.sharpPrimitiveOffAxis
import Submission.Work.LinnikAreas.OtherCharRepel.zetaLogDerivRegularSharp
import Submission.Work.LinnikAreas.OtherCharRepel.changeLevelSharpCorrection
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

/-!
# Far zeros of `L(·,χ*)` have `λ ≥ 1/25` (Heath-Brown 1992 / de la Vallée Poussin region)

**Target.**  For all sufficiently large `q`: for every `χ ≠ 1` mod `q` and every zero `u` of
`L(·, χ*)` (where `χ* = χ.primitiveCharacter`, i.e. `zeroMult χ u ≠ 0`) with `1 ≤ |Im u| ≤ 4`,

`λ(u) = (1 - Re u) · log q ≥ 1/25`.

**Route.**  Write `ε = 1 - Re u`, `γ = Im u`.  The classical de la Vallée Poussin argument is
run with the *sharp* cosine polynomial
`Q(θ) = 5/4 + 2 cos θ + cos 2θ + (1/4) cos 3θ = (1 + cos θ)(cos θ + 1/2)² ≥ 0`
(`cosPolyDecent`), whose pointwise positivity is `fourTermPointwise`:

`0 ≤ (5/4)(-Re ζ'/ζ)(σ) + 2(-Re L'/L)(σ+iγ,χ) + (-Re L'/L)(σ+2iγ,χ²) + (1/4)(-Re L'/L)(σ+3iγ,χ³)`.

Assuming `ε log q < 1/25` we evaluate this at `σ = 1 + δ` with `δ = √(5/4)·ε/(√2 - √(5/4))`, the
maximiser of `δ' ↦ 2/(δ'+ε) - (5/4)/δ'` (`farZeroArith.keyArith`), whose maximum is
`(√2 - √(5/4))²/ε = (13/4 - √10)/ε`.  The four terms are bounded by

* `-Re ζ'/ζ(1+δ) ≤ 1/δ + Cζ` — `zeta_logDeriv_re_axis_bound`;
* `-Re L'/L(1+δ+iγ, χ) ≤ -1/(δ+ε) + (1/2) log q + C(1+loglog q)` — the pole clause of the
  level-`q` sharp bound (here `|γ| ≤ 4 ≤ 12`);
* `-Re L'/L(1+δ+2iγ, χ²) ≤ (1/2) log q + C(1+loglog q)` and the same for `χ³` (here
  `|2γ| ≥ 2`, `|3γ| ≥ 3`, so the `1 ≤ |τ|` clause applies even when `χ²` or `χ³` is principal).

This gives `2/(δ+ε) - (5/4)/δ ≤ (13/8) log q + (13/4) C(1+loglog q) + (5/4) Cζ`, and for
`q ≥ q₀` the correction terms are `≤ (13/128) log q`; `keyArith` converts the left side into
`(13/4 - √10)/ε`, so `ε log q ≥ (13/4 - √10)·128/221 ≥ 1/25` (`farZeroArith.numBound`).

**The level-`q` sharp bounds.**  `sharpPrimitiveOffAxis` gives `-Re L'/L(·,ψ) ≤ (1/2) log N + C`
for a *primitive* `ψ` mod `N` (the crux: the optimal constant `1/2`, from the symmetric Hadamard
partial fraction).  `changeLevelSharpCorrection` (this directory) raises the level from the
conductor `N = χ.conductor` to `q` without destroying that constant: the Euler factors at the
primes `p ∣ q` contribute at most `(1/2)(log q - log N) + log 2`.  The principal character is
handled by the sharp zeta bound (`zetaLogDerivRegularSharp`).  See `sharpLevelOffAxisLevel`
below.
-/


set_option maxHeartbeats 800000

/-! ## Helper facts about `zeroMult`-zeros

They avoid depending on any unproved level-change estimate: the only imprimitivity
ingredient used is `changeLevelSharpCorrection` (proved in this directory), which preserves
the sharp constant `1/2` of `log q`. -/

/-- The primitive character inducing a non-principal character is non-principal. -/
private lemma prim_ne_one_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  exact h (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1,
    DirichletCharacter.changeLevel_one χ.conductor_dvd_level])

/-- A `zeroMult`-zero lies in the open critical strip. -/
private lemma zeroMult_strip {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {u : ℂ} (hz : Work.LinnikContract.zeroMult χ u ≠ 0) :
    0 < u.re ∧ u.re < 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 := prim_ne_one_of_ne_one hχ
  have hcz : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hz)
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψne
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hcz

/-- A `zeroMult`-zero is an ordinary zero of the `L`-function of the inducing primitive
character. -/
private lemma LFunction_prim_eq_zero_of_zeroMult {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {u : ℂ}
    (hz : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter u = 0 := by
  have hψne : χ.primitiveCharacter ≠ 1 := prim_ne_one_of_ne_one hχ
  have hstrip := zeroMult_strip χ hχ hz
  have hlt : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u
      ≠ 0 := by simpa only [Work.LinnikContract.zeroMult] using hz
  have horder :=
    Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
      χ.primitiveCharacter hψne hstrip.1 hstrip.2
  have hL : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
    rw [horder]; exact hlt
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hL

/-! ## The sharp off-axis bounds at the level `q` -/

/-- The level-`q` sharp bounds, obtained from the *primitive* sharp bound
`sharpPrimitiveOffAxis` and the imprimitivity correction `changeLevelSharpCorrection`. -/
private theorem sharpLevelOffAxisLevel : ∃ q₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q),
    (χ ≠ 1 → ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → |τ| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ)))) ∧
    (∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| → |τ| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ)))) ∧
    (χ ≠ 1 → ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 → |u.im| ≤ 12 →
        (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (u.im : ℂ) * Complex.I)).re ≤
          -1 / (σ - u.re) + (1 / 2) * Real.log (q : ℝ)
            + C * (1 + Real.log (Real.log (q : ℝ)))) := by
  obtain ⟨Cprim, hCprimpos, hprim⟩ := sharpPrimitiveOffAxis
  obtain ⟨Czr, hCzrpos, hzr⟩ := zetaLogDerivRegularSharp
  have key : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → |τ| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (1 / 2) * Real.log (q : ℝ) + (Cprim + Real.log 2) := by
    intro q _inst χ hχ σ τ hσ1 hσ2 hτ
    haveI hN : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψne : χ.primitiveCharacter ≠ 1 := prim_ne_one_of_ne_one hχ
    have hs : (1 : ℝ) < (((σ : ℂ) + (τ : ℂ) * Complex.I)).re := by simp; linarith only [hσ1]
    have hp := (hprim χ.conductor χ.primitiveCharacter hψne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)).1 σ τ hσ1 hσ2 hτ
    have hcl := changeLevelSharpCorrection (hdvd := χ.conductor_dvd_level) χ.primitiveCharacter
      ((σ : ℂ) + (τ : ℂ) * Complex.I) hs
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
    linarith only [_inst, hN, hp, hcl]
  have key0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 → |u.im| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (u.im : ℂ) * Complex.I)).re ≤
        -1 / (σ - u.re) + (1 / 2) * Real.log (q : ℝ) + (Cprim + Real.log 2) := by
    intro q _inst χ hχ u hz σ hσ1 hσ2 huim
    haveI hN : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψne : χ.primitiveCharacter ≠ 1 := prim_ne_one_of_ne_one hχ
    have hs : (1 : ℝ) < (((σ : ℂ) + (u.im : ℂ) * Complex.I)).re := by simp; linarith only [hσ1]
    have hu : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
      LFunction_prim_eq_zero_of_zeroMult χ hχ hz
    have hp := (hprim χ.conductor χ.primitiveCharacter hψne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)).2 u hu σ hσ1 hσ2 huim
    have hcl := changeLevelSharpCorrection (hdvd := χ.conductor_dvd_level) χ.primitiveCharacter
      ((σ : ℂ) + (u.im : ℂ) * Complex.I) hs
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
    linarith only [_inst, hN, hp, hcl]
  have key1 : ∀ (q : ℕ) [NeZero q] (σ τ : ℝ), 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| → |τ| ≤ 12 →
      (-logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        (1 / 2) * Real.log (q : ℝ) + ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) := by
    intro q _inst σ τ hσ1 hσ2 hτ1 hτ2
    have hs : (1 : ℝ) < (((σ : ℂ) + (τ : ℂ) * Complex.I)).re := by simp; linarith only [hσ1]
    have hcl := changeLevelSharpCorrection (hdvd := Nat.one_dvd q) (1 : DirichletCharacter ℂ 1)
      ((σ : ℂ) + (τ : ℂ) * Complex.I) hs
    rw [DirichletCharacter.changeLevel_one] at hcl
    rw [DirichletCharacter.LFunction_modOne_eq] at hcl
    have hlog1 : Real.log (((1 : ℕ) : ℝ)) = 0 := by simp
    rw [hlog1] at hcl
    have hz := hzr σ τ hσ1 hσ2
    have hzeta : (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
        1 / 4 + (1 / 2) * Real.log 14 + Czr := by
      have hX : ((σ : ℂ) + (τ : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (τ : ℂ)) := by ring
      have hld : (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
          = (-deriv riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ)) /
              riemannZeta ((σ : ℂ) + Complex.I * (τ : ℂ))).re := by
        rw [logDeriv_apply, ← neg_div, hX]
      rw [hld]
      have hτsq : (1 : ℝ) ≤ τ ^ 2 := by
        have h := sq_abs τ; nlinarith only [hτ1, h]
      have h1 : (σ - 1) / ((σ - 1) ^ 2 + τ ^ 2) ≤ 1 / 4 := by
        have hden : 0 < (σ - 1) ^ 2 + τ ^ 2 := by nlinarith only [hτsq, hσ1, hσ2]
        rw [div_le_iff₀ hden]
        have hnum : σ - 1 ≤ 1 / 4 := by linarith only [hσ2]
        nlinarith only [hnum, hden, hτsq, hσ2]
      have h2 : (1 / 2) * Real.log (2 + |τ|) ≤ (1 / 2) * Real.log 14 := by
        have hle : 2 + |τ| ≤ 14 := by linarith only [abs_nonneg τ, hτ2]
        have := Real.log_le_log (by positivity) hle
        linarith only [this]
      linarith only [hz, h1, h2]
    linarith only [hcl, hzeta, _inst]
  refine ⟨3, max (Cprim + Real.log 2)
      ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) + 1, ?_, ?_⟩
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hge : Cprim + Real.log 2 ≤ max (Cprim + Real.log 2)
        ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) := le_max_left _ _
    linarith only [hCprimpos, hlog2pos, hge]
  · intro q hq hqne χ
    haveI : NeZero q := hqne
    have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hloglog : 0 ≤ Real.log (Real.log (q : ℝ)) := by
      have h3 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
        have h1 : (1 : ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
          exact le_of_lt Real.exp_one_lt_three
        exact le_trans h1 (Real.log_le_log (by norm_num) hq3)
      exact Real.log_nonneg h3
    have hfac : (1 : ℝ) ≤ 1 + Real.log (Real.log (q : ℝ)) := by linarith only [hloglog]
    have hCnonneg : 0 ≤ max (Cprim + Real.log 2)
        ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) + 1 := by
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hge := le_max_left (Cprim + Real.log 2)
        ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2)
      linarith only [hCprimpos, hlog2pos, hge]
    have hfinal : ∀ K : ℝ, K ≤ max (Cprim + Real.log 2)
        ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) → ∀ A : ℝ,
        A + K ≤ A +
          (max (Cprim + Real.log 2) ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) + 1) *
            (1 + Real.log (Real.log (q : ℝ))) := by
      intro K hK A
      have h1 : K ≤ max (Cprim + Real.log 2)
          ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) + 1 := by linarith only [hK]
      have h2 : K ≤ (max (Cprim + Real.log 2)
          ((1 / 4 + (1 / 2) * Real.log 14 + Czr) + Real.log 2) + 1) *
            (1 + Real.log (Real.log (q : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hfac hCnonneg
        linarith only [hK, hmul]
      linarith only [h2]
    refine ⟨?_, ?_, ?_⟩
    · intro hχ σ τ hσ1 hσ2 hτ
      exact le_trans (key q χ hχ σ τ hσ1 hσ2 hτ) (hfinal _ (le_max_left _ _) _)
    · intro σ τ hσ1 hσ2 hτ1 hτ2
      by_cases hχ : χ = 1
      · rw [hχ]
        exact le_trans (key1 q σ τ hσ1 hσ2 hτ1 hτ2) (hfinal _ (le_max_right _ _) _)
      · exact le_trans (key q χ hχ σ τ hσ1 hσ2 hτ2) (hfinal _ (le_max_left _ _) _)
    · intro hχ u hz σ hσ1 hσ2 huim
      exact le_trans (key0 q χ hχ u hz σ hσ1 hσ2 huim) (hfinal _ (le_max_left _ _) _)

set_option maxHeartbeats 1000000 in
/-- **Far zeros (`1 ≤ |Im| ≤ 4`) satisfy `λ ≥ 1/25` for all large `q`.** -/
theorem farZeroLambdaLowerDecent : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → Work.LinnikContract.zeroMult χ u ≠ 0 →
    1 ≤ |u.im| → |u.im| ≤ 4 → (1/25 : ℝ) ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨qA, C, hCpos, hA0⟩ := sharpLevelOffAxisLevel
  obtain ⟨Cζ, hCζpos, hζ⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  set x₀ : ℝ := max ((256 * C) ^ 2) (max (160 * Cζ) 1) with hx₀def
  have hx₀1 : 1 ≤ x₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max qA (max 6 (Nat.ceil (Real.exp x₀))), ?_⟩
  intro q hq hqne χ u hχ hz him1 him4
  haveI : NeZero q := hqne
  have hqA : qA ≤ q := le_trans (le_max_left _ _) hq
  have hqceil : Nat.ceil (Real.exp x₀) ≤ q :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)
  have hexp_le : Real.exp x₀ ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil (Real.exp x₀)) (by exact_mod_cast hqceil)
  have hlogx : x₀ ≤ Real.log (q : ℝ) := by
    calc x₀ = Real.log (Real.exp x₀) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexp_le
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := le_trans hx₀1 hlogx
  have hlogpos : 0 < Real.log (q : ℝ) := lt_of_lt_of_le zero_lt_one hlogq1
  -- the correction-term estimates
  have hCle : C ≤ Real.sqrt (Real.log (q : ℝ)) / 256 := by
    have h1 : (256 * C) ^ 2 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlogx
    have h2 : 0 ≤ 256 * C := by positivity
    have h3 : Real.sqrt ((256 * C) ^ 2) ≤ Real.sqrt (Real.log (q : ℝ)) := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq h2] at h3
    linarith only [h3]
  have hloglog_le : Real.log (Real.log (q : ℝ)) ≤ 2 * Real.sqrt (Real.log (q : ℝ)) := by
    have h := Real.log_le_rpow_div (le_of_lt hlogpos) (show (0 : ℝ) < 1 / 2 by norm_num)
    have hrw : Real.log (q : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Real.log (q : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrw, div_eq_mul_inv] at h
    linarith only [h]
  have hCorr : C * (1 + Real.log (Real.log (q : ℝ))) ≤ Real.log (q : ℝ) / 64 := by
    have hsq : Real.sqrt (Real.log (q : ℝ)) ^ 2 = Real.log (q : ℝ) :=
      Real.sq_sqrt (le_of_lt hlogpos)
    have hsqrt1 : 1 ≤ Real.sqrt (Real.log (q : ℝ)) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hlogq1
    have h1 : 1 + Real.log (Real.log (q : ℝ)) ≤ 3 * Real.sqrt (Real.log (q : ℝ)) := by
      linarith only [hloglog_le, hsqrt1]
    have h2 : C * (1 + Real.log (Real.log (q : ℝ)))
        ≤ C * (3 * Real.sqrt (Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_left h1 hCpos.le
    have h3 : C * (3 * Real.sqrt (Real.log (q : ℝ)))
        ≤ (Real.sqrt (Real.log (q : ℝ)) / 256) * (3 * Real.sqrt (Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_right hCle (by positivity)
    have h4 : (Real.sqrt (Real.log (q : ℝ)) / 256) * (3 * Real.sqrt (Real.log (q : ℝ)))
        = 3 * Real.log (q : ℝ) / 256 := by
      nlinarith only [hsq]
    have h5 : 3 * Real.log (q : ℝ) / 256 ≤ Real.log (q : ℝ) / 64 := by linarith only [hx₀1, hlogx]
    linarith only [h2, h3, h4, h5, hx₀1, hlogx, hsq]
  have hCζle : Cζ ≤ Real.log (q : ℝ) / 160 := by
    have h1 : 160 * Cζ ≤ Real.log (q : ℝ) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hlogx)
    linarith only [h1]
  -- the zero and the parameters
  have hstrip : 0 < u.re ∧ u.re < 1 := zeroMult_strip χ hχ hz
  set γ : ℝ := u.im with hγdef
  set ε : ℝ := 1 - u.re with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith only [hstrip.2, hstrip]
  obtain ⟨hs5, hvpos, hsval⟩ := sqrtData
  have hγle : |γ| ≤ 12 := by rw [hγdef]; linarith only [abs_nonneg u.im, him4, hstrip]
  have hγ4 : |γ| ≤ 4 := by rw [hγdef]; exact him4
  have hγge : 1 ≤ |γ| := by rw [hγdef]; exact him1
  by_contra hcon
  rw [not_le] at hcon
  have hlam : ε * Real.log (q : ℝ) < 1 / 25 := by
    rw [Work.LinnikContract.lamOf] at hcon
    rw [← hεdef] at hcon
    exact hcon
  have hεsmall : ε < 1 / 25 := by nlinarith only [hlam, hεpos, hlogq1, hx₀1, hstrip, hlogx]
  set δ : ℝ := Real.sqrt (5 / 4) * ε / (Real.sqrt 2 - Real.sqrt (5 / 4)) with hδdef
  have hδpos : 0 < δ := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hεpos) hvpos
  have hδle : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_iff₀ hvpos]
    have hs5le : Real.sqrt (5 / 4) ≤ 23 / 20 := by
      have h : (5 / 4 : ℝ) ≤ (23 / 20) ^ 2 := by norm_num
      calc Real.sqrt (5 / 4) ≤ Real.sqrt ((23 / 20) ^ 2) := Real.sqrt_le_sqrt h
        _ = 23 / 20 := Real.sqrt_sq (by norm_num)
    have hs2ge : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
      have h : (7 / 5 : ℝ) ^ 2 ≤ 2 := by norm_num
      calc (7 / 5 : ℝ) = Real.sqrt ((7 / 5) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h
    have hvge : 1 / 4 ≤ Real.sqrt 2 - Real.sqrt (5 / 4) := by linarith only [hs5le, hs2ge]
    calc Real.sqrt (5 / 4) * ε ≤ (23 / 20) * (1 / 25) := by nlinarith only [hs5le, hεsmall, hεpos, hx₀1, hstrip, hlogx, hlam]
      _ ≤ (1 / 4) * (1 / 4) := by norm_num
      _ ≤ (1 / 4) * (Real.sqrt 2 - Real.sqrt (5 / 4)) :=
          mul_le_mul_of_nonneg_left hvge (by norm_num)
  have hσ1 : (1 : ℝ) < 1 + δ := by linarith only [hδpos]
  have hσ2 : (1 : ℝ) + δ ≤ 5 / 4 := by linarith only [hδle]
  have hσ2' : (1 : ℝ) + δ ≤ 2 := by linarith only [hstrip, hεsmall, hδle]
  have hfour := fourTermPointwise (q := q) χ (σ := 1 + δ) (γ := γ) hσ1
  have hAq := hA0 q hqA χ
  have hb1 : (-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) / riemannZeta (((1 + δ : ℝ) : ℂ))).re
      ≤ 1 / δ + Cζ := by
    have h := hζ (1 + δ) hσ1 hσ2'
    have h1 : (1 + δ : ℝ) - 1 = δ := by ring
    rw [h1] at h
    exact h
  have hb2 : (-logDeriv (DirichletCharacter.LFunction χ)
        (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ -1 / (δ + ε) + (1 / 2) * Real.log (q : ℝ)
          + C * (1 + Real.log (Real.log (q : ℝ))) := by
    have h := hAq.2.2 hχ u hz (1 + δ) hσ1 hσ2 hγle
    have h1 : (1 + δ : ℝ) - u.re = δ + ε := by rw [hεdef]; ring
    rw [h1] at h
    exact h
  have hb3 : (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
      ≤ (1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ))) := by
    have hAq2 := hA0 q hqA (χ ^ 2)
    have h := hAq2.2.1 (1 + δ) (2 * γ) hσ1 hσ2 ?_ ?_
    · exact h
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith only [hstrip, him1, hεsmall]
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith only [hstrip, him4, hεsmall]
  have hb4 : (-logDeriv (DirichletCharacter.LFunction (χ ^ 3))
        (((1 + δ : ℝ) : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re
      ≤ (1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ))) := by
    have hAq3 := hA0 q hqA (χ ^ 3)
    have h := hAq3.2.1 (1 + δ) (3 * γ) hσ1 hσ2 ?_ ?_
    · exact h
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith only [hstrip, him1, hεsmall]
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith only [him4]
  have hmain : 2 / (δ + ε) ≤ (5 / 4) / δ + (13 / 8) * Real.log (q : ℝ)
      + (13 / 4) * (C * (1 + Real.log (Real.log (q : ℝ)))) + (5 / 4) * Cζ := by
    have e1 : (5 / 4 : ℝ) * (-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) / riemannZeta (((1 + δ : ℝ) : ℂ))).re
        ≤ (5 / 4) * (1 / δ + Cζ) := by linarith only [hb1]
    have e2 : 2 * (-logDeriv (DirichletCharacter.LFunction χ)
          (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ 2 * (-1 / (δ + ε) + (1 / 2) * Real.log (q : ℝ)
            + C * (1 + Real.log (Real.log (q : ℝ)))) := by linarith only [hb2, this]
    have e3 : 1 * (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
          (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
        ≤ 1 * ((1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ)))) := by
      linarith only [hb3, this]
    have e4 : (1 / 4 : ℝ) * (-logDeriv (DirichletCharacter.LFunction (χ ^ 3))
          (((1 + δ : ℝ) : ℂ) + ((3 * γ : ℝ) : ℂ) * Complex.I)).re
        ≤ (1 / 4) * ((1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ)))) := by
      linarith only [hb4, this]
    have e5 : (5 / 4 : ℝ) * (1 / δ + Cζ)
        + 2 * (-1 / (δ + ε) + (1 / 2) * Real.log (q : ℝ)
            + C * (1 + Real.log (Real.log (q : ℝ))))
        + 1 * ((1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ))))
        + (1 / 4) * ((1 / 2) * Real.log (q : ℝ) + C * (1 + Real.log (Real.log (q : ℝ))))
        = (5 / 4) / δ + (13 / 8) * Real.log (q : ℝ)
            + (13 / 4) * (C * (1 + Real.log (Real.log (q : ℝ)))) + (5 / 4) * Cζ
            - 2 / (δ + ε) := by ring
    linarith only [hfour, e1, e2, e3, e4, e5, this, hb1, hb2, hb3, hb4]
  have hKbound : (13 / 4) * (C * (1 + Real.log (Real.log (q : ℝ)))) + (5 / 4) * Cζ
      ≤ (13 / 128) * Real.log (q : ℝ) := by
    have h1 : (13 / 4) * (C * (1 + Real.log (Real.log (q : ℝ))))
        ≤ (13 / 4) * (Real.log (q : ℝ) / 64) :=
      mul_le_mul_of_nonneg_left hCorr (by norm_num)
    have h2 : (5 / 4) * Cζ ≤ (5 / 4) * (Real.log (q : ℝ) / 160) :=
      mul_le_mul_of_nonneg_left hCζle (by norm_num)
    linarith only [h1, h2, hCζpos, hCorr, hCζle]
  have hker := keyArith (ε := ε) (s := Real.sqrt (5 / 4)) (v := Real.sqrt 2 - Real.sqrt (5 / 4))
    hεpos hvpos (Real.sqrt_pos.mpr (by norm_num))
    (by
      rw [show Real.sqrt (5 / 4) + (Real.sqrt 2 - Real.sqrt (5 / 4)) = Real.sqrt 2 by ring,
        Real.sq_sqrt (by norm_num)])
    (Real.sq_sqrt (by norm_num))
  have hsub : 2 / (δ + ε) - (5 / 4) / δ = (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 / ε := by
    rw [hδdef]; exact hker
  have hkey : (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 / ε
      ≤ (13 / 8) * Real.log (q : ℝ) * (17 / 16) := by
    nlinarith only [hmain, hKbound, hsub, hlogpos, hCζpos, hCorr, hCζle]
  have hpos2 : (0 : ℝ) < (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 := by positivity
  have hfinal : (1 / 25 : ℝ) ≤ ε * Real.log (q : ℝ) := by
    have hmul : (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 ≤ (13 / 8) * Real.log (q : ℝ) * (17 / 16) * ε := by
      have h := mul_le_mul_of_nonneg_right hkey hεpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hεpos)] at h
      exact h
    have hnum : (13 / 4 - Real.sqrt 10) * 128 / 221 ≤ ε * Real.log (q : ℝ) := by
      have hcoef : (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 = 13 / 4 - Real.sqrt 10 := hsval
      nlinarith only [hmul, numBound, hlogpos, hεpos, Real.sqrt_nonneg 10, hsval]
    linarith only [hnum, numBound, hsval, hlam, hmul]
  linarith only [hfinal, hlam]

end

end Work.LinnikAreas.OtherCharRepel
