/-
# Uniform convexity on the critical line (Hypothesis A of BGTZ)

The BGTZ repulsion consumes a *uniform* subconvexity/convexity bound
`‖L(1/2+it,ψ)‖ ≤ A (N(1+|t|))^θ` for primitive `ψ` mod `N`, with a single absolute
constant `A`.  The shared commons proves the classical convexity bound with an
*absolute* constant, in logarithmic form:

`Real.log ‖L(σ+iT,ψ)‖ ≤ ((1-σ)/2)·(log N + log(2+|T|)) + log(log(N(2+|T|))+2) + 6`

(`Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`).  At `σ = 1/2`
this is `log ‖L‖ ≤ (1/4)·log(N(2+|t|)) + log(log(N(2+|t|))+2) + 6`, and the two logarithmic
losses are absorbed into the extra power `(N(1+|t|))^{1/100}`:

*  `N(2+|t|) ≤ 2·N(1+|t|)`, so `(1/4)log(N(2+|t|)) ≤ (1/4)(log 2 + log(N(1+|t|)))`;
*  `log x ≤ x^{ε}/ε` (`Real.log_le_rpow_div`) gives
   `log(N(2+|t|)) + 2 ≤ (100·2^{1/100} + 2)·(N(1+|t|))^{1/100}`,
   whence `log(log(N(2+|t|))+2) ≤ log(100·2^{1/100}+2) + (1/100)·log(N(1+|t|))`.

Summing, the whole right hand side is
`log A + (1/4 + 1/100)·log(N(1+|t|))` with
`A = exp(log(100·2^{1/100}+2) + (1/4)log 2 + 6)`, which is exactly `HypA A (1/4+1/100)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- The absorbable factor `100·2^{1/100} + 2` coming from `Real.log_le_rpow_div`. -/
private def convexityK : ℝ := 100 * (2 : ℝ) ^ (1 / 100 : ℝ) + 2

/-- The absolute constant `A` of Hypothesis A for the exponent `1/4 + 1/100`. -/
private def convexityA : ℝ := Real.exp (Real.log convexityK + (1 / 4) * Real.log 2 + 6)

private lemma convexityK_pos : 0 < convexityK := by
  unfold convexityK
  have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / 100 : ℝ)
  positivity

private lemma convexityA_pos : 0 < convexityA := Real.exp_pos _

/-- `log (2x) + 2 ≤ (100·2^{1/100}+2)·x^{1/100}` for `x ≥ 1`. -/
private lemma log_absorb {x : ℝ} (hx : 1 ≤ x) :
    Real.log (2 * x) + 2 ≤ convexityK * x ^ (1 / 100 : ℝ) := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have h2x : (0 : ℝ) < 2 * x := by positivity
  have hxr : (1 : ℝ) ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hlog : Real.log (2 * x) ≤ 100 * (2 * x) ^ (1 / 100 : ℝ) := by
    have h := Real.log_le_rpow_div h2x.le (show (0 : ℝ) < 1 / 100 by norm_num)
    have he : (2 * x) ^ (1 / 100 : ℝ) / (1 / 100) = 100 * (2 * x) ^ (1 / 100 : ℝ) := by
      rw [div_eq_mul_inv, show ((1 : ℝ) / 100)⁻¹ = 100 by norm_num, mul_comm]
    rw [he] at h
    exact h
  have hsplit : (2 * x) ^ (1 / 100 : ℝ) = (2 : ℝ) ^ (1 / 100 : ℝ) * x ^ (1 / 100 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxpos.le]
  have hcomb : 100 * (2 * x) ^ (1 / 100 : ℝ) + 2 ≤ convexityK * x ^ (1 / 100 : ℝ) := by
    rw [hsplit]
    unfold convexityK
    nlinarith [hxr, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / 100 : ℝ)]
  linarith [hlog, hcomb]

theorem UniformConvexity : ∃ A : ℝ, Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100) := by
  refine ⟨convexityA, convexityA_pos, by norm_num, by norm_num, ?_⟩
  intro N _ ψ hprim hne t
  set U : ℝ := (N : ℝ) * (1 + |t|) with hU
  set V : ℝ := (N : ℝ) * (2 + |t|) with hV
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have ht1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have ht2 : (0 : ℝ) < 2 + |t| := by linarith [abs_nonneg t]
  have hU1 : (1 : ℝ) ≤ U := by
    rw [hU]
    exact one_le_mul_of_one_le_of_one_le hN1 ht1
  have hUpos : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
  have hVpos : (0 : ℝ) < V := by rw [hV]; exact mul_pos hNpos ht2
  have hV2 : (2 : ℝ) ≤ V := by rw [hV]; nlinarith [hN1, abs_nonneg t]
  -- the absolute convexity bound at σ = 1/2, in logarithmic form
  have hconv :=
    Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs ψ hne hprim
      (σ := (1 / 2 : ℝ)) (T := t) (by norm_num) (by norm_num)
  have harg : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = ((1 / 2 : ℝ) : ℂ) + I * (t : ℂ) := by
    rw [mul_comm]
  have hconv' : Real.log ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      (1 / 4) * (Real.log (N : ℝ) + Real.log (2 + |t|)) + Real.log (Real.log V + 2) + 6 := by
    have h := hconv
    rw [← hV] at h
    have hq : ((1 - (1 / 2 : ℝ)) / 2) = 1 / 4 := by norm_num
    rw [hq] at h
    rw [harg]
    exact h
  -- the two comparisons that absorb the logarithms
  have hVU : V ≤ 2 * U := by
    rw [hV, hU]
    nlinarith [hNpos, abs_nonneg t]
  have hlogVU : Real.log V ≤ Real.log (2 * U) := Real.log_le_log hVpos hVU
  have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U :=
    Real.log_mul (by norm_num) hUpos.ne'
  have hstep1 : (1 / 4) * (Real.log (N : ℝ) + Real.log (2 + |t|)) ≤
      (1 / 4) * (Real.log 2 + Real.log U) := by
    have hlogV : Real.log (N : ℝ) + Real.log (2 + |t|) = Real.log V := by
      rw [hV]
      exact (Real.log_mul hNpos.ne' ht2.ne').symm
    linarith [hlogV, hlogVU, hlog2U]
  have hstep2 : Real.log (Real.log V + 2) ≤ Real.log convexityK + (1 / 100) * Real.log U := by
    have hlogV2pos : 0 < Real.log V + 2 := by
      have := Real.log_pos (by linarith : (1 : ℝ) < V)
      linarith
    have habs : Real.log V + 2 ≤ convexityK * U ^ (1 / 100 : ℝ) := by
      have h1 := log_absorb hU1
      linarith [hlogVU, h1]
    have hKpos : 0 < convexityK := convexityK_pos
    have hUrpos : 0 < U ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hUpos _
    have hle := Real.log_le_log hlogV2pos habs
    rw [Real.log_mul hKpos.ne' hUrpos.ne', Real.log_rpow hUpos] at hle
    exact hle
  have hbound : Real.log ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log convexityA + ((1 : ℝ) / 4 + 1 / 100) * Real.log U := by
    have hA : Real.log convexityA = Real.log convexityK + (1 / 4) * Real.log 2 + 6 :=
      Real.log_exp _
    linarith [hconv', hstep1, hstep2, hA]
  have hmain : ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      convexityA * U ^ ((1 : ℝ) / 4 + 1 / 100) := by
    calc ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ Real.exp (Real.log ‖LFunction ψ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
          Real.le_exp_log _
      _ ≤ Real.exp (Real.log convexityA + ((1 : ℝ) / 4 + 1 / 100) * Real.log U) :=
          Real.exp_le_exp.mpr hbound
      _ = convexityA * U ^ ((1 : ℝ) / 4 + 1 / 100) := by
          rw [Real.exp_add, Real.exp_log convexityA_pos]
          congr 1
          rw [mul_comm, Real.rpow_def_of_pos hUpos]
  exact hmain

end Work.LinnikAreas.BGTZ
