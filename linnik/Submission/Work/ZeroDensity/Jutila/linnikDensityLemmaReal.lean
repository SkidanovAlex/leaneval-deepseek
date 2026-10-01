import Mathlib
import Submission.Work.ZeroDensity.Jutila.linnikDensityLemma
import Submission.Work.ZeroDensity.Jutila.kernelSumHalf

namespace Work.ZeroDensity.Jutila

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

/-!
# Linnik's density lemma with `|T|`, for an arbitrary real height

`Work.ZeroDensity.Jutila.linnikDensityLemmaReal` is the density estimate of
`Work.ZeroDensity.Jutila.linnikDensityLemma` (Jutila's Lemma 8) but formulated for *every* real
height `T`, with the logarithm on the right-hand side evaluated at `q·(|T| + 2)` and without the
hypothesis `1 ≤ T`.  The consumer of the estimate (the near-line reduction in
`Submission/Work/ZeroDensity/Jutila/jutilaNonPrincipal.lean`) needs boxes at arbitrary real heights.

Nothing new is needed analytically: `kernelSumHalf` (the Hadamard partial fraction at
`s₀ = 1 + λ + iT`) is already stated for arbitrary real `τ`, with `log (2 + |τ|)` on the right-hand
side.  The only changes are

* the ball of zeros is taken with radius `2(|T| + 2)` instead of `2(T + 2)`
  (`boxSum_le_kernelSumGen`: every box zero satisfies `|Im ρ| ≤ |T| + 1/2` and `|Re ρ| ≤ 1`);
* the elementary arithmetic `arithRealAux` turns
  `(17λ/4)(1/λ + log N/2 + log(2+|T|)/2 + 4)` into `64(λ·log(q(|T|+2)) + 1)`, using only
  `N ≤ q` and `q ≥ 2`.
-/

/-- Pointwise form of `Re (1/((a : ℂ) + iT - u))`. -/
private lemma one_div_sub_re_explicit (a T : ℝ) (u : ℂ) :
    (1 / (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re
      = (a - u.re) / ((a - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hzre : (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = a - u.re := by simp
  have hzim : (((a : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hzre, hzim]
  ring

private theorem boxSum_le_kernelSumGen {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hψprim : ψ.IsPrimitive) {σ T : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction ψ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) ρ : ℝ) else 0)
      ≤ (17 * (1 - σ) / 4) * (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ) *
            (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) := by
  classical
  have hdiff : Differentiable ℂ (completedLFunction ψ) :=
    DirichletCharacter.differentiable_completedLFunction hψ
  have hAn : AnalyticOnNhd ℂ (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2))) :=
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hdiff _
  -- every zero in the box lies in the ball
  have huball : ∀ u : ℂ, analyticOrderNatAt (completedLFunction ψ) u ≠ 0 → σ ≤ u.re →
      u.re ≤ 1 → |u.im - T| ≤ (1 - σ) / 2 → u ∈ Metric.closedBall (0 : ℂ) (2 * (|T| + 2)) := by
    intro u hord hσu hu1 him
    have hzu : completedLFunction ψ u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
    have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
    rw [Metric.mem_closedBall, dist_zero_right]
    have himabs : |u.im| ≤ |T| + 1 / 2 := by
      calc |u.im| = |(u.im - T) + T| := by ring_nf
        _ ≤ |u.im - T| + |T| := abs_add_le _ _
        _ ≤ (1 - σ) / 2 + |T| := by linarith
        _ ≤ |T| + 1 / 2 := by linarith
    have hrere : |u.re| ≤ 1 := abs_le.mpr ⟨by linarith [hstrip.1.le], hu1⟩
    calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      _ ≤ 1 + (|T| + 1 / 2) := by linarith
      _ ≤ 2 * (|T| + 2) := by linarith [abs_nonneg T]
  -- the pointwise domination
  have hpoint : ∀ u : ℂ,
      (if analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
          |u.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) u : ℝ) else 0)
        ≤ (17 * (1 - σ) / 4) *
            ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ) *
              (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) := by
    intro u
    by_cases hbox : analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im - T| ≤ (1 - σ) / 2
    · rw [if_pos hbox]
      obtain ⟨hord, hσu, hu1, him⟩ := hbox
      have hzu : completedLFunction ψ u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
      have hlampos : 0 < 1 - σ := by
        rcases lt_or_ge (0 : ℝ) (1 - σ) with hpos | hnonpos
        · exact hpos
        · exfalso
          have h0 : (1 : ℝ) - σ = 0 := le_antisymm hnonpos (by linarith)
          have hure : u.re = 1 := le_antisymm hu1 (by linarith [h0, hσu])
          linarith [hstrip.2, hure]
      have hDval : (MeromorphicOn.divisor (completedLFunction ψ)
            (Metric.closedBall 0 (2 * (|T| + 2)))) u = ↑(analyticOrderNatAt (completedLFunction ψ) u) :=
        Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hAn (huball u hord hσu hu1 him)
      have hcast : (((analyticOrderNatAt (completedLFunction ψ) u : ℤ) : ℝ)) =
          ((analyticOrderNatAt (completedLFunction ψ) u : ℕ) : ℝ) := by simp
      rw [hDval, hcast]
      have hk : 4 / (17 * (1 - σ)) ≤
          (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re := by
        refine kernelReLower (a := 1 + (1 - σ)) (T := T) (lam := 1 - σ) hlampos ?_ ?_ ?_
        · have : (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = 1 + (1 - σ) - u.re := by
            simp
          linarith
        · have : (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u).re = 1 + (1 - σ) - u.re := by
            simp
          linarith
        · exact him
      have hkey : (17 * (1 - σ) / 4) *
          ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) * (4 / (17 * (1 - σ)))) =
            (analyticOrderNatAt (completedLFunction ψ) u : ℝ) := by
        have hne : (1 : ℝ) - σ ≠ 0 := ne_of_gt hlampos
        field_simp
      calc ((analyticOrderNatAt (completedLFunction ψ) u : ℝ))
          = (17 * (1 - σ) / 4) *
              ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) * (4 / (17 * (1 - σ)))) :=
                hkey.symm
        _ ≤ (17 * (1 - σ) / 4) *
              ((analyticOrderNatAt (completedLFunction ψ) u : ℝ) *
                (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hk (by positivity)) (by linarith)
    · rw [if_neg hbox]
      apply mul_nonneg (by linarith)
      by_cases hDu : (MeromorphicOn.divisor (completedLFunction ψ)
          (Metric.closedBall 0 (2 * (|T| + 2)))) u = 0
      · rw [hDu]; simp
      · have hzu := Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn hDu
        have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u hzu
        have hk : 0 ≤ (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re := by
          rw [one_div_sub_re_explicit]
          have h1 : 0 < 1 + (1 - σ) - u.re := by linarith [hstrip.2, hσ1]
          have h2 : 0 < (1 + (1 - σ) - u.re) ^ 2 + (T - u.im) ^ 2 := by
            nlinarith [sq_nonneg (T - u.im), h1]
          exact div_nonneg h1.le h2.le
        exact mul_nonneg (Int.cast_nonneg ((MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn) u)) hk
  -- finite supports and the finsum comparison
  have hDfin : (Function.support (fun u : ℂ =>
      ((((MeromorphicOn.divisor (completedLFunction ψ)
        (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ)))).Finite :=
    ((MeromorphicOn.divisor (completedLFunction ψ)
      (Metric.closedBall 0 (2 * (|T| + 2)))).finiteSupport
        (isCompact_closedBall (0 : ℂ) (2 * (|T| + 2)))).subset (by
          intro u hu
          rw [Function.mem_support] at hu ⊢
          intro h0
          exact hu (by rw [h0, Int.cast_zero]))
  have hfsF : Function.HasFiniteSupport (fun u : ℂ =>
      if analyticOrderNatAt (completedLFunction ψ) u ≠ 0 ∧ σ ≤ u.re ∧ u.re ≤ 1 ∧
        |u.im - T| ≤ (1 - σ) / 2 then (analyticOrderNatAt (completedLFunction ψ) u : ℝ) else 0) :=
    hDfin.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hDu
      apply hu
      rw [if_neg]
      rintro ⟨hord, hσu, hu1, him⟩
      have hDval := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hAn
        (huball u hord hσu hu1 him)
      rw [hDval] at hDu
      exact hord (by simpa using hDu))
  have hfsG : Function.HasFiniteSupport (fun u : ℂ => (17 * (1 - σ) / 4) *
      ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ) *
        (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re)) :=
    hDfin.subset (by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hDu
      exact hu (by rw [hDu]; ring))
  have h1 := finsum_le_finsum' hfsF hfsG hpoint
  have h2 : (∑ᶠ u : ℂ, (17 * (1 - σ) / 4) *
      ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ) *
        (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re))
      = (17 * (1 - σ) / 4) * (∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor (completedLFunction ψ) (Metric.closedBall 0 (2 * (|T| + 2)))) u : ℤ) : ℝ) *
            (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * (T : ℂ) - u)).re)) := by
    rw [← mul_finsum]
  exact le_trans h1 (le_of_eq h2)
/-- Elementary arithmetic: for `0 ≤ λ ≤ 1`, `1 ≤ N ≤ q`, `q ≥ 2` and arbitrary real `T`,
`(17λ/4)(1/λ + log N/2 + log(2+|T|)/2 + 4) ≤ 64(λ·log(q(|T|+2)) + 1)`. -/
private theorem arithRealAux {lam N q T : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hN : 1 ≤ N) (hNq : N ≤ q) (hq : 2 ≤ q) :
    (17 * lam / 4) * (1 / lam + (1 / 2) * Real.log N + (1 / 2) * Real.log (2 + |T|) + 4)
      ≤ 64 * (lam * Real.log (q * (|T| + 2)) + 1) := by
  have hA0 : (0 : ℝ) < |T| + 2 := by linarith [abs_nonneg T]
  have hA1 : (1 : ℝ) ≤ |T| + 2 := by linarith [abs_nonneg T]
  have hA2 : (2 : ℝ) ≤ |T| + 2 := by linarith [abs_nonneg T]
  have hq0 : (0 : ℝ) < q := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 ≤ Real.log (q * (|T| + 2)) := by
    apply Real.log_nonneg
    have h4 : (2 : ℝ) * 2 ≤ q * (|T| + 2) := mul_le_mul hq hA2 (by norm_num) (by linarith)
    linarith
  have hlogN : Real.log N ≤ Real.log (q * (|T| + 2)) := by
    refine Real.log_le_log hN0 ?_
    have h1 : (q : ℝ) ≤ q * (|T| + 2) := by
      have := mul_le_mul_of_nonneg_left hA1 (le_of_lt hq0)
      linarith
    linarith
  have hlogT : Real.log (2 + |T|) ≤ Real.log (q * (|T| + 2)) := by
    refine Real.log_le_log (by linarith [abs_nonneg T]) ?_
    have h1 : (2 : ℝ) * (|T| + 2) ≤ q * (|T| + 2) :=
      mul_le_mul_of_nonneg_right hq (le_of_lt hA0)
    have h2 : 2 + |T| ≤ 2 * (|T| + 2) := by linarith [abs_nonneg T]
    linarith
  rcases eq_or_lt_of_le hlam0 with hz | hpos
  · rw [← hz]
    have h1 : (17 * (0 : ℝ) / 4) * (1 / (0 : ℝ) + (1 / 2) * Real.log N +
        (1 / 2) * Real.log (2 + |T|) + 4) = 0 := by ring
    have h2 : 64 * ((0 : ℝ) * Real.log (q * (|T| + 2)) + 1) = 64 := by ring
    rw [h1, h2]
    norm_num
  · set L : ℝ := Real.log (q * (|T| + 2)) with hL
    have hstep : (1 / lam + (1 / 2) * Real.log N + (1 / 2) * Real.log (2 + |T|) + 4)
        ≤ 1 / lam + (L + 4) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 17 * lam / 4)
    have hl : lam ≠ 0 := ne_of_gt hpos
    have hkey1 : (17 * lam / 4) * (1 / lam) = 17 / 4 := by
      field_simp
    have heq : (17 * lam / 4) * (1 / lam + (L + 4)) =
        17 / 4 + (17 * lam / 4) * L + 17 * lam := by
      rw [mul_add, hkey1]
      ring
    have hfin : (17 : ℝ) / 4 + (17 * lam / 4) * L + 17 * lam ≤ 64 * (lam * L + 1) := by
      have hlamL : 0 ≤ lam * L := mul_nonneg hlam0 hL0
      nlinarith [hlamL, hlam0, hlam1]
    have hgoal : 64 * (lam * L + 1) = 64 * (lam * Real.log (q * (|T| + 2)) + 1) := by rw [hL]
    linarith [hmul, heq, hfin, hgoal]

/-- **Linnik's density lemma with an absolute constant, at an arbitrary real height `T`.**

There is an absolute constant `C > 0` such that for every `q ≥ 2`, every non-principal Dirichlet
character `χ` mod `q`, every `0 ≤ σ ≤ 1` and **every** real `T`, the multiplicity-weighted number of
zeros `ρ` of the completed `L`-function of the primitive character inducing `χ` with
`σ ≤ Re ρ ≤ 1` and `|Im ρ - T| ≤ (1-σ)/2` is at most `C·((1-σ)·log(q(|T|+2)) + 1)`.

This is `Work.ZeroDensity.Jutila.linnikDensityLemma` (Jutila (1977), Lemma 8, i.e. the density
lemma of Linnik) without the restriction `1 ≤ T`: the same Hadamard partial-fraction argument
applies, with the ball of zeros taken large enough to contain the box whatever the sign of `T`. -/
theorem linnikDensityLemmaReal :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 →
      (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - T| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (|T| + 2)) + 1) := by
  refine ⟨64, by norm_num, ?_⟩
  intro q hq qne χ hχ σ T hσ0 hσ1
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨hψne, hdiv, hcon1, hconq⟩ := primitiveCharacterConductor χ hχ
  have hzero : ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ =
      analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ := fun ρ => rfl
  have hconv : (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - T| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      = (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0) := by
    simp only [hzero]
  rw [hconv]
  have hprim : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hbk := boxSum_le_kernelSumGen (N := χ.conductor) (ψ := χ.primitiveCharacter) hψne hprim
    (σ := σ) (T := T) hσ0 hσ1
  rcases lt_or_ge (0 : ℝ) (1 - σ) with hpos | hnonpos
  · have hks := kernelSumHalf (N := χ.conductor) (χ := χ.primitiveCharacter) hψne hprim
      (σ := 1 + (1 - σ)) (τ := T) (by linarith) (by linarith) (2 * (|T| + 2))
    have hsub : 1 + (1 - σ) - 1 = 1 - σ := by ring
    rw [hsub] at hks
    have hstep : (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0)
        ≤ (17 * (1 - σ) / 4) * (1 / (1 - σ) + (1 / 2) * Real.log (χ.conductor : ℝ) +
            1 / 2 * Real.log (2 + |T|) + 4) :=
      le_trans hbk (mul_le_mul_of_nonneg_left hks (by linarith))
    have hcon1r : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hcon1
    have hconqr : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hconq
    have hqr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have harith := arithRealAux (lam := 1 - σ) (N := (χ.conductor : ℝ)) (q := (q : ℝ)) (T := T)
      (by linarith) (by linarith) hcon1r hconqr hqr
    linarith [hstep, harith]
  · have h0 : (1 : ℝ) - σ = 0 := le_antisymm hnonpos (by linarith)
    have hLHS0 : (∑ᶠ ρ : ℂ, if analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 ∧
          σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - T| ≤ (1 - σ) / 2 then
          (analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ : ℝ) else 0) ≤ 0 := by
      simpa [h0] using hbk
    have hRHS : 64 * ((1 - σ) * Real.log ((q : ℝ) * (|T| + 2)) + 1) = 64 := by
      rw [h0]; ring
    linarith [hLHS0, hRHS]

end Work.ZeroDensity.Jutila
