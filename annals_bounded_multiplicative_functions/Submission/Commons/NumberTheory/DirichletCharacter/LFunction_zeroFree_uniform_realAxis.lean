import Mathlib
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_fe
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_diskZeroCount_explicit
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.DirichletCharacter.isPrimitive_inv
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Filter
open scoped Real Topology BigOperators
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ## The symmetric form of the Hadamard partial fraction -/

/-- Finiteness of the support of the divisor of `Λ` in balls, for a non-trivial `χ`. -/
private lemma pf_support_finite (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R : ℝ) :
    (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u)).Finite := by
  have hAn : AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall (0:ℂ) R) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  exact MeromorphicOn.divisor_support_finite_of_subset
    (f := completedLFunction χ) (V := Metric.closedBall (0:ℂ) R)
    (U := Metric.closedBall (0:ℂ) R) hAn.meromorphicOn
    (isCompact_closedBall (0:ℂ) R) (fun z hz => hz)

/-- Real part of a finite sum of complex numbers. -/
private lemma re_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a A' ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

/-- The divisor weight at radius `R`. -/
private noncomputable def pfW (χ : DirichletCharacter ℂ N) (R : ℝ) (u : ℂ) : ℂ :=
  (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ)

/-- The partial-fraction sum based at `0`. -/
private noncomputable def pfSum (χ : DirichletCharacter ℂ N) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ u : ℂ, pfW χ R u * (1 / (s - u) + 1 / u)

/-- The symmetric partial-fraction sum (the difference of the sums at `s` and `1 - s`). -/
private noncomputable def pfSym (χ : DirichletCharacter ℂ N) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ u : ℂ, pfW χ R u * (1 / (s - u) + 1 / (s + u - 1))

/-- Difference of the partial-fraction sums at `s` and `1 - s`: the terms `1/u` cancel and the
symmetric kernel `1/(s-ρ) + 1/(s+ρ-1)` appears. -/
private lemma pf_diff (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R : ℝ) (s : ℂ) :
    pfSum χ R s - pfSum χ R (1 - s) = pfSym χ R s := by
  classical
  have hS := pf_support_finite χ hχ R
  let S : Finset ℂ := hS.toFinset
  have hmem : ∀ u : ℂ, u ∈ S ↔
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
    intro u
    simp [S, Set.Finite.mem_toFinset]
  have key : ∀ u : ℂ, pfW χ R u ≠ 0 → u ∈ S := by
    intro u hu'
    exact (hmem u).mpr (by
      simp only [pfW] at hu'
      intro h
      exact hu' (by rw [h]; simp))
  have h1 : pfSum χ R s = ∑ u ∈ S, pfW χ R u * (1 / (s - u) + 1 / u) := by
    show (∑ᶠ u : ℂ, pfW χ R u * (1 / (s - u) + 1 / u)) = _
    rw [finsum_eq_sum_of_support_subset _ (s := S) (fun u hu => ?_)]
    simp only [Function.mem_support] at hu
    exact key u (mul_ne_zero_iff.mp hu).1
  have h2 : pfSum χ R (1 - s) = ∑ u ∈ S, pfW χ R u * (1 / ((1 - s) - u) + 1 / u) := by
    show (∑ᶠ u : ℂ, pfW χ R u * (1 / ((1 - s) - u) + 1 / u)) = _
    rw [finsum_eq_sum_of_support_subset _ (s := S) (fun u hu => ?_)]
    simp only [Function.mem_support] at hu
    exact key u (mul_ne_zero_iff.mp hu).1
  have h3 : pfSym χ R s = ∑ u ∈ S, pfW χ R u * (1 / (s - u) + 1 / (s + u - 1)) := by
    show (∑ᶠ u : ℂ, pfW χ R u * (1 / (s - u) + 1 / (s + u - 1))) = _
    rw [finsum_eq_sum_of_support_subset _ (s := S) (fun u hu => ?_)]
    simp only [Function.mem_support] at hu
    exact key u (mul_ne_zero_iff.mp hu).1
  rw [h1, h2, h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hker : (1 : ℂ) / ((1 - s) - u) = -(1 / (s + u - 1)) := by
    rw [show (1 : ℂ) - s - u = -(s + u - 1) by ring, div_neg]
  rw [hker]
  ring

/-- The symmetric partial-fraction sum expanded over the finite support of the divisor. -/
private lemma pfSym_eq_sum (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R : ℝ) (s : ℂ) :
    pfSym χ R s = ∑ u ∈ (pf_support_finite χ hχ R).toFinset,
      pfW χ R u * (1 / (s - u) + 1 / (s + u - 1)) := by
  classical
  have hS := pf_support_finite χ hχ R
  let S : Finset ℂ := hS.toFinset
  have hmem : ∀ u : ℂ, u ∈ S ↔
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
    intro u
    simp [S, Set.Finite.mem_toFinset]
  have key : ∀ u : ℂ, pfW χ R u ≠ 0 → u ∈ S := by
    intro u hu'
    exact (hmem u).mpr (by
      simp only [pfW] at hu'
      intro h
      exact hu' (by rw [h]; simp))
  show (∑ᶠ u : ℂ, pfW χ R u * (1 / (s - u) + 1 / (s + u - 1))) = _
  rw [finsum_eq_sum_of_support_subset _ (s := S) (fun u hu => ?_)]
  simp only [Function.mem_support] at hu
  exact key u (mul_ne_zero_iff.mp hu).1


/-- `Λ(χ⁻¹)` does not vanish at a real point `σ > 1`. -/
private lemma completedLFunction_inv_ne_zero_of_one_lt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) :
    completedLFunction χ⁻¹ (σ : ℂ) ≠ 0 := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
      _ = 1 := by simp
  intro hz
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ⁻¹ hχinv
    (Commons.NumberTheory.DirichletCharacter.isPrimitive_inv hχprim) hz
  have hre : (σ : ℂ).re = σ := rfl
  rw [hre] at hstrip
  linarith [hstrip.1]

/-- `Λ(χ)` does not vanish at a real point `σ > 1`. -/
private lemma completedLFunction_ne_zero_of_one_lt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) :
    completedLFunction χ (σ : ℂ) ≠ 0 := by
  intro hz
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz
  have hre : (σ : ℂ).re = σ := rfl
  rw [hre] at hstrip
  linarith [hstrip.1]

/-- The functional equation, in logarithmic-derivative form, at the real point `1 - σ`. -/
private lemma logDeriv_completed_fe_real {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) :
    logDeriv (completedLFunction χ) (1 - (σ : ℂ)) =
      -((Real.log N : ℝ) : ℂ) - (starRingEnd ℂ) (logDeriv (completedLFunction χ) (σ : ℂ)) := by
  have hΛ1σ : completedLFunction χ (1 - (σ : ℂ)) ≠ 0 := by
    intro hz
    have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz
    have hre : (1 - (σ : ℂ)).re = 1 - σ := by simp
    rw [hre] at hstrip
    linarith [hstrip.1]
  have hinv := completedLFunction_inv_ne_zero_of_one_lt hχ hχprim hσ
  have h1 := completedLogDeriv_fe χ hχprim (1 - (σ : ℂ)) hΛ1σ (by simpa using hinv)
  rw [show (1 : ℂ) - (1 - (σ : ℂ)) = (σ : ℂ) by ring] at h1
  rw [h1]
  congr 1
  have h2 := logDeriv_starComp (f := completedLFunction χ)
    (differentiable_completedLFunction hχ) (σ : ℂ)
  rw [starComp_completedLFunction_eq χ hχ] at h2
  have hconj : ((starRingEnd ℂ) (σ : ℂ)) = (σ : ℂ) := by simp
  rw [hconj] at h2
  exact h2

/-- **Symmetric form of the Hadamard partial fraction, as a limit.**  For primitive non-trivial
`χ` and real `σ > 1`, the symmetric divisor sums converge to
`2 Re((Λ'/Λ)(σ)) + log N`. -/
private lemma tendsto_pfSym_re (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun R : ℝ => (pfSym χ R (σ : ℂ)).re) atTop
      (𝓝 (2 * (logDeriv (completedLFunction χ) (σ : ℂ)).re + Real.log N)) := by
  have hΛσ := completedLFunction_ne_zero_of_one_lt hχ hχprim hσ
  have hΛ1σ : completedLFunction χ (1 - (σ : ℂ)) ≠ 0 := by
    intro hz
    have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz
    have hre : (1 - (σ : ℂ)).re = 1 - σ := by simp
    rw [hre] at hstrip
    linarith [hstrip.1]
  have h1 : Tendsto (fun R : ℝ => pfSum χ R (σ : ℂ)) atTop
      (𝓝 (logDeriv (completedLFunction χ) (σ : ℂ) -
        logDeriv (completedLFunction χ) 0)) := by
    have h := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim (σ : ℂ) hΛσ
    simpa only [pfSum, pfW, logDeriv_apply] using h
  have h2 : Tendsto (fun R : ℝ => pfSum χ R (1 - (σ : ℂ))) atTop
      (𝓝 (logDeriv (completedLFunction χ) (1 - (σ : ℂ)) -
        logDeriv (completedLFunction χ) 0)) := by
    have h := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim (1 - (σ : ℂ)) hΛ1σ
    simpa only [pfSum, pfW, logDeriv_apply] using h
  have hsub : Tendsto (fun R : ℝ => pfSum χ R (σ : ℂ) - pfSum χ R (1 - (σ : ℂ))) atTop
      (𝓝 (logDeriv (completedLFunction χ) (σ : ℂ) -
        logDeriv (completedLFunction χ) (1 - (σ : ℂ)))) := by
    have h := h1.sub h2
    have heq : logDeriv (completedLFunction χ) (σ : ℂ) -
        logDeriv (completedLFunction χ) 0 -
          (logDeriv (completedLFunction χ) (1 - (σ : ℂ)) -
            logDeriv (completedLFunction χ) 0) =
        logDeriv (completedLFunction χ) (σ : ℂ) -
          logDeriv (completedLFunction χ) (1 - (σ : ℂ)) := by ring
    rwa [heq] at h
  have hfun : (fun R : ℝ => pfSum χ R (σ : ℂ) - pfSum χ R (1 - (σ : ℂ))) =
      fun R : ℝ => pfSym χ R (σ : ℂ) := by
    funext R
    exact pf_diff χ hχ R (σ : ℂ)
  rw [hfun] at hsub
  have hlim := (Complex.continuous_re.tendsto _).comp hsub
  have hval : (logDeriv (completedLFunction χ) (σ : ℂ) -
      logDeriv (completedLFunction χ) (1 - (σ : ℂ))).re =
      2 * (logDeriv (completedLFunction χ) (σ : ℂ)).re + Real.log N := by
    have hfe := logDeriv_completed_fe_real hχ hχprim hσ
    have hconjre : ((starRingEnd ℂ) (logDeriv (completedLFunction χ) (σ : ℂ))).re =
        (logDeriv (completedLFunction χ) (σ : ℂ)).re := by simp
    rw [hfe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, hconjre]
    ring
  rw [hval] at hlim
  exact hlim

/-- Nonnegativity of an individual symmetric partial-fraction summand, for `σ > 1`. -/
private lemma pfSym_term_re_nonneg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) {R : ℝ} {u : ℂ}
    (hu : u ∈ (pf_support_finite χ hχ R).toFinset) :
    0 ≤ (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re := by
  have hS := pf_support_finite χ hχ R
  have hmem : ∀ u : ℂ, u ∈ hS.toFinset ↔
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
    intro u
    simp [Set.Finite.mem_toFinset]
  have hdu : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 :=
    (hmem u).mp hu
  have hAn : AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall (0:ℂ) R) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  have hzu : completedLFunction χ u = 0 :=
    Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn hdu
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hzu
  have hdnn : (0 : ℝ) ≤
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) :=
    Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn u
  have hWre : (pfW χ R u).re =
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) := by
    simp [pfW]
  have hWim : (pfW χ R u).im = 0 := by simp [pfW]
  rw [Complex.mul_re, hWre, hWim, zero_mul, sub_zero]
  refine mul_nonneg hdnn ?_
  rw [Complex.add_re]
  refine add_nonneg ?_ ?_
  · rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re]
    simp only [Complex.ofReal_re]
    linarith [hstrip.2]
  · rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, Complex.add_re]
    simp only [Complex.ofReal_re, Complex.one_re]
    linarith [hstrip.1]

/-- Lower bound for the symmetric partial-fraction summand belonging to a real zero `β`. -/
private lemma pfSym_term_re_ge_at (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {σ : ℝ} (hσ : 1 < σ) {R : ℝ} (hR : 2 ≤ R) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hz : completedLFunction χ (β : ℂ) = 0) :
    1 / (σ - β) + 1 / (σ + β - 1) ≤
      (pfW χ R (β : ℂ) * (1 / ((σ : ℂ) - (β : ℂ)) + 1 / ((σ : ℂ) + (β : ℂ) - 1))).re := by
  have hS := pf_support_finite χ hχ R
  have hmem : ∀ u : ℂ, u ∈ hS.toFinset ↔
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
    intro u
    simp [Set.Finite.mem_toFinset]
  have hΛne : completedLFunction χ ≠ 0 := fun h => by
    have h0 := Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
    rw [h] at h0
    exact h0 rfl
  have hβball : (β : ℂ) ∈ Metric.closedBall (0:ℂ) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hβ0]
    linarith
  have hdβ : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) (β : ℂ) ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
      (differentiable_completedLFunction hχ) hΛne hβball hz
  have hdβ1 : (1 : ℝ) ≤
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) := by
    have hAn : AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall (0:ℂ) R) :=
      fun z _ => (differentiable_completedLFunction hχ).analyticAt z
    have hnn : (0 : ℝ) ≤
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) :=
      Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn (β : ℂ)
    have hne : (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) ≠ 0 := by
      intro h0
      exact hdβ (by exact_mod_cast h0)
    have hpos : 0 < (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) := lt_of_le_of_ne hnn (Ne.symm hne)
    have h2 : (1 : ℤ) ≤ MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall (0:ℂ) R) (β : ℂ) := by exact_mod_cast hpos
    exact_mod_cast h2
  have hWre : (pfW χ R (β : ℂ)).re =
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) := by
    simp [pfW]
  have hWim : (pfW χ R (β : ℂ)).im = 0 := by simp [pfW]
  have hkey : (1 / ((σ : ℂ) - (β : ℂ)) + 1 / ((σ : ℂ) + (β : ℂ) - 1)).re =
      1 / (σ - β) + 1 / (σ + β - 1) := by
    have e1 : (σ : ℂ) - (β : ℂ) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
    have e2 : (σ : ℂ) + (β : ℂ) - 1 = ((σ + β - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.add_re, one_div, one_div, Complex.inv_re, Complex.inv_re,
      Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_re]
    have h1 : (σ - β) ≠ 0 := by linarith
    have h2 : (σ + β - 1) ≠ 0 := by linarith
    field_simp
  have hpos1 : 0 < 1 / (σ - β) + 1 / (σ + β - 1) := by
    have h1 : 0 < σ - β := by linarith
    have h2 : 0 < σ + β - 1 := by linarith
    have := one_div_pos.mpr h1
    have := one_div_pos.mpr h2
    linarith
  rw [Complex.mul_re, hWre, hWim, zero_mul, sub_zero, hkey]
  have hle : (1 : ℝ) * (1 / (σ - β) + 1 / (σ + β - 1))
      ≤ (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall (0:ℂ) R)) (β : ℂ) : ℤ) : ℝ) * (1 / (σ - β) + 1 / (σ + β - 1)) :=
    mul_le_mul_of_nonneg_right hdβ1 hpos1.le
  simpa using hle


/-- **Lower bound for `Re((Λ'/Λ)(σ))` on the real axis.**  For a primitive non-trivial `χ` and
`σ > 1`, `Re((Λ'/Λ)(σ)) ≥ -(1/2) log N`. -/
lemma completedLogDeriv_re_ge_neg_half_log (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∀ σ : ℝ, 1 < σ → -(1 / 2) * Real.log N ≤
      (logDeriv (completedLFunction χ) (σ : ℂ)).re := by
  intro σ hσ
  have hlim := tendsto_pfSym_re χ hχ hχprim hσ
  have hterm : ∀ R : ℝ, (0 : ℝ) ≤ (pfSym χ R (σ : ℂ)).re := by
    intro R
    rw [pfSym_eq_sum χ hχ R (σ : ℂ), re_finset_sum]
    exact Finset.sum_nonneg (fun u hu => pfSym_term_re_nonneg χ hχ hχprim hσ hu)
  have h0 : (0 : ℝ) ≤ 2 * (logDeriv (completedLFunction χ) (σ : ℂ)).re + Real.log N :=
    isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hterm)
  linarith

/-- The reflection of a real zero: if `L(β,χ) = 0` with `0 < β < 1`, then `L(1-β,χ) = 0`.
This follows from the functional equation and the conjugation symmetry of the completed
`L`-function. -/
private lemma LFunction_zero_of_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hz : LFunction χ (β : ℂ) = 0) : LFunction χ (((1 - β : ℝ)) : ℂ) = 0 := by
  have hΛβ : completedLFunction χ (β : ℂ) = 0 := by
    have hfac := Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (β : ℂ)) (by simpa using hβ0)
    rw [hfac, hz, zero_mul]
  have hΛinvβ : completedLFunction χ⁻¹ (β : ℂ) = 0 := by
    have h2 := starComp_completedLFunction_eq χ hχ
    have h3 := congrFun h2 (β : ℂ)
    simp only [Commons.NumberTheory.DirichletCharacter.starComp] at h3
    rw [← h3]
    simp [hΛβ]
  have hΛ1β : completedLFunction χ (1 - (β : ℂ)) = 0 := by
    have hfe := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχprim (β : ℂ)
    rw [hfe, hΛinvβ, mul_zero]
  have h1β : (((1 - β : ℝ)) : ℂ) = 1 - (β : ℂ) := by push_cast; ring
  rw [h1β]
  have hγ : gammaFactor χ (1 - (β : ℂ)) ≠ 0 := by
    apply Commons.NumberTheory.DirichletCharacter.gammaFactor_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (1 - (β : ℂ))
    (Or.inl (by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith))
  rw [hL, hΛ1β, zero_div]

/-- **Pole bound for `Re((Λ'/Λ)(σ))` above a real zero.**  For a primitive non-trivial `χ` with a
real zero `β ∈ (0,1)` of `L(·,χ)` and `1 < σ`, `Re((Λ'/Λ)(σ)) ≥ 1/(σ-β) - (1/2) log N`. -/
lemma completedLogDeriv_re_ge_pole (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hz : LFunction χ (β : ℂ) = 0) :
    ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 / (σ - β) - (1 / 2) * Real.log N ≤
      (logDeriv (completedLFunction χ) (σ : ℂ)).re := by
  have hΛβ : completedLFunction χ (β : ℂ) = 0 := by
    have hfac := Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (β : ℂ)) (by simpa using hβ0)
    rw [hfac, hz, zero_mul]
  have h1β : (((1 - β : ℝ)) : ℂ) = 1 - (β : ℂ) := by push_cast; ring
  have hL1β : LFunction χ (1 - (β : ℂ)) = 0 := by
    rw [← h1β]
    exact LFunction_zero_of_one_sub hχ hχprim hβ0 hβ1 hz
  have hΛ1β : completedLFunction χ (((1 - β : ℝ)) : ℂ) = 0 := by
    rw [h1β]
    have hfac := Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (1 - (β : ℂ))) (by simp; linarith)
    rw [hfac, hL1β, zero_mul]
  intro σ hσ _
  have hlim := tendsto_pfSym_re χ hχ hχprim hσ
  have hbound : ∀ R : ℝ, 2 ≤ R → 2 / (σ - β) ≤ (pfSym χ R (σ : ℂ)).re := by
    intro R hR
    rw [pfSym_eq_sum χ hχ R (σ : ℂ), re_finset_sum]
    have hmem : ∀ u : ℂ, u ∈ (pf_support_finite χ hχ R).toFinset ↔
        MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
      intro u
      simp [Set.Finite.mem_toFinset]
    have hΛne : completedLFunction χ ≠ 0 := fun h => by
      have h0 := Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
      rw [h] at h0
      exact h0 rfl
    have hmemβ : (β : ℂ) ∈ (pf_support_finite χ hχ R).toFinset := by
      refine (hmem _).mpr ?_
      refine Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
        (differentiable_completedLFunction hχ) hΛne ?_ hΛβ
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hβ0]
      linarith
    have hmem1β : (((1 - β : ℝ)) : ℂ) ∈ (pf_support_finite χ hχ R).toFinset := by
      refine (hmem _).mpr ?_
      refine Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero
        (differentiable_completedLFunction hχ) hΛne ?_ hΛ1β
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - β)]
      linarith
    have hterm_nonneg : ∀ u ∈ (pf_support_finite χ hχ R).toFinset,
        (0 : ℝ) ≤ (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re :=
      fun u hu => pfSym_term_re_nonneg χ hχ hχprim hσ hu
    by_cases hβhalf : β = 1 / 2
    · have hsingle := Finset.single_le_sum
        (f := fun u => (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re)
        hterm_nonneg hmemβ
      have hge := pfSym_term_re_ge_at χ hχ hχprim hσ hR hβ0 hβ1 hΛβ
      have h2 : 2 / (σ - β) = 1 / (σ - β) + 1 / (σ + β - 1) := by
        rw [hβhalf]; ring
      rw [h2]
      linarith
    · have hneq : (β : ℂ) ≠ (((1 - β : ℝ)) : ℂ) := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.ofReal_re] at hre
        exact hβhalf (by linarith)
      have hmem1β' : (((1 - β : ℝ)) : ℂ) ∈
          (pf_support_finite χ hχ R).toFinset.erase (β : ℂ) := by
        rw [Finset.mem_erase]
        exact ⟨hneq.symm, hmem1β⟩
      have hsingle := Finset.single_le_sum
        (f := fun u => (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re)
        (fun u hu => hterm_nonneg u (Finset.mem_of_mem_erase hu)) hmem1β'
      have hgeβ := pfSym_term_re_ge_at χ hχ hχprim hσ hR hβ0 hβ1 hΛβ
      have hge1β := pfSym_term_re_ge_at χ hχ hχprim hσ hR
        (by linarith : (0:ℝ) < 1 - β) (by linarith : (1 - β : ℝ) < 1) hΛ1β
      have hsum2 : (2 : ℝ) / (σ - β)
          ≤ (pfW χ R (β : ℂ) * (1 / ((σ : ℂ) - (β : ℂ)) +
              1 / ((σ : ℂ) + (β : ℂ) - 1))).re
            + (pfW χ R (((1 - β : ℝ)) : ℂ) * (1 / ((σ : ℂ) - (((1 - β : ℝ)) : ℂ)) +
              1 / ((σ : ℂ) + (((1 - β : ℝ)) : ℂ) - 1))).re := by
        have h1 := hgeβ
        have h2 := hge1β
        have hrw : 1 / (σ - (1 - β)) + 1 / (σ + (1 - β) - 1) = 1 / (σ + β - 1) + 1 / (σ - β) := by
          ring
        rw [hrw] at h2
        have hpos : 0 < 1 / (σ + β - 1) := by
          apply one_div_pos.mpr; linarith
        have hsum := add_le_add h1 h2
        have h2' : (2 : ℝ) / (σ - β) = 1 / (σ - β) + 1 / (σ - β) := by ring
        rw [h2']
        linarith
      have hsplit0 := Finset.sum_erase_add (s := (pf_support_finite χ hχ R).toFinset)
        (f := fun u => (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re) hmemβ
      have hsplit : (pfW χ R (β : ℂ) * (1 / ((σ : ℂ) - (β : ℂ)) +
            1 / ((σ : ℂ) + (β : ℂ) - 1))).re
            + ∑ u ∈ (pf_support_finite χ hχ R).toFinset.erase (β : ℂ),
              (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re
          = ∑ u ∈ (pf_support_finite χ hχ R).toFinset,
              (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re := by
        rw [← hsplit0]; ring
      calc (2 : ℝ) / (σ - β)
          ≤ (pfW χ R (β : ℂ) * (1 / ((σ : ℂ) - (β : ℂ)) +
              1 / ((σ : ℂ) + (β : ℂ) - 1))).re
            + (pfW χ R (((1 - β : ℝ)) : ℂ) * (1 / ((σ : ℂ) - (((1 - β : ℝ)) : ℂ)) +
              1 / ((σ : ℂ) + (((1 - β : ℝ)) : ℂ) - 1))).re := hsum2
        _ ≤ (pfW χ R (β : ℂ) * (1 / ((σ : ℂ) - (β : ℂ)) +
              1 / ((σ : ℂ) + (β : ℂ) - 1))).re
            + ∑ u ∈ (pf_support_finite χ hχ R).toFinset.erase (β : ℂ),
              (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re :=
              add_le_add (le_refl _) hsingle
        _ = ∑ u ∈ (pf_support_finite χ hχ R).toFinset,
              (pfW χ R u * (1 / ((σ : ℂ) - u) + 1 / ((σ : ℂ) + u - 1))).re := hsplit
  have h2 := isClosed_Ici.mem_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨2, hbound⟩)
  have h2' : 2 * (1 / (σ - β)) ≤ 2 * (logDeriv (completedLFunction χ) (σ : ℂ)).re + Real.log N := by
    have heq : 2 * (1 / (σ - β)) = 2 / (σ - β) := by ring
    rw [heq]; exact h2
  linarith


/-- Bound for the real part of the logarithmic derivative of the Archimedean gamma factor on the
real axis segment `(1, 5/4]` (an absolute constant, independent of `N`). -/
private lemma logDeriv_gammaFactor_re_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ : ℝ),
      1 < σ → σ ≤ 5 / 4 → (logDeriv (gammaFactor χ) (σ : ℂ)).re ≤ C := by
  refine ⟨Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log 2 + 8) + 1, ?_⟩
  intro N _ χ σ hσ hσ5
  have key : ∀ x : ℝ, (1 : ℝ) / 2 ≤ x → x ≤ 16 →
      ‖logDeriv Complex.Gammaℝ (x : ℂ)‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log 2 + 8) := by
    intro x hx1 hx2
    have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le x 0 hx1 hx2
    have h0 : |(0 : ℝ)| = 0 := abs_zero
    rw [h0, show (2:ℝ) + 0 = 2 by norm_num] at h
    rw [show ((x : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) = (x : ℂ) by simp] at h
    exact h
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z
      exact hE.gammaFactor_def z
    rw [hfun]
    refine le_trans (Complex.re_le_norm _) ?_
    refine le_trans (key σ (by linarith) (by linarith)) ?_
    linarith
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      exact hO.gammaFactor_def z
    rw [hfun]
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) (σ : ℂ) =
        logDeriv Complex.Gammaℝ ((σ : ℂ) + 1) := by
      have hs1 : 0 < ((σ : ℂ) + 1).re := by
        rw [Complex.add_re]; simp; linarith
      have hf := Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ ((σ : ℂ) + 1) hs1
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) (σ : ℂ) := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := (σ : ℂ)) hf hg
      have hder : deriv (fun z : ℂ => z + 1) (σ : ℂ) = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    rw [hldcomp]
    have hcast : (((σ + 1 : ℝ)) : ℂ) = (σ : ℂ) + 1 := by push_cast; ring
    rw [← hcast]
    refine le_trans (Complex.re_le_norm _) ?_
    refine le_trans (key (σ + 1) (by linarith) (by linarith)) ?_
    linarith

/-- **Uniform lower bound for `Re(L'/L)` on the real axis.**  For a primitive non-trivial `χ`
modulo `N` and `1 < σ ≤ 5/4`, `Re(L'/L)(σ,χ) ≥ -C (log (2N) + 1)` with an absolute `C`. -/
lemma logDeriv_LFunction_re_lower_of_primitive :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive → ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
      -C * (Real.log (2 * (N : ℝ)) + 1) ≤ (logDeriv (LFunction χ) (σ : ℂ)).re := by
  obtain ⟨Cγ, hCγ⟩ := logDeriv_gammaFactor_re_le
  refine ⟨max Cγ (1 / 2) + 1, by positivity, ?_⟩
  intro N _ χ hχ hχprim σ hσ hσ5
  set C : ℝ := max Cγ (1 / 2) + 1 with hCdef
  have hCγ' : Cγ ≤ C := by
    have : Cγ ≤ max Cγ (1 / 2) := le_max_left _ _
    rw [hCdef]; linarith
  have hChalf : (1 / 2 : ℝ) ≤ C := by
    have : (1 / 2 : ℝ) ≤ max Cγ (1 / 2) := le_max_right _ _
    rw [hCdef]; linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog2N : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg; nlinarith
  have hlogle : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by linarith); nlinarith
  have hsre : 0 < (σ : ℂ).re := by simp; linarith
  have hLne : LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ (σ : ℂ) hsre hLne
  have hA := completedLogDeriv_re_ge_neg_half_log χ hχ hχprim σ hσ
  have hγ := hCγ N χ σ hσ hσ5
  have hre : (logDeriv (LFunction χ) (σ : ℂ)).re =
      (logDeriv (completedLFunction χ) (σ : ℂ)).re -
        (logDeriv (gammaFactor χ) (σ : ℂ)).re := by
    rw [hdec, Complex.add_re]; ring
  rw [hre]
  have hprod : (1 / 2 : ℝ) * Real.log (2 * (N : ℝ)) ≤ C * Real.log (2 * (N : ℝ)) :=
    mul_le_mul_of_nonneg_right hChalf hlog2N
  nlinarith [hA, hγ, hprod, hlogle, hCγ', hCγ, hChalf]

/-- **Pole bound for `Re(L'/L)` above a real zero.**  For a primitive non-trivial `χ` with a real
zero `β ∈ (0,1)` of `L(·,χ)` and `1 < σ ≤ 5/4`,
`Re(L'/L)(σ,χ) ≥ 1/(σ-β) - C (log (2N) + 1)` with an absolute `C`. -/
lemma logDeriv_LFunction_re_pole_of_real_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive → ∀ β : ℝ, 0 < β → β < 1 → LFunction χ (β : ℂ) = 0 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
      1 / (σ - β) - C * (Real.log (2 * (N : ℝ)) + 1) ≤
        (logDeriv (LFunction χ) (σ : ℂ)).re := by
  obtain ⟨Cγ, hCγ⟩ := logDeriv_gammaFactor_re_le
  refine ⟨max Cγ (1 / 2) + 1, by positivity, ?_⟩
  intro N _ χ hχ hχprim β hβ0 hβ1 hz σ hσ hσ5
  set C : ℝ := max Cγ (1 / 2) + 1 with hCdef
  have hCγ' : Cγ ≤ C := by
    have : Cγ ≤ max Cγ (1 / 2) := le_max_left _ _
    rw [hCdef]; linarith
  have hChalf : (1 / 2 : ℝ) ≤ C := by
    have : (1 / 2 : ℝ) ≤ max Cγ (1 / 2) := le_max_right _ _
    rw [hCdef]; linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog2N : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg; nlinarith
  have hlogle : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by linarith); nlinarith
  have hsre : 0 < (σ : ℂ).re := by simp; linarith
  have hLne : LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ (σ : ℂ) hsre hLne
  have hA := completedLogDeriv_re_ge_pole χ hχ hχprim hβ0 hβ1 hz σ hσ hσ5
  have hγ := hCγ N χ σ hσ hσ5
  have hre : (logDeriv (LFunction χ) (σ : ℂ)).re =
      (logDeriv (completedLFunction χ) (σ : ℂ)).re -
        (logDeriv (gammaFactor χ) (σ : ℂ)).re := by
    rw [hdec, Complex.add_re]; ring
  rw [hre]
  have hprod : (1 / 2 : ℝ) * Real.log (2 * (N : ℝ)) ≤ C * Real.log (2 * (N : ℝ)) :=
    mul_le_mul_of_nonneg_right hChalf hlog2N
  nlinarith [hA, hγ, hprod, hlogle, hCγ', hCγ, hChalf]


/-! ## The `3-4-1` inequality on the real axis -/

/-- Pointwise positivity: `3 + 4 Re z + Re z² = 2 (1 + Re z)² ≥ 0` for `‖z‖ ≤ 1`. -/
private lemma pointwise_341 (z : ℂ) (hz : ‖z‖ ≤ 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [sq_nonneg (z.re + 1), norm_nonneg z, hsq, hnorm]

/-- Summability of the twisted von Mangoldt series on `Re s > 1`. -/
private lemma summable_twist_vonMangoldt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Summable (LSeries.term (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod N) : ℂ)) s) := by
  have hbase : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re) :=
    Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hs
  refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hbase)
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · rw [hn]
    have hz : (0 : ℝ) ^ s.re = 0 := Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hs))
    simp [hz]
  · rw [if_neg hn]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [norm_mul]
    calc ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * ‖(χ (n : ZMod N) : ℂ)‖
        = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (by simpa using χ.norm_le_one (n : ZMod N))
            ArithmeticFunction.vonMangoldt_nonneg
      _ = (ArithmeticFunction.vonMangoldt n : ℝ) := by ring

/-- The product of the three `LSeries` terms at a single index. -/
private lemma term_341_realAxis (χ : DirichletCharacter ℂ N) {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    3 * LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n
      + 4 * LSeries.term (fun m : ℕ =>
            (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod N) : ℂ)) (σ : ℂ) n
      + LSeries.term (fun m : ℕ =>
            (ArithmeticFunction.vonMangoldt m : ℂ) * ((χ * χ) (m : ZMod N) : ℂ)) (σ : ℂ) n
      = ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))) *
          (3 + 4 * ((χ (n : ZMod N) : ℂ)) + ((χ (n : ZMod N) : ℂ)) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term, if_neg hn0, LSeries.term, if_neg hn0, LSeries.term, if_neg hn0]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← Complex.cpow_neg]
  have hsq : ((χ * χ) (n : ZMod N) : ℂ) = (χ (n : ZMod N) : ℂ) * (χ (n : ZMod N) : ℂ) := by
    rw [MulChar.mul_apply]
  rw [hsq]
  ring

private lemma re_mul_real (a r : ℝ) (z : ℂ) : (((a : ℂ) * (r : ℂ)) * z).re = a * r * z.re := by
  rw [Complex.mul_re]
  simp

private lemma re_comb_three (z0 z1 z2 : ℂ) :
    (3 * z0 + 4 * z1 + z2).re = 3 * z0.re + 4 * z1.re + z2.re := by
  simp [Complex.add_re, Complex.mul_re]

private lemma re_341_comb (w : ℂ) : (3 + 4 * w + w ^ 2).re = 3 + 4 * w.re + (w ^ 2).re := by
  simp [Complex.add_re, Complex.mul_re]

/-- **The `3-4-1` inequality on the real axis.**  For every Dirichlet character `χ` modulo `N`
and every real `σ > 1`,

`3·Re(−ζ′/ζ)(σ) + 4·Re(−(L′/L)(σ,χ)) + Re(−(L′/L)(σ,χ²)) ≥ 0`. -/
lemma logDeriv_re_341_realAxis (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * ((-deriv riemannZeta (σ : ℂ)) / riemannZeta (σ : ℂ)).re
      + 4 * ((-deriv (LFunction χ) (σ : ℂ)) / (LFunction χ (σ : ℂ))).re
      + ((-deriv (LFunction (χ * χ)) (σ : ℂ)) / (LFunction (χ * χ) (σ : ℂ))).re := by
  have hσ0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have e0 : (-deriv riemannZeta (σ : ℂ)) / riemannZeta (σ : ℂ) =
      LSeries (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) := by
    have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (σ : ℂ)) hσ0
    rw [h, neg_div]
  have e1 : (-deriv (LFunction χ) (σ : ℂ)) / (LFunction χ (σ : ℂ)) =
      LSeries (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) *
        (χ (m : ZMod N) : ℂ)) (σ : ℂ) := by
    have h := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ
      (s := (σ : ℂ)) hσ0
    rw [logDeriv_apply] at h
    rw [show (-deriv (LFunction χ) (σ : ℂ)) / (LFunction χ (σ : ℂ)) =
        -(deriv (LFunction χ) (σ : ℂ) / (LFunction χ (σ : ℂ))) by rw [neg_div], h, neg_neg]
  have e2 : (-deriv (LFunction (χ * χ)) (σ : ℂ)) / (LFunction (χ * χ) (σ : ℂ)) =
      LSeries (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) *
        ((χ * χ) (m : ZMod N) : ℂ)) (σ : ℂ) := by
    have h := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
      (χ * χ) (s := (σ : ℂ)) hσ0
    rw [logDeriv_apply] at h
    rw [show (-deriv (LFunction (χ * χ)) (σ : ℂ)) / (LFunction (χ * χ) (σ : ℂ)) =
        -(deriv (LFunction (χ * χ)) (σ : ℂ) / (LFunction (χ * χ) (σ : ℂ))) by rw [neg_div], h, neg_neg]
  have hsum0 : Summable (LSeries.term (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ)) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ0
    simpa [LSeriesSummable] using h
  have hsum1 := summable_twist_vonMangoldt χ (s := (σ : ℂ)) hσ0
  have hsum2 := summable_twist_vonMangoldt (χ * χ) (s := (σ : ℂ)) hσ0
  have hr0 : Summable (fun n : ℕ => (LSeries.term (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n).re) :=
    hsum0.map Complex.reCLM Complex.continuous_re
  have hr1 : Summable (fun n : ℕ => (LSeries.term (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod N) : ℂ)) (σ : ℂ) n).re) :=
    hsum1.map Complex.reCLM Complex.continuous_re
  have hr2 : Summable (fun n : ℕ => (LSeries.term (fun m : ℕ =>
      (ArithmeticFunction.vonMangoldt m : ℂ) * ((χ * χ) (m : ZMod N) : ℂ)) (σ : ℂ) n).re) :=
    hsum2.map Complex.reCLM Complex.continuous_re
  rw [e0, e1, e2]
  simp only [LSeries]
  rw [Complex.re_tsum hsum0, Complex.re_tsum hsum1, Complex.re_tsum hsum2]
  have hkey : 3 * (∑' n : ℕ, (LSeries.term (fun m : ℕ =>
        (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n).re)
      + 4 * (∑' n : ℕ, (LSeries.term (fun m : ℕ =>
        (ArithmeticFunction.vonMangoldt m : ℂ) * (χ (m : ZMod N) : ℂ)) (σ : ℂ) n).re)
      + (∑' n : ℕ, (LSeries.term (fun m : ℕ =>
        (ArithmeticFunction.vonMangoldt m : ℂ) * ((χ * χ) (m : ZMod N) : ℂ)) (σ : ℂ) n).re)
      = ∑' n : ℕ, (3 * LSeries.term (fun m : ℕ =>
            (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n
        + 4 * LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) *
            (χ (m : ZMod N) : ℂ)) (σ : ℂ) n
        + LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ) *
            ((χ * χ) (m : ZMod N) : ℂ)) (σ : ℂ) n).re := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    rw [← (hr0.mul_left 3).tsum_add (hr1.mul_left 4),
      ← ((hr0.mul_left 3).add (hr1.mul_left 4)).tsum_add hr2]
    apply tsum_congr
    intro n
    rw [re_comb_three]
  rw [hkey]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term]
  · have hn1 : 1 ≤ n := by omega
    rw [term_341_realAxis χ hn1]
    have hcast : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      norm_num
    rw [hcast, re_mul_real, re_341_comb]
    have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) :=
      le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
    have h3 := pointwise_341 ((χ (n : ZMod N) : ℂ))
      (by simpa using χ.norm_le_one (n : ZMod N))
    exact mul_nonneg (mul_nonneg h1 h2) h3


/-! ## The imprimitive lower bound -/

/-- Bound for the logarithmic derivative of a single Euler factor `1 - c p^{-s}` on `σ ≥ 1`. -/
private lemma logDeriv_factor_re_ge {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    -(Real.log p) ≤ (logDeriv (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) (σ : ℂ)).re := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hppos : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpc : (p : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hp.ne_zero
  have hneg : DifferentiableAt ℂ (fun s : ℂ => -s) (σ : ℂ) := differentiableAt_id.neg
  set a : ℝ := (p : ℝ) ^ (-σ) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hppos _
  have hahalf : a ≤ 1 / 2 := by
    rw [ha, Real.rpow_neg hppos.le]
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ σ := by
      calc (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
        _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (p : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hp1 hσ
    have h3 : 0 < (p : ℝ) ^ σ := Real.rpow_pos_of_pos hppos _
    rw [inv_le_comm₀ h3 (by norm_num)]
    linarith
  have hcast : (p : ℂ) ^ (-(σ : ℂ)) = ((a : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow (Nat.cast_nonneg p) (-σ)
    have hexp : ((-σ : ℝ) : ℂ) = -(σ : ℂ) := by push_cast; ring
    rw [hexp] at h
    rw [ha]
    exact h.symm
  have hdiff1 : DifferentiableAt ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) (σ : ℂ) :=
    DifferentiableAt.const_cpow (f := fun s : ℂ => -s) hneg (Or.inl hpc)
  have hderiv : deriv (fun s : ℂ => c * (p : ℂ) ^ (-s)) (σ : ℂ) =
      -(c * ((Real.log p : ℝ) : ℂ) * ((a : ℝ) : ℂ)) := by
    rw [deriv_const_mul _ hdiff1]
    have h := Complex.deriv_const_cpow (f := fun s : ℂ => -s) hneg (c := (p : ℂ))
    have h' : deriv (fun s : ℂ => (p : ℂ) ^ (-s)) (σ : ℂ) =
        Complex.log (p : ℂ) * deriv (fun s : ℂ => -s) (σ : ℂ) * (p : ℂ) ^ (-(σ : ℂ)) := h
    rw [h']
    have hder : deriv (fun s : ℂ => -s) (σ : ℂ) = -1 := by simp
    rw [hder, hcast]
    have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) :=
      (Complex.ofReal_log (x := (p : ℝ)) (le_of_lt hppos)).symm
    rw [hlog]
    ring
  have hval : logDeriv (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) (σ : ℂ) =
      (c * ((Real.log p : ℝ) : ℂ) * ((a : ℝ) : ℂ)) / (1 - c * ((a : ℝ) : ℂ)) := by
    rw [logDeriv_apply, deriv_const_sub, hderiv, hcast]
    rw [neg_neg]
  have hca : ‖c * ((a : ℝ) : ℂ)‖ ≤ a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hapos]
    calc ‖c‖ * a ≤ 1 * a := mul_le_mul_of_nonneg_right hc hapos.le
      _ = a := one_mul a
  have hden_le : (1 : ℝ) - a ≤ ‖(1 : ℂ) - c * ((a : ℝ) : ℂ)‖ := by
    have h5 : ‖(1 : ℂ)‖ - ‖c * ((a : ℝ) : ℂ)‖ ≤
        |‖(1 : ℂ)‖ - ‖c * ((a : ℝ) : ℂ)‖| := le_abs_self _
    calc (1 : ℝ) - a ≤ ‖(1 : ℂ)‖ - ‖c * ((a : ℝ) : ℂ)‖ := by rw [norm_one]; linarith
      _ ≤ _ := h5
      _ ≤ ‖(1 : ℂ) - c * ((a : ℝ) : ℂ)‖ := abs_norm_sub_norm_le _ _
  have hden_pos : 0 < 1 - a := by linarith
  have hden_ne : (1 - c * ((a : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have h1 : c * ((a : ℝ) : ℂ) = 1 := (sub_eq_zero.mp h).symm
    have h2 : ‖c * ((a : ℝ) : ℂ)‖ = 1 := by rw [h1]; simp
    linarith [hahalf, hca, h2]
  have hnorm : ‖logDeriv (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) (σ : ℂ)‖ ≤
      (Real.log p) * a / (1 - a) := by
    rw [hval]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp,
      abs_of_pos hapos]
    refine div_le_div₀ (mul_nonneg hlogp hapos.le) ?_ hden_pos hden_le
    calc ‖c‖ * Real.log (p : ℝ) * a ≤ 1 * Real.log (p : ℝ) * a := by
          apply mul_le_mul_of_nonneg_right _ hapos.le
          exact mul_le_mul_of_nonneg_right hc hlogp
      _ = Real.log (p : ℝ) * a := by ring
  have hstep : -(Real.log p) ≤ -(Real.log p * a / (1 - a)) := by
    have h1 : a / (1 - a) ≤ 1 := by rw [div_le_one hden_pos]; linarith
    have h2 : Real.log (p : ℝ) * (a / (1 - a)) ≤ Real.log (p : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 hlogp
    have h3 : Real.log (p : ℝ) * a / (1 - a) = Real.log (p : ℝ) * (a / (1 - a)) := by ring
    rw [h3]
    linarith
  calc -(Real.log p) ≤ -(Real.log p * a / (1 - a)) := hstep
    _ ≤ (logDeriv (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) (σ : ℂ)).re := by
        have h := Complex.abs_re_le_norm (logDeriv (fun s : ℂ => 1 - c * (p : ℂ) ^ (-s)) (σ : ℂ))
        rw [abs_le] at h
        linarith [h.1, hnorm]


/-- **Uniform lower bound for `Re(L'/L)` on the real axis, imprimitive case.**  For any
non-principal character `χ` modulo `N` and `1 < σ ≤ 5/4`,
`Re(L'/L)(σ,χ) ≥ -C (log (2N) + 1)` with an absolute `C`. -/
lemma logDeriv_LFunction_re_lower_of_ne_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
      -C * (Real.log (2 * (N : ℝ)) + 1) ≤ (logDeriv (LFunction χ) (σ : ℂ)).re := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := logDeriv_LFunction_re_lower_of_primitive
  refine ⟨C₁ + 2, by positivity, ?_⟩
  intro N _ χ hχ σ hσ hσ5
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := χ), h,
      DirichletCharacter.changeLevel_one]
  have hψ := hC₁ χ.conductor χ.primitiveCharacter hψne χ.primitiveCharacter_isPrimitive σ hσ hσ5
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcle : (χ.conductor : ℝ) ≤ (N : ℝ) := by
    have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ.conductor_dvd_level
    exact_mod_cast h
  have hcondpos : (0 : ℝ) < (χ.conductor : ℝ) := by
    have h : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
    exact_mod_cast h
  have hlogc : Real.log (2 * (χ.conductor : ℝ)) ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by linarith)
    linarith
  have hlog2N : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg; linarith
  have hfun : LFunction χ = fun s : ℂ => LFunction χ.primitiveCharacter s *
      ∏ p ∈ N.primeFactors,
        (1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-s)) := by
    funext s
    have h := DirichletCharacter.LFunction_changeLevel (hMN := χ.conductor_dvd_level)
      (χ := χ.primitiveCharacter) (s := s) (Or.inl hψne)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    exact h
  have hfactor_ne : ∀ p ∈ N.primeFactors,
      (1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-(σ : ℂ))) ≠ 0 := by
    intro p hp
    intro hzero
    have hz : ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-(σ : ℂ)) = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hpc : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have h1 : ‖((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-(σ : ℂ))‖ = 1 := by
      rw [hz]; simp
    have h2 : ‖((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-(σ : ℂ))‖ < 1 := by
      rw [norm_mul]
      have hcp : ‖(((p : ℝ)) : ℂ) ^ (-(σ : ℂ))‖ = (p : ℝ) ^ (-σ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hpc]
        simp
      rw [show ((p : ℂ)) = (((p : ℝ)) : ℂ) by norm_num, hcp]
      have hnorm : ‖((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ))‖ ≤ 1 := by
        simpa using χ.primitiveCharacter.norm_le_one (p : ZMod χ.conductor)
      have hlt : (p : ℝ) ^ (-σ) < 1 := by
        rw [Real.rpow_neg hpc.le]
        have h2 : 1 < (p : ℝ) ^ σ := by
          calc (1:ℝ) < 2 := by norm_num
            _ ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            _ = (p : ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
            _ ≤ (p : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast
                (Nat.prime_of_mem_primeFactors hp).one_le) hσ.le
        rw [inv_lt_one_iff₀]
        exact Or.inr h2
      calc ‖((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ))‖ * (p : ℝ) ^ (-σ)
          ≤ 1 * (p : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hnorm
              (Real.rpow_nonneg hpc.le _)
        _ = (p : ℝ) ^ (-σ) := one_mul _
        _ < 1 := hlt
    linarith
  have hprod_ne : (∏ p ∈ N.primeFactors,
      (1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-(σ : ℂ)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor_ne
  have hψ_ne : LFunction χ.primitiveCharacter (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψne)
      (by simp; linarith)
  have hdiffψ : DifferentiableAt ℂ (LFunction χ.primitiveCharacter) (σ : ℂ) :=
    (DirichletCharacter.differentiable_LFunction hψne) (σ : ℂ)
  have hdiffprod : DifferentiableAt ℂ (fun s : ℂ => ∏ p ∈ N.primeFactors,
      (1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-s))) (σ : ℂ) := by
    refine DifferentiableAt.fun_finsetProd (fun p hp => ?_)
    have hpc : (p : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact ((DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg
      (Or.inl hpc)).const_mul (χ.primitiveCharacter (p : ZMod χ.conductor))).const_sub 1
  have hdec : logDeriv (LFunction χ) (σ : ℂ) =
      logDeriv (LFunction χ.primitiveCharacter) (σ : ℂ) +
        ∑ p ∈ N.primeFactors, logDeriv (fun s : ℂ =>
          1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-s)) (σ : ℂ) := by
    rw [hfun]
    erw [logDeriv_mul _ hψ_ne hprod_ne hdiffψ hdiffprod]
    congr 1
    rw [← Finset.prod_fn]
    rw [logDeriv_prod]
    · intro p hp
      exact hfactor_ne p hp
    · intro p hp
      have hpc : (p : ℂ) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact ((DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg
        (Or.inl hpc)).const_mul (χ.primitiveCharacter (p : ZMod χ.conductor))).const_sub 1
  have hrec : (logDeriv (LFunction χ) (σ : ℂ)).re =
      (logDeriv (LFunction χ.primitiveCharacter) (σ : ℂ)).re +
        ∑ p ∈ N.primeFactors, (logDeriv (fun s : ℂ =>
          1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-s)) (σ : ℂ)).re := by
    rw [hdec, Complex.add_re, re_finset_sum]
  rw [hrec]
  have hsum : -(∑ p ∈ N.primeFactors, Real.log (p : ℝ)) ≤
      ∑ p ∈ N.primeFactors, (logDeriv (fun s : ℂ =>
        1 - ((χ.primitiveCharacter (p : ZMod χ.conductor) : ℂ)) * (p : ℂ) ^ (-s)) (σ : ℂ)).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    exact logDeriv_factor_re_ge (Nat.prime_of_mem_primeFactors hp)
      (by simpa using χ.primitiveCharacter.norm_le_one (p : ZMod χ.conductor)) hσ.le
  have hlogsum : (∑ p ∈ N.primeFactors, Real.log (p : ℝ)) ≤ Real.log (N : ℝ) := by
    have hprod : (∏ p ∈ N.primeFactors, (p : ℝ)) ≤ (N : ℝ) := by
      have hdvd := Nat.prod_primeFactors_dvd N
      have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd
      have h' : ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_prod] at h'
    have hposprod : 0 < ∏ p ∈ N.primeFactors, (p : ℝ) := by
      apply Finset.prod_pos
      intro p hp
      have hp2 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
      exact_mod_cast hp2
    have hlogprod : Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) =
        ∑ p ∈ N.primeFactors, Real.log (p : ℝ) :=
      Real.log_prod (fun p hp => by
        have hp2 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
        exact_mod_cast (ne_of_gt hp2))
    rw [← hlogprod]
    exact Real.log_le_log hposprod hprod
  have hlogNle : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by linarith); linarith
  linarith [hψ, hlogc, hsum, hlogsum, hlog2N, hlogNle, hC₁pos,
    mul_le_mul_of_nonneg_left hlogc hC₁pos.le]

/-! ## The real zero-free region and the main theorem -/

/-- **Real zeros are bounded away from `1` uniformly.**  For a primitive character `χ` modulo `N`
with `χ ≠ 1` and `χ * χ ≠ 1`, every real zero `β ∈ (0,1)` of `L(·,χ)` satisfies
`1 - β ≥ c / log (2N)` for an absolute constant `c > 0`. -/
private lemma real_zero_far_from_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → χ * χ ≠ 1 → ∀ β : ℝ, 0 < β → β < 1 →
      LFunction χ (β : ℂ) = 0 → c / Real.log (2 * (N : ℝ)) ≤ 1 - β := by
  obtain ⟨Cζ, hCζpos, hCζ⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨Cp, hCppos, hCp⟩ := logDeriv_LFunction_re_pole_of_real_zero
  obtain ⟨Cl, hClpos, hCl⟩ := logDeriv_LFunction_re_lower_of_ne_one
  set K : ℝ := Cζ + Cp + Cl + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  refine ⟨1 / (160 * K), by positivity, ?_⟩
  intro N _ χ hχ hχprim hχ2 β hβ0 hβ1 hz
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hLpos : 0 < Real.log (2 * (N : ℝ)) := by
    apply Real.log_pos; linarith
  have hLbig : (11 / 17 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
    have h2 : Real.log 2 ≤ Real.log (2 * (N : ℝ)) := by
      apply Real.log_le_log (by norm_num); nlinarith
    have h9 := Real.log_two_gt_d9
    linarith
  set δ : ℝ := 1 / (16 * K * Real.log (2 * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [hK1, hLbig]
  have hσ1 : 1 < 1 + δ := by linarith
  have hσ5 : 1 + δ ≤ 5 / 4 := by linarith
  have hσ2 : 1 + δ ≤ 2 := by linarith
  have hA := hCζ (1 + δ) hσ1 hσ2
  have hB := hCp N χ hχ hχprim β hβ0 hβ1 hz (1 + δ) hσ1 hσ5
  have hC := hCl N (χ * χ) hχ2 (1 + δ) hσ1 hσ5
  have h341 := logDeriv_re_341_realAxis χ hσ1
  have hA' : ((-deriv riemannZeta ((1 + δ : ℝ) : ℂ)) / riemannZeta ((1 + δ : ℝ) : ℂ)).re ≤
      1 / δ + Cζ := by
    have h := hA
    rw [show (1 + δ) - 1 = δ by ring] at h
    exact h
  have hB' : ((-deriv (LFunction χ) ((1 + δ : ℝ) : ℂ)) / (LFunction χ ((1 + δ : ℝ) : ℂ))).re ≤
      -(1 / ((1 + δ) - β)) + Cp * (Real.log (2 * (N : ℝ)) + 1) := by
    have h1 : ((-deriv (LFunction χ) ((1 + δ : ℝ) : ℂ)) / (LFunction χ ((1 + δ : ℝ) : ℂ))).re =
        -(logDeriv (LFunction χ) ((1 + δ : ℝ) : ℂ)).re := by
      rw [logDeriv_apply, neg_div, Complex.neg_re]
    rw [h1]
    linarith [hB]
  have hC' : ((-deriv (LFunction (χ * χ)) ((1 + δ : ℝ) : ℂ)) /
      (LFunction (χ * χ) ((1 + δ : ℝ) : ℂ))).re ≤
      Cl * (Real.log (2 * (N : ℝ)) + 1) := by
    have h1 : ((-deriv (LFunction (χ * χ)) ((1 + δ : ℝ) : ℂ)) /
        (LFunction (χ * χ) ((1 + δ : ℝ) : ℂ))).re =
        -(logDeriv (LFunction (χ * χ)) ((1 + δ : ℝ) : ℂ)).re := by
      rw [logDeriv_apply, neg_div, Complex.neg_re]
    rw [h1]
    linarith [hC]
  have h4x : (4 : ℝ) / ((1 + δ) - β) = 4 * (1 / ((1 + δ) - β)) := by ring
  have hstep1 : 4 * (1 / ((1 + δ) - β)) ≤
      3 * (1 / δ) + 3 * Cζ + (4 * Cp + Cl) * (Real.log (2 * (N : ℝ)) + 1) := by
    have h := h341
    linarith [hA', hB', hC', h341, h4x]
  have hstep2 : 4 * (1 / ((1 + δ) - β)) ≤
      3 * (1 / δ) + 4 * K * (Real.log (2 * (N : ℝ)) + 1) := by
    have h1 : (3 * Cζ + (4 * Cp + Cl) * (Real.log (2 * (N : ℝ)) + 1)) ≤
        4 * K * (Real.log (2 * (N : ℝ)) + 1) := by
      have hKexp : K = Cζ + Cp + Cl + 1 := hKdef
      have hlog1 : (1 : ℝ) ≤ Real.log (2 * (N : ℝ)) + 1 := by linarith
      nlinarith [hCζpos, hCppos, hClpos, hK1, hlog1]
    linarith [hstep1, h1]
  have hstep3 : 1 / ((1 + δ) - β) ≤
      (3 / 4) * (1 / δ) + K * (Real.log (2 * (N : ℝ)) + 1) := by linarith [hstep2]
  have h3δ : (3 / 4) * (1 / δ) = 12 * K * Real.log (2 * (N : ℝ)) := by
    rw [hδdef]
    field_simp
    ring
  have hstep4 : 1 / ((1 + δ) - β) ≤
      K * (13 * Real.log (2 * (N : ℝ)) + 1) := by
    rw [h3δ] at hstep3
    nlinarith [hstep3, hKpos, hLpos]
  have hXpos : 0 < (1 + δ) - β := by linarith
  have hYpos : 0 < K * (13 * Real.log (2 * (N : ℝ)) + 1) := by positivity
  have hXge : 1 / (K * (13 * Real.log (2 * (N : ℝ)) + 1)) ≤ (1 + δ) - β := by
    have h1 : (1 : ℝ) ≤ (K * (13 * Real.log (2 * (N : ℝ)) + 1)) * ((1 + δ) - β) :=
      (div_le_iff₀ hXpos).mp hstep4
    rw [div_le_iff₀ hYpos]
    linarith [h1]
  have hfinal : 1 / (160 * K * Real.log (2 * (N : ℝ))) ≤ 1 - β := by
    have h2 : (1 : ℝ) - β = ((1 + δ) - β) - δ := by ring
    rw [h2]
    have h3 : 1 / (K * (13 * Real.log (2 * (N : ℝ)) + 1)) - δ ≥
        1 / (160 * K * Real.log (2 * (N : ℝ))) := by
      rw [hδdef, ge_iff_le]
      field_simp
      linarith [hLbig, hKpos]
    linarith [hXge, h3]
  rw [div_div]
  exact hfinal

/-- **Uniform zero-free region of Dirichlet `L`-functions on the real axis.**  There is an
absolute constant `c > 0` such that for every `N ≥ 1`, every primitive character `χ` modulo `N`
with `χ ≠ 1` and `χ * χ ≠ 1`, and every real `σ ≥ 1 - c / log (2N)`, `L(σ,χ) ≠ 0`. -/
theorem LFunction_zeroFree_uniform_realAxis :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ ≠ 1 → ∀ σ : ℝ,
      1 - c / Real.log (2 * (N : ℝ)) ≤ σ →
      DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := real_zero_far_from_one
  set c : ℝ := min (c₀ / 2) (1 / 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact lt_min (by linarith) (by norm_num)
  have hcle : c ≤ c₀ / 2 := by rw [hcdef]; exact min_le_left _ _
  have hcle2 : c ≤ 1 / 2 := by rw [hcdef]; exact min_le_right _ _
  refine ⟨c, hcpos, ?_⟩
  intro N _ χ hχprim hχ hχ2 σ hσ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hℓpos : 0 < Real.log (2 * (N : ℝ)) := by
    apply Real.log_pos; linarith
  have hℓ2 : Real.log 2 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by norm_num); nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hσ1 : (1 : ℝ) ≤ σ
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hσ1)
  · push Not at hσ1
    have hσpos : 0 < σ := by
      have h1ℓ : 1 / Real.log (2 * (N : ℝ)) ≤ 1 / Real.log 2 :=
        one_div_le_one_div_of_le hlog2pos hℓ2
      have h2 : c * (1 / Real.log (2 * (N : ℝ))) ≤ (1 / 2) * (1 / Real.log 2) :=
        mul_le_mul hcle2 h1ℓ (by positivity) (by norm_num)
      have h3 : c / Real.log (2 * (N : ℝ)) = c * (1 / Real.log (2 * (N : ℝ))) := by ring
      have h4 : (1 / 2) * (1 / Real.log 2) = (1 / 2) / Real.log 2 := by ring
      have h5 : (1 : ℝ) < 2 * Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have h6 : (1 / 2) / Real.log 2 < 1 := by
        rw [div_lt_one hlog2pos]; linarith
      linarith [hσ, h3, h2, h4, h6]
    intro hzero
    have hfar := hc₀ N χ hχ hχprim hχ2 σ hσpos hσ1 hzero
    have hle : 1 - σ ≤ c / Real.log (2 * (N : ℝ)) := by linarith [hσ]
    have hmono : c₀ / Real.log (2 * (N : ℝ)) ≤ c / Real.log (2 * (N : ℝ)) :=
      le_trans hfar hle
    have h1 : c₀ ≤ c := by
      have h := (div_le_iff₀ hℓpos).mp hmono
      have h2 : (c / Real.log (2 * (N : ℝ))) * Real.log (2 * (N : ℝ)) = c := by
        field_simp
      linarith [h, h2]
    linarith [h1, hcle, hc₀pos]

end Commons.NumberTheory.DirichletCharacter
