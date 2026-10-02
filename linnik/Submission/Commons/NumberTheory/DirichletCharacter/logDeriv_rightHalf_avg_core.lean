import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_small
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_small
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

open Complex DirichletCharacter Filter
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-- The vertical line `Re = 2` contains no zero of the completed L-function of a primitive
non-trivial character. -/
lemma completedLFunction_ne_zero_re_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
  intro hz
  have hstrip := zerosInStrip χ hχ hχprim ((2 : ℂ) + Complex.I * (T : ℂ)) hz
  have hre : (((2 : ℂ) + Complex.I * (T : ℂ)).re) = 2 := by simp
  have hlt : ((2 : ℂ) + Complex.I * (T : ℂ)).re < 1 := by simpa [hre] using hstrip.2
  norm_num at hlt


/-- The vertical line `Re = -1` contains no zero of the completed L-function of a primitive
non-trivial character. -/
lemma completedLFunction_ne_zero_re_neg_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) :
    DirichletCharacter.completedLFunction χ ((-1 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
  intro hz
  have hstrip := zerosInStrip χ hχ hχprim ((-1 : ℂ) + Complex.I * (T : ℂ)) hz
  have hre : (((-1 : ℂ) + Complex.I * (T : ℂ)).re) = -1 := by simp
  have hgt : (0 : ℝ) < ((-1 : ℂ) + Complex.I * (T : ℂ)).re := by simpa [hre] using hstrip.1
  norm_num at hgt


theorem partialFraction_diff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s s₁ : ℂ)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hs₁ : DirichletCharacter.completedLFunction χ s₁ ≠ 0) :
    Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))
      atTop (nhds (logDeriv (DirichletCharacter.completedLFunction χ) s
        - logDeriv (DirichletCharacter.completedLFunction χ) s₁)) := by
  have h1 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
  have h2 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s₁ hs₁
  have hsub := h1.sub h2
  change Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))
    atTop (nhds (deriv (DirichletCharacter.completedLFunction χ) s /
      DirichletCharacter.completedLFunction χ s -
      deriv (DirichletCharacter.completedLFunction χ) s₁ /
      DirichletCharacter.completedLFunction χ s₁))
  have hgoal : (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0) -
      (deriv (DirichletCharacter.completedLFunction χ) s₁ /
        DirichletCharacter.completedLFunction χ s₁ -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0) =
      deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) s₁ /
        DirichletCharacter.completedLFunction χ s₁ := by ring
  rw [← hgoal]
  refine hsub.congr' ?_
  filter_upwards with R
  have hfs : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  have hfs₁ : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s₁ - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  rw [← finsum_sub_distrib hfs hfs₁]
  exact finsum_congr fun u => by ring


/-- `Re (1/((x : ℂ) + i T - u)) = (x - Re u)/((x - Re u)² + (T - Im u)²)`. -/
private lemma re_inv_shift (x T : ℝ) (u : ℂ) :
    (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)).re
      = (x - u.re) / ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hz : (((x : ℂ) + Complex.I * (T : ℂ)) - u).re = x - u.re := by simp
  have hi : (((x : ℂ) + Complex.I * (T : ℂ)) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hz, hi]
  ring


/-- The divisor of `Λ = completedLFunction χ` on a ball has finite support (as a plain
function `ℂ → ℤ`). -/
private lemma divisor_support_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) :
    (Function.support ⇑(MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R))).Finite :=
  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
    (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R))


private lemma rebased_kernel_nonneg {u : ℂ} (h1 : 0 < u.re) (h2 : u.re < 1) (T : ℝ) :
    0 ≤ (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) := by
  have ha : (0:ℝ) < 2 - u.re := by linarith
  have hb : (0:ℝ) < 1 + u.re := by linarith
  have hd1 : 0 < (2 - u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos ha ha]
  have hd2 : 0 < (1 + u.re) ^ 2 + (T - u.im) ^ 2 := by
    nlinarith [sq_nonneg (T - u.im), mul_pos hb hb]
  exact add_nonneg (div_nonneg ha.le hd1.le) (div_nonneg hb.le hd2.le)


/-- **Weighted zero count.**  For a primitive non-trivial character `χ` mod `N`, every real
`T` and every `R`, the divisor-weighted sum of the rebased partial-fraction kernel is at
most `log N + log(2 + |T|) + 10`. -/
theorem finsum_divisor_re_sub_inv_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T : ℝ) (R : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))
      ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by
  classical
  set K : ℂ → ℝ := fun u => (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) with hK
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛdiff _
  have hz1 : DirichletCharacter.completedLFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 :=
    completedLFunction_ne_zero_re_two χ hχ hχprim T
  have hz2 : DirichletCharacter.completedLFunction χ ((-1 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 :=
    completedLFunction_ne_zero_re_neg_one χ hχ hχprim T
  have hpf := partialFraction_diff χ hχ hχprim ((2 : ℂ) + Complex.I * (T : ℂ))
    ((-1 : ℂ) + Complex.I * (T : ℂ)) hz1 hz2
  set L : ℝ := (logDeriv (DirichletCharacter.completedLFunction χ)
      ((2 : ℂ) + Complex.I * (T : ℂ))
    - logDeriv (DirichletCharacter.completedLFunction χ)
      ((-1 : ℂ) + Complex.I * (T : ℂ))).re with hL
  have hre : Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))).re)
      atTop (𝓝 L) := by
    rw [hL]
    exact (Complex.continuous_re.tendsto _).comp hpf
  -- identify the real part of the sum with the target finsum
  have hident : ∀ R : ℝ, (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))).re
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u := by
    intro R
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))) := by
      refine (divisor_support_finite χ R).subset (fun u hu => ?_)
      have hu' : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - u)
            - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)) ≠ 0 := hu
      exact fun h => hu' (by rw [h, Int.cast_zero, zero_mul])
    rw [← Complex.reCLM_apply, map_finsum Complex.reCLM hfs]
    refine finsum_congr fun u => ?_
    rw [Complex.reCLM_apply]
    rw [Complex.mul_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
        show (-1 : ℂ) = ((-1 : ℝ) : ℂ) from by norm_num]
    rw [Complex.sub_re, re_inv_shift (2:ℝ) T u, re_inv_shift (-1:ℝ) T u, hK]
    ring
  have hre' : Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u) atTop (𝓝 L) := by
    refine hre.congr' ?_
    filter_upwards with R
    exact hident R
  -- monotonicity in R
  have hmono : ∀ R R' : ℝ, R ≤ R' → (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u)
      ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u) := by
    intro R R' hRR'
    refine finsum_le_finsum'
      (f := fun u => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u)
      (g := fun u => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u) ?_ ?_ ?_
    · refine (divisor_support_finite χ R).subset (fun u hu => ?_)
      have hu' : ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ)) * K u ≠ 0 := hu
      exact fun h => hu' (by rw [h, Int.cast_zero, zero_mul])
    · refine (divisor_support_finite χ R').subset (fun u hu => ?_)
      have hu' : ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ)) * K u ≠ 0 := hu
      intro h
      exact hu' (by rw [h, Int.cast_zero, zero_mul])
    · intro u
      show (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u
        ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R')) u : ℤ) : ℝ) * K u
      by_cases hu : u ∈ Metric.closedBall (0:ℂ) R
      · have hu' : u ∈ Metric.closedBall (0:ℂ) R' := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu ⊢
          exact le_trans hu hRR'
        have hfU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R ∪ Metric.closedBall 0 R') := by
          intro z hz
          exact hΛdiff.analyticAt z
        have heq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
          (hf := hfU) hu hu'
        rw [heq]
      · have h0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u = 0 :=
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu
        rw [h0, Int.cast_zero, zero_mul]
        by_cases hd : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R') u = 0
        · rw [hd, Int.cast_zero, zero_mul]
        · refine mul_nonneg (Int.cast_nonneg ?_) ?_
          · exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn R') u
          · have hfu : DirichletCharacter.completedLFunction χ u = 0 :=
              Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R') hd
            have hs := zerosInStrip χ hχ hχprim u hfu
            rw [hK]
            exact rebased_kernel_nonneg hs.1 hs.2 T
  have hfin : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u) ≤ L :=
    ge_of_tendsto hre' (Filter.eventually_atTop.2 ⟨R, fun c hc => hmono R c hc⟩)
  have hLb : L ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by
    rw [hL]
    have h2 : ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ (1 / 2) * Real.log (2 + |T|) + 5 :=
      completedLogDeriv_two_small χ hχ T
    have h1 : ‖logDeriv (DirichletCharacter.completedLFunction χ)
        ((-1 : ℂ) + Complex.I * (T : ℂ))‖
        ≤ Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |T|) + 5 :=
      completedLogDeriv_neg_one_small χ hχ hχprim T
    calc (logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))
              - logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))).re
          ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))
              - logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))‖ := Complex.re_le_norm _
      _ ≤ ‖logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖
            + ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((-1 : ℂ) + Complex.I * (T : ℂ))‖ := norm_sub_le _ _
      _ ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by linarith
  calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
          + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2)))
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * K u := by
        rw [hK]
    _ ≤ L := hfin
    _ ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := hLb


end Commons.NumberTheory.DirichletCharacter
