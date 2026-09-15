import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

noncomputable section
open Complex Metric
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Boundedness of the truncated explicit-formula zero sum on a small window

For `2 ≤ x ≤ 3` and `2 ≤ T ≤ x` we bound the weighted zero sum
`∑_ρ m(ρ) · x^ρ/ρ`, restricted to the zeros `ρ` of an entire function `f` with
`0 < Re ρ < 1` and `|Im ρ| ≤ T`, by a constant depending only on `f`.

The key point is that the summand is supported on the finitely many zeros of `f`
inside the fixed closed disc of radius `5` (a zero of the completed L-function in
the critical strip with `|Im ρ| ≤ 3` has `‖ρ‖ ≤ 4`).  On this finite set every term
is bounded by `m(ρ) · 3/‖ρ‖` because `x ≤ 3` and `Re ρ < 1`, which gives a bound
independent of `x` and `T`.
-/

/-- The norm of `x ^ s` for positive real `x` and complex `s` is `x ^ s.re`. -/
private lemma cpow_norm_ofReal (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ = x ^ s.re := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.norm_exp]
  have h1 : (Complex.log (x : ℂ) * s).re = Real.log x * s.re := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le,
      Complex.norm_of_nonneg hx.le]
    ring
  rw [h1, Real.rpow_def_of_pos hx]

/-- On a set where `f` is analytic and `u` lies, the divisor of `f` coincides with the
vanishing order of `f` at `u`. -/
private lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]
      simp
    rw [h2, ← hn]
    simp

/-- **Boundedness of the small-window zero sum for an arbitrary entire function.** -/
private lemma zeroSum_small_window_bound_aux (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → x ≤ 3 → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖∑ᶠ ρ : ℂ, ((analyticOrderNatAt f ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖ ≤ K := by
  classical
  have hfanB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 5) :=
    fun z _ => hf.analyticAt z
  have hfin : (Function.support fun u : ℂ =>
      MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) 5) u).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) 5)).finiteSupport
        (isCompact_closedBall (0 : ℂ) 5)
  let D : Finset ℂ := hfin.toFinset
  have hDfin : ((D : Set ℂ)).Finite := by
    simpa only [D, Set.Finite.coe_toFinset hfin] using hfin
  have memD : ∀ u : ℂ, u ∈ D ↔ MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) 5) u ≠ 0 := by
    intro u
    simp only [D, Set.Finite.mem_toFinset hfin, Function.mem_support]
  refine ⟨1 + ∑ ρ ∈ D, ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖, ?_, ?_⟩
  · have hnonneg : ∀ ρ ∈ D, 0 ≤ ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ := by
      intro ρ _
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (norm_nonneg ρ)
    linarith [Finset.sum_nonneg hnonneg]
  · intro x hx2 hx3 T hT2 hTx
    have hxpos : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    let g : ℂ → ℂ := fun ρ : ℂ => ((analyticOrderNatAt f ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)
    change ‖∑ᶠ ρ : ℂ, g ρ‖ ≤ 1 + ∑ ρ ∈ D, ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖
    -- support of the summand is contained in the finite set `D`
    have hsub : Function.support g ⊆ (D : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, memD]
      intro hdiv0
      apply hu
      by_cases hind : 0 < u.re ∧ u.re < 1 ∧ |u.im| ≤ T
      · have huB : u ∈ Metric.closedBall (0 : ℂ) 5 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          refine le_trans (Complex.norm_le_abs_re_add_abs_im u) ?_
          have h1 : |u.re| ≤ 1 := by
            rw [abs_of_pos hind.1]
            linarith [hind.2.1]
          have h2 : |u.im| ≤ 3 := by
            refine le_trans hind.2.2 ?_
            linarith
          linarith
        have hm0 : (analyticOrderNatAt f u : ℤ) = 0 := by
          rw [← divisor_eq_analyticOrderNatAt hfanB huB]
          exact hdiv0
        have hm0' : analyticOrderNatAt f u = 0 := by exact_mod_cast hm0
        simp only [g, if_pos hind, hm0', Nat.cast_zero, zero_mul]
      · simp only [g, if_neg hind, mul_zero]
    have hgfin : Function.HasFiniteSupport g := hDfin.subset hsub
    -- pointwise bound of each summand
    have hterm : ∀ ρ ∈ D, ‖g ρ‖ ≤ ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ := by
      intro ρ _
      by_cases hind : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T
      · have hρne : ρ ≠ 0 := by
          intro h
          rw [h] at hind
          simp only [Complex.zero_re] at hind
          linarith [hind.1]
        have hval : g ρ = ((analyticOrderNatAt f ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ) := by
          simp only [g, if_pos hind]
        have hxre : x ^ ρ.re ≤ 3 := by
          have h1 : x ^ ρ.re ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hind.2.1)
          rw [Real.rpow_one] at h1
          linarith
        have hm : (0 : ℝ) ≤ ((analyticOrderNatAt f ρ : ℕ) : ℝ) := Nat.cast_nonneg _
        rw [hval, norm_mul, Complex.norm_natCast, norm_div, cpow_norm_ofReal x hxpos]
        calc ((analyticOrderNatAt f ρ : ℕ) : ℝ) * (x ^ ρ.re / ‖ρ‖)
            ≤ ((analyticOrderNatAt f ρ : ℕ) : ℝ) * (3 / ‖ρ‖) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxre (norm_nonneg ρ)) hm
          _ = ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ := by ring
      · rw [show g ρ = 0 by simp only [g, if_neg hind, mul_zero], norm_zero]
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (norm_nonneg ρ)
    calc ‖∑ᶠ ρ : ℂ, g ρ‖
        = ‖∑ ρ ∈ D, g ρ‖ := by rw [finsum_eq_sum_of_support_subset g hsub]
      _ ≤ ∑ ρ ∈ D, ‖g ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ D, ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ := Finset.sum_le_sum hterm
      _ ≤ 1 + ∑ ρ ∈ D, ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ := by
          have hnn : (0 : ℝ) ≤ ∑ ρ ∈ D, ((analyticOrderNatAt f ρ : ℕ) : ℝ) * 3 / ‖ρ‖ :=
            Finset.sum_nonneg (fun ρ _ =>
              div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (norm_nonneg ρ))
          linarith

theorem completedL_zeroSum_small_window_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → x ≤ 3 → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖ ≤ K := by
  exact zeroSum_small_window_bound_aux (DirichletCharacter.completedLFunction χ)
    (DirichletCharacter.differentiable_completedLFunction hχ)

end Commons.NumberTheory.DirichletCharacter