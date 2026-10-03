import Mathlib
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.Sharp.Chi4LSeriesOffAxisLogDerivReBound
import Submission.Work.FIArea6Road.Chi4CCommon
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ZetaValues
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight
import Submission.Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one
import Submission.Commons.Analysis.Complex.borelCaratheodory_deriv_le
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Work.FIArea6Hecke.R.real_zeros_bounded_above

namespace Work.FIArea6Road

open Complex Filter Metric
open scoped BigOperators Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6400000

/-! ## Elementary kernels -/

/-- `Re (1/((x : ℂ) + iT - u)) = (x - Re u)/((x - Re u)² + (T - Im u)²)`. -/
lemma re_inv_shift_chi4 {x T : ℝ} {u : ℂ} :
    (1 / (((x : ℂ) + (T : ℂ) * Complex.I) - u)).re
      = (x - u.re) / ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hz : (((x : ℂ) + (T : ℂ) * Complex.I) - u).re = x - u.re := by simp
  have hi : (((x : ℂ) + (T : ℂ) * Complex.I) - u).im = T - u.im := by simp
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hz, hi]
  ring

/-- The kernel of the pair `(2 + it, -1 + it)` at a zero `β + iγ` dominates
`(1/2)·1/(1 + δ²)`. -/
lemma kernel_two_neg_one_lower {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 / (1 + δ ^ 2) ≤ 2 * ((2 - β) / ((2 - β) ^ 2 + δ ^ 2)
      + (1 + β) / ((1 + β) ^ 2 + δ ^ 2)) := by
  have ha1 : (1 : ℝ) ≤ 2 - β := by linarith
  have ha2 : 2 - β ≤ 2 := by linarith
  have hb1 : (1 : ℝ) ≤ 1 + β := by linarith
  have hb2 : 1 + β ≤ 2 := by linarith
  have hden1 : 0 < (2 - β) ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg δ, sq_nonneg (2 - β)]
  have hden2 : 0 < (1 + β) ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg δ, sq_nonneg (1 + β)]
  have hden0 : 0 < 1 + δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hden4 : 0 < 4 + δ ^ 2 := by nlinarith [sq_nonneg δ]
  have h1 : 1 / (4 + δ ^ 2) ≤ (2 - β) / ((2 - β) ^ 2 + δ ^ 2) := by
    rw [div_le_div_iff₀ hden4 hden1]
    nlinarith [sq_nonneg δ, ha1, ha2]
  have h2 : 1 / (4 + δ ^ 2) ≤ (1 + β) / ((1 + β) ^ 2 + δ ^ 2) := by
    rw [div_le_div_iff₀ hden4 hden2]
    nlinarith [sq_nonneg δ, hb1, hb2]
  have h3 : 1 / (1 + δ ^ 2) ≤ 4 / (4 + δ ^ 2) := by
    rw [div_le_div_iff₀ hden0 hden4]
    linarith [sq_nonneg δ]
  have h4 : 4 / (4 + δ ^ 2) = 2 * (1 / (4 + δ ^ 2) + 1 / (4 + δ ^ 2)) := by ring
  rw [h4] at h3
  linarith

/-! ## The weighted zero sum for `χ₄` -/

/-- Weighted zero sum: the divisor-weighted sum of the rebased kernels `1/(1+(t-Im u)²)` over the
zeros of `Λ(·,χ₄)` in the ball of radius `R ≥ 1` is `O(log(4(|t|+2)))` for `|t| ≥ 1`. -/
theorem chi4C_weightedZeroSum :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ t : ℝ, 1 ≤ |t| → ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
        ≤ Cw * Real.log (4 * (|t| + 2)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro t ht R hR
  set ℓ : ℝ := Real.log (4 * (|t| + 2)) with hℓ
  have hℓpos : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hℓ2 : (2 : ℝ) ≤ ℓ := by
    rw [hℓ]
    have hexp : Real.exp 2 ≤ 4 * (|t| + 2) := by
      have h8 : Real.exp 2 < 8 := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      have h2 : (8 : ℝ) ≤ 4 * (|t| + 2) := by linarith [abs_nonneg t, ht]
      linarith
    have := Real.log_le_log (Real.exp_pos 2) hexp
    rwa [Real.log_exp] at this
  set B₁ : ℝ := (1 / 2) * Real.log (2 + |t|) + 3 / 4 with hB₁
  have hB2 : (logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      ((2 : ℂ) + Complex.I * (t : ℂ))).re ≤ B₁ := by
    have h := Commons.NumberTheory.DirichletCharacter.re_completedLogDeriv_two_tight
      Work.FIArea6Hecke.R.chi4C chi4C_ne_one t
    rw [hB₁]
    exact h
  have hfins := Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
    Work.FIArea6Hecke.R.chi4C chi4C_ne_one chi4C_isPrimitive t 2 B₁ (by norm_num) hB2 R
  set K : ℂ → ℝ := fun u => (2 - u.re) / ((2 - u.re) ^ 2 + (t - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (t - u.im) ^ 2) with hK
  have hfins' : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * K u)
      ≤ B₁ + Real.log ((4 : ℕ) : ℝ) + (1 / 2) * Real.log (2 + |t|) + 3 / 2 := by
    rw [hK]
    exact hfins
  -- comparison of kernels
  have hdivnn : ∀ u : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.closedBall 0 R)) u : ℝ) := by
    intro u
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction chi4C_ne_one).analyticAt z) u
  have hcmp : ∀ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)
      ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℝ) * (2 * K u) := by
    intro u
    by_cases hd0 : ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) = 0
    · rw [hd0]; simp
    · have hΛu : DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero
          (fun z _ => (DirichletCharacter.differentiable_completedLFunction chi4C_ne_one).analyticAt z)
          (by
            intro hc
            exact hd0 (by rw [hc]; simp))
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip Work.FIArea6Hecke.R.chi4C
        chi4C_ne_one chi4C_isPrimitive u hΛu
      have hkl := kernel_two_neg_one_lower (δ := t - u.im) hstrip.1 hstrip.2
      rw [hK]
      have h5 : (0 : ℝ) < 1 + (t - u.im) ^ 2 := by positivity
      have heq : ((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)
          = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℝ) * (1 / (1 + (t - u.im) ^ 2)) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hkl (hdivnn u)
  have hfs1 : Function.HasFiniteSupport (fun u : ℂ => ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h, Int.cast_zero, zero_div]))
  have hfs2 : Function.HasFiniteSupport (fun u : ℂ => ((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.closedBall 0 R)) u : ℝ) * (2 * K u)) :=
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h, Int.cast_zero, zero_mul]))
  have hstep1 : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * (2 * K u) :=
    finsum_le_finsum' hfs1 hfs2 hcmp
  have hstep2 : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * (2 * K u))
      = 2 * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * K u) := by
    have heq : (fun u : ℂ => ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * (2 * K u))
        = fun u : ℂ => (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℝ) * K u) * 2 := by
      funext u; ring
    rw [heq, ← finsum_mul]
    ring
  have hmain₂ : 2 * (B₁ + Real.log ((4 : ℕ) : ℝ) + (1 / 2) * Real.log (2 + |t|) + 3 / 2)
      ≤ 8 * ℓ := by
    rw [hB₁]
    have hlog4 : Real.log ((4 : ℕ) : ℝ) ≤ 2 := by
      have h4 : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
      rw [h4]
      have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      rw [h2]; linarith
    have hlogt : Real.log (2 + |t|) ≤ ℓ := by
      rw [hℓ]
      apply Real.log_le_log (by positivity)
      linarith [abs_nonneg t]
    have hgoal : 2 * ((1 / 2) * Real.log (2 + |t|) + 3 / 4 + Real.log ((4 : ℕ) : ℝ)
        + (1 / 2) * Real.log (2 + |t|) + 3 / 2)
        = 2 * Real.log (2 + |t|) + 2 * Real.log ((4 : ℕ) : ℝ) + 9 / 2 := by ring
    rw [hgoal]
    have e1 : 2 * Real.log (2 + |t|) ≤ 2 * ℓ :=
      mul_le_mul_of_nonneg_left hlogt (by norm_num)
    have e2 : 2 * Real.log ((4 : ℕ) : ℝ) ≤ 4 := by
      have := mul_le_mul_of_nonneg_left hlog4 (by norm_num : (0:ℝ) ≤ 2)
      norm_num at this ⊢
      exact this
    have e3 : (9 : ℝ) / 2 ≤ 3 * ℓ := by nlinarith only [hℓ2]
    have e4 : 2 * Real.log (2 + |t|) + 2 * Real.log ((4 : ℕ) : ℝ) + 9 / 2
        ≤ 2 * ℓ + 4 + 3 * ℓ := by
      have h1 := add_le_add e1 e2
      have h2 := add_le_add h1 e3
      calc 2 * Real.log (2 + |t|) + 2 * Real.log ((4 : ℕ) : ℝ) + 9 / 2
          ≤ (2 * ℓ + 4) + 3 * ℓ := h2
        _ = 2 * ℓ + 4 + 3 * ℓ := by ring
    have e5 : 2 * ℓ + 4 + 3 * ℓ ≤ 8 * ℓ := by nlinarith only [hℓ2]
    exact le_trans e4 e5
  have hmain₁ : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
      ≤ 2 * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * K u) := by
    rw [hstep2] at hstep1
    exact hstep1
  have hmain₃ : 2 * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℝ) * K u)
      ≤ 2 * (B₁ + Real.log ((4 : ℕ) : ℝ) + (1 / 2) * Real.log (2 + |t|) + 3 / 2) := by
    linarith [hfins']
  linarith [hmain₁, hmain₃, hmain₂]


/-! ## The one-sided logarithmic-derivative bound -/

/-- If `L(·,χ₄)` does not vanish at `z` (with `0 < Re z`) then neither does `Λ(·,χ₄)`, the
archimedean factor being zero-free there. -/
lemma completedL_chi4C_ne_zero_of_L_ne_zero {z : ℂ} (hz : 0 < z.re)
    (hL : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C z ≠ 0) :
    DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C z ≠ 0 := by
  intro hΛ
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    (χ := Work.FIArea6Hecke.R.chi4C) z (Or.inl hz0)
  rw [h, hΛ, zero_div] at hL
  exact hL rfl

/-- Numerical core: the kernel of the pair `(σ + it, 2 + it)` at a zero `β + iγ` is bounded below
by `-3/(1 + (t-γ)²)`.  This is the only place where the zero-free region enters (through the
hypothesis `hsep` that a zero strictly to the right of `σ` cannot be vertically close to `t`). -/
lemma pair_kernel_lower {σ β δ c ℓ : ℝ} (hcℓ : c / ℓ ≤ 1 / 2) (hℓpos : 0 < ℓ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσβ : max (β - σ) 0 ≤ c / ℓ)
    (hsep : σ < β → 1 ≤ |δ|) :
    -(3 / (1 + δ ^ 2)) ≤ (σ - β) / ((σ - β) ^ 2 + δ ^ 2)
      - (2 - β) / ((2 - β) ^ 2 + δ ^ 2) := by
  set x : ℝ := 1 + δ ^ 2 with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  -- the second term, multiplied by `x`
  have h2 : x * ((2 - β) / ((2 - β) ^ 2 + δ ^ 2)) ≤ 2 := by
    have hden2 : 0 < (2 - β) ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg δ, hβ1]
    rw [mul_div_assoc', div_le_iff₀ hden2, hx]
    nlinarith [sq_nonneg δ, hβ0, hβ1]
  -- the first term, multiplied by `x`
  have h1 : -1 ≤ x * ((σ - β) / ((σ - β) ^ 2 + δ ^ 2)) := by
    by_cases hle : σ < β
    · have hδ1 : (1 : ℝ) ≤ δ ^ 2 := by nlinarith [abs_nonneg δ, sq_abs δ, hsep hle]
      have hden1 : 0 < (β - σ) ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg (β - σ), hδ1]
      have hβσ : β - σ ≤ c / ℓ := le_trans (le_max_left _ _) hσβ
      have hsym : x * ((σ - β) / ((σ - β) ^ 2 + δ ^ 2))
          = -(x * ((β - σ) / ((β - σ) ^ 2 + δ ^ 2))) := by
        rw [show σ - β = -(β - σ) by ring, neg_pow]
        field_simp
      rw [hsym]
      have hkey : x * ((β - σ) / ((β - σ) ^ 2 + δ ^ 2)) ≤ 1 := by
        rw [mul_div_assoc', div_le_iff₀ hden1]
        have hxa : x * (β - σ) ≤ x * (c / ℓ) :=
          mul_le_mul_of_nonneg_left hβσ (le_of_lt hxpos)
        have hxb : x * (c / ℓ) ≤ x * (1 / 2) :=
          mul_le_mul_of_nonneg_left hcℓ (le_of_lt hxpos)
        have hxc : x * (1 / 2) ≤ (β - σ) ^ 2 + δ ^ 2 := by
          rw [hx]; nlinarith [hδ1, sq_nonneg (β - σ)]
        linarith [hxa, hxb, hxc]
      linarith
    · push_neg at hle
      have hA0 : 0 ≤ (σ - β) / ((σ - β) ^ 2 + δ ^ 2) := by
        rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (σ - β) ^ 2 + δ ^ 2) with h0 | h0
        · rw [← h0, div_zero]
        · exact div_nonneg (by linarith) (le_of_lt h0)
      have : (0 : ℝ) ≤ x * ((σ - β) / ((σ - β) ^ 2 + δ ^ 2)) :=
        mul_nonneg (le_of_lt hxpos) hA0
      linarith
  -- conclusion
  have hgoal : -(3 / x) ≤ (σ - β) / ((σ - β) ^ 2 + δ ^ 2)
      - (2 - β) / ((2 - β) ^ 2 + δ ^ 2) := by
    rw [← neg_div, div_le_iff₀ hxpos]
    have heq : ((σ - β) / ((σ - β) ^ 2 + δ ^ 2) - (2 - β) / ((2 - β) ^ 2 + δ ^ 2)) * x
        = x * ((σ - β) / ((σ - β) ^ 2 + δ ^ 2))
          - x * ((2 - β) / ((2 - β) ^ 2 + δ ^ 2)) := by ring
    rw [heq]
    linarith [h1, h2]
  rw [hx] at hgoal
  exact hgoal

/-- Separation of the zeros of `Λ(·,χ₄)` from the point `σ + it` inside the zero-free region:
a zero with `σ < Re u` must have vertical distance at least `1` from `t`. -/
lemma chi4C_zero_separated {c c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁2 : c ≤ c₁ / 2)
    (hzf : ∀ σ τ : ℝ, 1 ≤ |τ| → 1 - c₁ / Real.log (4 * (|τ| + 2)) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0)
    {σ t : ℝ} (ht : 2 ≤ |t|) (hσ : 1 - c / Real.log (4 * (|t| + 2)) ≤ σ)
    {u : ℂ} (hu : DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C u = 0)
    (hlt : σ < u.re) :
    1 ≤ |t - u.im| := by
  by_contra hcon
  push_neg at hcon
  have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip
    Work.FIArea6Hecke.R.chi4C chi4C_ne_one chi4C_isPrimitive u hu
  have hℓpos : 0 < Real.log (4 * (|t| + 2)) := Real.log_pos (by linarith [abs_nonneg t])
  have h2pos : 0 < Real.log (4 * (|u.im| + 2)) := Real.log_pos (by linarith [abs_nonneg u.im])
  have hLu : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
      ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = 0 := by
    have hLu' : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C u = 0 := by
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0] at hstrip
        simp at hstrip
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        (χ := Work.FIArea6Hecke.R.chi4C) u (Or.inl hu0)
      rw [h, hu, zero_div]
    rwa [Complex.re_add_im]
  have hγ : 1 ≤ |u.im| := by
    have h1 : |t| ≤ |u.im| + |t - u.im| := by
      calc |t| = |u.im + (t - u.im)| := by ring_nf
        _ ≤ |u.im| + |t - u.im| := abs_add_le _ _
    linarith
  have himle : |u.im| < |t| + 1 := by
    have h1 : |u.im| ≤ |u.im - t| + |t| := by
      calc |u.im| = |(u.im - t) + t| := by ring_nf
        _ ≤ |u.im - t| + |t| := abs_add_le _ _
    rw [abs_sub_comm] at h1
    linarith
  have hlogc : Real.log (4 * (|u.im| + 2)) ≤ 2 * Real.log (4 * (|t| + 2)) := by
    have hle : 4 * (|u.im| + 2) ≤ 2 * (4 * (|t| + 2)) :=
      by linarith [abs_nonneg t, abs_nonneg u.im]
    have hpos1 : (0 : ℝ) < 4 * (|u.im| + 2) := by linarith [abs_nonneg u.im]
    have hpos2 : (0 : ℝ) < 4 * (|t| + 2) := by linarith [abs_nonneg t]
    have h1 := Real.log_le_log hpos1 hle
    rw [Real.log_mul (by norm_num) hpos2.ne'] at h1
    have h2 : Real.log 2 ≤ Real.log (4 * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith
  have hreg : 1 - c₁ / Real.log (4 * (|u.im| + 2)) ≤ u.re := by
    have h1 : c₁ / (2 * Real.log (4 * (|t| + 2))) ≤ c₁ / Real.log (4 * (|u.im| + 2)) := by
      rw [div_le_div_iff₀ (by positivity) h2pos]
      nlinarith [hlogc, hc₁, hℓpos]
    have h2 : 1 - c₁ / (2 * Real.log (4 * (|t| + 2))) ≤ σ := by
      have h3 : c / Real.log (4 * (|t| + 2)) ≤ c₁ / (2 * Real.log (4 * (|t| + 2))) := by
        rw [div_le_div_iff₀ hℓpos (by positivity)]
        nlinarith [hc₁2, hℓpos]
      linarith
    linarith
  exact (hzf u.re u.im hγ hreg (by linarith [hstrip.2])) hLu

/-- **The one-sided logarithmic-derivative bound for `χ₄`** in the zero-free region
`1 - c/log(4(|t|+2)) ≤ σ ≤ 2`, `|t| ≥ 2`: from the weighted zero sum for the zeros of `Λ(·,χ₄)`
and the non-vanishing of `L(·,χ₄)` in the (slightly larger) region. -/
theorem chi4C_oneSidedBound {Cw c₁ : ℝ} (hCw : 0 < Cw) (hc₁ : 0 < c₁)
    (hwzs : ∀ t : ℝ, 1 ≤ |t| → ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℝ) / (1 + (t - u.im) ^ 2))
        ≤ Cw * Real.log (4 * (|t| + 2)))
    (hzf : ∀ σ τ : ℝ, 1 ≤ |τ| → 1 - c₁ / Real.log (4 * (|τ| + 2)) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0)
    {c : ℝ} (hc : 0 < c) (hc₁2 : c ≤ c₁ / 2) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 2 ≤ |t| →
      1 - c / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
        (-logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
          ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤ C * Real.log (4 * (|t| + 2)) := by
  obtain ⟨Cg, hCg, hgbf⟩ := gammaFactor_chi4C_logDeriv_re_abs_le
  obtain ⟨CL, hCL, hLb⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
  obtain ⟨C2, hC2, hC2b⟩ := completedL_logDeriv_re_at_two_ge
  refine ⟨CL + 2 * Cg + 1 + 3 * Cw + C2, by linarith, ?_⟩
  intro σ t ht hσ hσ2
  set ℓ : ℝ := Real.log (4 * (|t| + 2)) with hℓ
  have hℓpos : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hℓ2 : (2 : ℝ) ≤ ℓ := by
    rw [hℓ]
    have hexp : Real.exp 2 ≤ 4 * (|t| + 2) := by
      have h8 : Real.exp 2 < 8 := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      have h2 : (8 : ℝ) ≤ 4 * (|t| + 2) := by linarith [abs_nonneg t, ht]
      linarith
    have := Real.log_le_log (Real.exp_pos 2) hexp
    rwa [Real.log_exp] at this
  have hcℓ : c / ℓ ≤ 1 / 2 := by
    rw [div_le_iff₀ hℓpos]
    linarith [hℓ2, hc1]
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  set s₂ : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs₂
  have hsre : s.re = σ := by rw [hs]; simp
  have hs₂re : s₂.re = 2 := by rw [hs₂]; simp
  have hs₂im : s₂.im = t := by rw [hs₂]; simp
  have hσpos : 0 < σ := by
    have h1 : 1 - c / ℓ ≤ σ := by rw [hℓ]; exact hσ
    have h2 : c / ℓ ≤ 1 / 2 := hcℓ
    linarith only [h1, h2]
  -- non-vanishing
  have hLs : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s ≠ 0 := by
    have h1 : 1 - c₁ / Real.log (4 * (|t| + 2)) ≤ σ := by
      have h3 : c / Real.log (4 * (|t| + 2)) ≤ c₁ / Real.log (4 * (|t| + 2)) :=
        div_le_div_of_nonneg_right (by linarith)
          (le_of_lt (Real.log_pos (by linarith [abs_nonneg t])))
      linarith
    have h := hzf σ t (by linarith) h1 hσ2
    rwa [← hs] at h
  have hΛs : DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C s ≠ 0 :=
    completedL_chi4C_ne_zero_of_L_ne_zero (by rw [hsre]; exact hσpos) hLs
  have hLs₂ : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s₂ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _
      (Or.inl chi4C_ne_one) (by rw [hs₂re]; norm_num)
  have hΛs₂ : DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C s₂ ≠ 0 :=
    completedL_chi4C_ne_zero_of_L_ne_zero (by rw [hs₂re]; norm_num) hLs₂
  -- the Hadamard partial fraction
  have hpf := completedL_pf_diff Work.FIArea6Hecke.R.chi4C chi4C_ne_one chi4C_isPrimitive
    s s₂ hΛs hΛs₂
  -- pointwise kernel bound at the zeros
  have hker : ∀ u : ℂ, DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C u = 0 →
      -(3 / (1 + (t - u.im) ^ 2)) ≤ (1 / (s - u) - 1 / (s₂ - u)).re := by
    intro u hu
    have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip
      Work.FIArea6Hecke.R.chi4C chi4C_ne_one chi4C_isPrimitive u hu
    have h1 : (1 / (s - u)).re = (σ - u.re) / ((σ - u.re) ^ 2 + (t - u.im) ^ 2) := by
      rw [hs]; exact re_inv_shift_chi4
    have h2 : (1 / (s₂ - u)).re = (2 - u.re) / ((2 - u.re) ^ 2 + (t - u.im) ^ 2) := by
      rw [hs₂]; exact re_inv_shift_chi4
    rw [Complex.sub_re, h1, h2]
    have hmax : max (u.re - σ) 0 ≤ c / ℓ := by
      rcases le_or_gt u.re σ with hle | hlt
      · rw [max_eq_right (by linarith)]
        exact div_nonneg (le_of_lt hc) (le_of_lt hℓpos)
      · rw [max_eq_left (le_of_lt (by linarith))]
        rw [hℓ] at hσ ⊢
        linarith [hstrip.2]
    exact pair_kernel_lower hcℓ hℓpos hstrip.1 hstrip.2 hmax
      (fun hlt => chi4C_zero_separated hc₁ hc₁2 hzf ht hσ hu hlt)
  -- the real part of the divisor sum
  have hident : ∀ R : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
          Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₂ - u))).re
        = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
            Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₂ - u)).re) := by
    intro R
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
          Work.FIArea6Hecke.R.chi4C) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₂ - u))) :=
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
        (fun u hu => by
          rw [Function.mem_support] at hu ⊢
          intro h
          exact hu (by rw [h, Int.cast_zero, zero_mul]))
    rw [← Complex.reCLM_apply, map_finsum Complex.reCLM hfs]
    refine finsum_congr fun u => ?_
    rw [Complex.reCLM_apply, Complex.mul_re]
    simp
  -- the bound on the divisor sum, uniformly in `R`
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      -(3 * (Cw * ℓ)) ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₂ - u))).re := by
    refine Filter.eventually_atTop.2 ⟨1, fun R hR => ?_⟩
    rw [hident R]
    have hdivfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R) u)).Finite :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
    have hsupp : Function.HasFiniteSupport (fun u : ℂ => (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ)) := by
      show (Function.support (fun u : ℂ => (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ))).Finite
      refine hdivfin.subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, Int.cast_zero])
    have hdivnn : ∀ u : ℂ, 0 ≤ (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by
      intro u
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (fun z _ => (DirichletCharacter.differentiable_completedLFunction chi4C_ne_one).analyticAt z) u
    have hpt : ∀ u : ℂ, (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * (-(3 / (1 + (t - u.im) ^ 2)))
        ≤ (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₂ - u)).re) := by
      intro u
      by_cases hd0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction
        Work.FIArea6Hecke.R.chi4C) (Metric.closedBall 0 R) u = 0
      · rw [hd0]; simp
      · have hΛu : DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C u = 0 :=
          Commons.Analysis.Complex.zero_of_divisor_ne_zero
            (fun z _ => (DirichletCharacter.differentiable_completedLFunction chi4C_ne_one).analyticAt z)
            hd0
        exact mul_le_mul_of_nonneg_left (hker u hΛu) (hdivnn u)
    have hfs1 : Function.HasFiniteSupport (fun u : ℂ => (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * (-(3 / (1 + (t - u.im) ^ 2)))) :=
      hsupp.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h, zero_mul]))
    have hfs2 : Function.HasFiniteSupport (fun u : ℂ => (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₂ - u)).re)) :=
      hsupp.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h, zero_mul]))
    have hfs3 : Function.HasFiniteSupport (fun u : ℂ => ((((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)) * 3) :=
      hsupp.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h, zero_div, zero_mul]))
    have hle1 := finsum_le_finsum' hfs1 hfs2 hpt
    have hconv : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * (-(3 / (1 + (t - u.im) ^ 2))))
        = -(3 * (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2))) := by
      have heqf : (fun u : ℂ => (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) * (-(3 / (1 + (t - u.im) ^ 2))))
          = fun u : ℂ => -((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2) * 3) := by
        funext u; ring
      rw [heqf]
      have hneg : (∑ᶠ u : ℂ, -((((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2) * 3))
          = -(∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
            (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2) * 3) := by
        have h := map_finsum negAddMonoidHom hfs3
        simpa using h.symm
      rw [hneg, ← finsum_mul]
      ring
    have hwz : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)) ≤ Cw * ℓ := by
      have h := hwzs t (by linarith) R hR
      rw [← hℓ] at h
      exact h
    linarith [hle1, hconv, hwz]
  -- take the limit
  have hlim : -(3 * (Cw * ℓ)) ≤ (logDeriv (DirichletCharacter.completedLFunction
      Work.FIArea6Hecke.R.chi4C) s
      - logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s₂).re := by
    have hre_tend : Filter.Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
          Work.FIArea6Hecke.R.chi4C) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₂ - u))).re) Filter.atTop
        (nhds ((logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s
          - logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s₂).re)) :=
      (Complex.continuous_re.tendsto _).comp hpf
    have hmem := isClosed_Ici.mem_of_tendsto hre_tend hev
    simpa only [Set.mem_Ici] using hmem
  -- the two remaining one-sided inputs
  have hb2 : -(logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s₂).re
      ≤ C2 * ℓ := by
    have h := hC2b t
    rw [← hℓ] at h
    have hs₂' : s₂ = (2 : ℂ) + (t : ℂ) * Complex.I := hs₂
    rw [hs₂']
    linarith
  have hg : (logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re
      ≤ Cg * ℓ := by
    have h := hgbf σ t (le_of_lt hσpos) hσ2
    rw [← hℓ] at h
    have hs' : s = (σ : ℂ) + (t : ℂ) * Complex.I := hs
    rw [hs']
    exact (abs_le.mp h).2
  have hdec : logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s
      = logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s
        + logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add
      Work.FIArea6Hecke.R.chi4C chi4C_ne_one s (by rw [hsre]; exact hσpos) hLs
  have hredec : (logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s).re
      = (logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s).re
        + (logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re := by
    rw [hdec, Complex.add_re]
  rw [Complex.neg_re]
  have hdiff : -(logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C)
        s).re
      ≤ 3 * (Cw * ℓ) - (logDeriv (DirichletCharacter.completedLFunction
        Work.FIArea6Hecke.R.chi4C) s₂).re := by
    rw [Complex.sub_re] at hlim
    linarith
  have hmain : -(logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) s).re
      = -(logDeriv (DirichletCharacter.completedLFunction Work.FIArea6Hecke.R.chi4C) s).re
        + (logDeriv (DirichletCharacter.gammaFactor Work.FIArea6Hecke.R.chi4C) s).re := by
    rw [hredec]; ring
  rw [hmain]
  nlinarith [hdiff, hb2, hg, hℓpos, hCL, hCg, hCw, hC2]

/-! ## Mean value inequalities -/

/-- Mean-value inequality on a real segment, from a bound on an explicit derivative. -/
lemma norm_sub_le_of_hasDerivAt_segment_chi4 {F : ℂ → ℂ} {x y : ℂ} {f' : ℂ → ℂ} {K : ℝ}
    (hF : ∀ w ∈ segment ℝ x y, HasDerivAt F (f' w) w)
    (hK : ∀ w ∈ segment ℝ x y, ‖f' w‖ ≤ K) :
    ‖F y - F x‖ ≤ K * ‖y - x‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := F)
    (s := segment ℝ x y) (C := K)
    (f' := fun w => ContinuousLinearMap.toSpanSingleton ℂ (f' w))
    (x := x) (y := y) ?_ ?_ (convex_segment x y) (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)
  · intro w hw
    exact ((hF w hw).hasFDerivAt).hasFDerivWithinAt
  · intro w hw
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact hK w hw

/-- Mean-value inequality for a real function on a real segment. -/
lemma norm_sub_le_of_hasDerivWithinAt_Icc_chi4 {g : ℝ → ℂ} {σ σ₂ : ℝ} {g' : ℝ → ℂ} {K : ℝ}
    (hσ : σ ≤ σ₂)
    (hg : ∀ u ∈ Set.Icc σ σ₂, HasDerivWithinAt g (g' u) (Set.Icc σ σ₂) u)
    (hK : ∀ u ∈ Set.Icc σ σ₂, ‖g' u‖ ≤ K) :
    ‖g σ₂ - g σ‖ ≤ K * (σ₂ - σ) := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := g)
    (s := Set.Icc σ σ₂) (C := K)
    (f' := fun u => ContinuousLinearMap.toSpanSingleton ℝ (g' u))
    (x := σ) (y := σ₂)
    (fun u hu => (hg u hu).hasFDerivWithinAt)
    (fun u hu => by rw [ContinuousLinearMap.norm_toSpanSingleton]; exact hK u hu)
    (convex_Icc σ σ₂) (Set.left_mem_Icc.mpr hσ) (Set.right_mem_Icc.mpr hσ)
  simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ₂ - σ)] using h


/-- Borel--Carathéodory oscillation bound: an analytic function vanishing at the centre of a ball
and with real part bounded above by `Bnd` on the ball is bounded by `4·Bnd` on the ball of half
the radius. -/
lemma bc_oscillation_bound {F : ℂ → ℂ} {cb : ℂ} {R Bnd : ℝ} (hR : 0 < R) (hBnd : 0 ≤ Bnd)
    (hFan : AnalyticOnNhd ℂ F (Metric.ball cb R)) (hFc : F cb = 0)
    (hRe : ∀ w ∈ Metric.ball cb R, (F w).re ≤ Bnd) :
    ∀ z : ℂ, ‖z - cb‖ ≤ R / 2 → ‖F z‖ ≤ 4 * Bnd := by
  have hBC := Commons.Analysis.Complex.borelCaratheodory_deriv_le hR hBnd hFan hFc hRe
  have hderiv : ∀ z : ℂ, ‖z - cb‖ ≤ R / 2 → ‖deriv F z‖ ≤ 8 * Bnd / R := by
    intro z hz
    have hzm : z ∈ Metric.ball cb R := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith only [hz, hR]
    have hb := hBC z hzm
    have hden : R / 2 ≤ R - ‖z - cb‖ := by linarith only [hz]
    have hdenpos : 0 < R - ‖z - cb‖ := by linarith only [hz, hR]
    have hsq2 : R ^ 2 ≤ 4 * (R - ‖z - cb‖) ^ 2 := by nlinarith only [hden, hR]
    have key : 2 * R * Bnd / (R - ‖z - cb‖) ^ 2 ≤ 8 * Bnd / R := by
      rw [div_le_div_iff₀ (pow_pos hdenpos 2) hR]
      nlinarith only [hsq2, hBnd]
    linarith only [hb, key]
  intro z hz
  have hsegball : ∀ w ∈ segment ℝ cb z, ‖w - cb‖ ≤ R / 2 := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have hsub : (cb + θ • (z - cb)) - cb = θ • (z - cb) := by rw [add_sub_cancel_left]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    nlinarith only [hθ.2, norm_nonneg (z - cb), hz]
  have h1 : ∀ w ∈ segment ℝ cb z, HasDerivAt F (deriv F w) w := by
    intro w hw
    have hw' : w ∈ Metric.ball cb R := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith only [hsegball w hw, hR]
    exact (hFan.differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hw')).hasDerivAt
  have h2 : ∀ w ∈ segment ℝ cb z, ‖deriv F w‖ ≤ 8 * Bnd / R :=
    fun w hw => hderiv w (hsegball w hw)
  have hmv := norm_sub_le_of_hasDerivAt_segment_chi4 h1 h2
  rw [hFc, sub_zero] at hmv
  have h3 : ‖F z‖ ≤ 8 * Bnd / R * ‖z - cb‖ := hmv
  have h4 : 8 * Bnd / R * ‖z - cb‖ ≤ 8 * Bnd / R * (R / 2) :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  have h5 : 8 * Bnd / R * (R / 2) = 4 * Bnd := by
    field_simp
    ring
  linarith only [h3, h4, h5.le, h5.ge]


/-- Arithmetic step of the final estimate: `K·(σ₂-σ) ≤ (4d₀/3)·B`. -/
lemma final_estimate {K B d₀ ℓ σ σ₂ : ℝ} (hK : K ≤ B * ℓ) (hKnn : 0 ≤ K) (hℓpos : 0 < ℓ)
    (hd₀pos : 0 < d₀) (hBnn : 0 ≤ B) (hσ : σ₂ - σ ≤ 4 * d₀ / (3 * ℓ)) :
    K * (σ₂ - σ) ≤ 4 * d₀ / 3 * B := by
  have hpos : 0 < 4 * d₀ / (3 * ℓ) := by positivity
  have h1 : K * (σ₂ - σ) ≤ K * (4 * d₀ / (3 * ℓ)) := mul_le_mul_of_nonneg_left hσ hKnn
  have h2 : K * (4 * d₀ / (3 * ℓ)) ≤ (B * ℓ) * (4 * d₀ / (3 * ℓ)) :=
    mul_le_mul_of_nonneg_right hK hpos.le
  have h3 : (B * ℓ) * (4 * d₀ / (3 * ℓ)) = 4 * d₀ / 3 * B := by
    field_simp
  linarith only [h1, h2, h3.le, h3.ge]

/-! ## The inverse bound on the region `|t| ≥ 2` -/

/-- **Landau--Littlewood from the one-sided bound.**  The one-sided logarithmic-derivative bound
plus non-vanishing in the region implies the sharp inverse bound
`1/‖L(σ+iτ,χ₄)‖ ≪ log(4(|τ|+2))` there. -/
theorem chi4C_invBound_largeT {c₁ C₁ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hbound : ∀ σ τ : ℝ, 2 ≤ |τ| → 1 - c₁ / Real.log (4 * (|τ| + 2)) ≤ σ → σ ≤ 2 →
      (-logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ C₁ * Real.log (4 * (|τ| + 2)))
    (hzf : ∀ σ τ : ℝ, 1 ≤ |τ| → 1 - c₁ / Real.log (4 * (|τ| + 2)) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ τ : ℝ, 3 ≤ |τ| →
      1 - c / Real.log (4 * (|τ| + 2)) ≤ σ → σ ≤ 2 →
        1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * Real.log (4 * (|τ| + 2)) := by
  obtain ⟨Cn, hCn, hn⟩ :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_norm_le_of_one_lt_re
  set d₀ : ℝ := min c₁ 1 / 4 with hd₀
  have hd₀pos : 0 < d₀ := by
    rw [hd₀]; exact div_pos (lt_min hc₁ one_pos) (by norm_num)
  have hd₀c₁ : d₀ ≤ c₁ / 4 := by
    rw [hd₀]; have h := min_le_left c₁ 1; linarith
  have hd₀1 : d₀ ≤ 1 / 4 := by
    rw [hd₀]; have h := min_le_right c₁ 1; linarith
  have hd₀pos' : 0 < d₀ := hd₀pos
  refine ⟨min c₁ 1 / 24,
    (1 + 1 / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)),
    by positivity,
    mul_pos (by positivity) (Real.exp_pos _), ?_⟩
  intro σ τ hτ hσ hσ2
  set ℓ : ℝ := Real.log (4 * (|τ| + 2)) with hℓ
  have hℓpos : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by linarith [abs_nonneg τ])
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    rw [hℓ]
    exact Real.le_log_iff_exp_le (by linarith [abs_nonneg τ]) |>.mpr (by
      have h8 : Real.exp 1 < 8 := lt_trans Real.exp_one_lt_three (by norm_num)
      linarith [abs_nonneg τ, hτ])
  have hℓ2 : (2 : ℝ) ≤ ℓ := by
    rw [hℓ]
    have hexp : Real.exp 2 ≤ 4 * (|τ| + 2) := by
      have h8 : Real.exp 2 < 8 := by
        have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
      have h2 : (8 : ℝ) ≤ 4 * (|τ| + 2) := by linarith [abs_nonneg τ, hτ]
      linarith
    have := Real.log_le_log (Real.exp_pos 2) hexp
    rwa [Real.log_exp] at this
  set eps : ℝ := d₀ / ℓ with heps
  have hepspos : 0 < eps := by rw [heps]; exact div_pos hd₀pos hℓpos
  have heps4 : eps ≤ 1 / 8 := by
    rw [heps, div_le_iff₀ hℓpos]; linarith [hd₀1, hℓ2]
  have hσ' : 1 - (min c₁ 1 / 24) / ℓ ≤ σ := by rw [hℓ]; exact hσ
  have hc24 : (min c₁ 1 / 24) / ℓ ≤ eps / 3 := by
    have h1 : eps / 3 = d₀ / (3 * ℓ) := by rw [heps]; ring
    rw [h1, div_le_div_iff₀ hℓpos (by positivity)]
    have h : min c₁ 1 / 24 * 3 ≤ d₀ := by
      rw [hd₀]; linarith [min_le_left c₁ 1, min_le_right c₁ 1]
    nlinarith [h, hℓpos]
  set cb : ℂ := ((1 + eps / 3 : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hcb
  have hcbre : cb.re = 1 + eps / 3 := by rw [hcb]; simp [Complex.add_re, Complex.mul_re]
  have hcbim : cb.im = τ := by rw [hcb]; simp [Complex.add_im, Complex.mul_im]
  set R : ℝ := 4 * eps / 3 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hRle : R ≤ 1 / 6 := by rw [hR]; linarith [heps4]
  -- elementary comparisons inside the ball
  have hlogcmp : ∀ w : ℂ, ‖w - cb‖ < R → Real.log (4 * (|w.im| + 2)) ≤ 2 * ℓ := by
    intro w hw
    have him : |w.im - cb.im| ≤ ‖w - cb‖ := Complex.abs_im_le_norm (w - cb)
    have h1 : |w.im - τ| < R := by rw [hcbim] at him; exact lt_of_le_of_lt him hw
    have h2 : |w.im| ≤ |τ| + R := by
      have h3 := abs_sub_abs_le_abs_sub w.im τ
      linarith
    have hle : 4 * (|w.im| + 2) ≤ 2 * (4 * (|τ| + 2)) := by linarith [abs_nonneg τ]
    have hpos1 : (0 : ℝ) < 4 * (|w.im| + 2) := by linarith [abs_nonneg w.im]
    have hpos2 : (0 : ℝ) < 4 * (|τ| + 2) := by linarith [abs_nonneg τ]
    have h4 := Real.log_le_log hpos1 hle
    rw [Real.log_mul (by norm_num) hpos2.ne'] at h4
    have h5 : Real.log 2 ≤ ℓ := by
      rw [hℓ]
      exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg τ, hτ])
    linarith
  have himge : ∀ w : ℂ, ‖w - cb‖ < R → 2 ≤ |w.im| := by
    intro w hw
    have him : |w.im - cb.im| ≤ ‖w - cb‖ := Complex.abs_im_le_norm (w - cb)
    have h1 : |w.im - τ| < R := by rw [hcbim] at him; exact lt_of_le_of_lt him hw
    have h2 : |τ| ≤ |w.im| + |w.im - τ| := by
      have h3 : |τ| = |w.im - (w.im - τ)| := by congr 1; ring
      rw [h3]
      calc |w.im - (w.im - τ)| = |w.im + -(w.im - τ)| := by rw [sub_eq_add_neg]
        _ ≤ |w.im| + |-(w.im - τ)| := abs_add_le _ _
        _ = |w.im| + |w.im - τ| := by rw [abs_neg]
    linarith [h1, hRle, hτ, h2]
  have hrewre : ∀ w : ℂ, ‖w - cb‖ < R → 1 - eps ≤ w.re := by
    intro w hw
    have hre : |w.re - cb.re| ≤ ‖w - cb‖ := Complex.abs_re_le_norm (w - cb)
    have h1 : -(R) ≤ w.re - cb.re := (abs_le.mp (le_of_lt (lt_of_le_of_lt hre hw))).1
    rw [hcbre, hR] at h1
    linarith
  have hrewre2 : ∀ w : ℂ, ‖w - cb‖ < R → w.re ≤ 2 := by
    intro w hw
    have hre : |w.re - cb.re| ≤ ‖w - cb‖ := Complex.abs_re_le_norm (w - cb)
    have h1 : w.re - cb.re < R := (abs_lt.mp (lt_of_le_of_lt hre hw)).2
    rw [hcbre, hR] at h1
    have h2 : eps ≤ 1 / 4 := by linarith [heps4]
    linarith
  -- the ball is zero-free
  have hball_nz : ∀ w : ℂ, w ∈ Metric.ball cb R →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C w ≠ 0 := by
    intro w hw
    have hwlt : ‖w - cb‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwim := himge w hwlt
    have hwre := hrewre w hwlt
    have hwre2 := hrewre2 w hwlt
    have hlog := hlogcmp w hwlt
    have hreg : 1 - c₁ / Real.log (4 * (|w.im| + 2)) ≤ w.re := by
      have hpos : 0 < Real.log (4 * (|w.im| + 2)) := Real.log_pos (by linarith [abs_nonneg w.im])
      have h4d : (c₁ / 2) / ℓ ≤ c₁ / Real.log (4 * (|w.im| + 2)) := by
        rw [div_le_div_iff₀ hℓpos hpos]
        have h1 : (c₁ / 2) * Real.log (4 * (|w.im| + 2)) ≤ (c₁ / 2) * (2 * ℓ) :=
          mul_le_mul_of_nonneg_left hlog (by linarith [hc₁])
        have h2 : (c₁ / 2) * (2 * ℓ) = c₁ * ℓ := by ring
        linarith [h1, h2.le, h2.ge]
      have h6 : eps ≤ (c₁ / 2) / ℓ := by
        rw [heps, div_le_div_iff₀ hℓpos hℓpos]
        nlinarith [hd₀c₁, hd₀pos, hℓpos]
      linarith
    have hw' : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    have h := hzf w.re w.im (le_trans (by norm_num) hwim) hreg hwre2
    rwa [← hw'] at h
  -- the one-sided bound on the ball
  have hRe_ball : ∀ w : ℂ, w ∈ Metric.ball cb R →
      (-logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) w).re ≤ C₁ * 2 * ℓ := by
    intro w hw
    have hwlt : ‖w - cb‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwim := himge w hwlt
    have hwre := hrewre w hwlt
    have hwre2 := hrewre2 w hwlt
    have hlog := hlogcmp w hwlt
    have hreg : 1 - c₁ / Real.log (4 * (|w.im| + 2)) ≤ w.re := by
      have hpos : 0 < Real.log (4 * (|w.im| + 2)) := Real.log_pos (by linarith [abs_nonneg w.im])
      have h4d : (c₁ / 2) / ℓ ≤ c₁ / Real.log (4 * (|w.im| + 2)) := by
        rw [div_le_div_iff₀ hℓpos hpos]
        have h1 : (c₁ / 2) * Real.log (4 * (|w.im| + 2)) ≤ (c₁ / 2) * (2 * ℓ) :=
          mul_le_mul_of_nonneg_left hlog (by linarith [hc₁])
        have h2 : (c₁ / 2) * (2 * ℓ) = c₁ * ℓ := by ring
        linarith [h1, h2.le, h2.ge]
      have h6 : eps ≤ (c₁ / 2) / ℓ := by
        rw [heps, div_le_div_iff₀ hℓpos hℓpos]
        nlinarith [hd₀c₁, hd₀pos, hℓpos]
      linarith
    have h := hbound w.re w.im hwim hreg hwre2
    have hw' : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    rw [← hw'] at h
    have hmult : C₁ * Real.log (4 * (|w.im| + 2)) ≤ C₁ * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog hC₁.le
    linarith [h, hmult]
  -- the value at the centre
  have hcb1 : 1 < cb.re := by rw [hcbre]; linarith [hepspos]
  have hcbval : ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) cb‖
      ≤ 3 / d₀ * ℓ + Cn := by
    have h := hn 4 Work.FIArea6Hecke.R.chi4C cb hcb1
    have h2 : cb.re - 1 = eps / 3 := by rw [hcbre]; ring
    have h3 : 1 / (cb.re - 1) = 3 * ℓ / d₀ := by
      rw [h2, heps]; field_simp
    rw [h3] at h
    have h4 : 3 * ℓ / d₀ = 3 / d₀ * ℓ := by ring
    rw [h4] at h
    exact h
  -- Borel--Caratheodory
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
      (Metric.ball cb R) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction chi4C_ne_one).analyticAt z
  set F : ℂ → ℂ := fun z => (-deriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) z)
    / DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C z with hF
  have hFan : AnalyticOnNhd ℂ F (Metric.ball cb R) :=
    ((hLan.deriv.neg).div hLan hball_nz)
  set G : ℂ → ℂ := fun z => F z - F cb with hG
  have hGan : AnalyticOnNhd ℂ G (Metric.ball cb R) :=
    hFan.sub (analyticOnNhd_const (v := F cb) (s := Metric.ball cb R))
  have hGc : G cb = 0 := by simp only [hG]; ring
  set Bnd : ℝ := C₁ * 2 * ℓ + (3 / d₀ * ℓ + Cn) with hBnd
  have hBndnn : 0 ≤ Bnd := by rw [hBnd]; positivity
  have hGre : ∀ w ∈ Metric.ball cb R, (G w).re ≤ Bnd := by
    intro w hw
    have h1 : (F w).re ≤ C₁ * 2 * ℓ := by
      have heq : (F w).re
          = (-logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) w).re := by
        simp only [hF, logDeriv_apply, neg_div]
      rw [heq]; exact hRe_ball w hw
    have h2 : -(F cb).re ≤ ‖F cb‖ := by
      have hh := Complex.re_le_norm (-(F cb)); simpa using hh
    have h3 : ‖F cb‖ ≤ 3 / d₀ * ℓ + Cn := by
      have heq : ‖F cb‖
          = ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) cb‖ := by
        simp only [hF, logDeriv_apply, neg_div, norm_div, norm_neg]
      rw [heq]; exact hcbval
    have heq : (G w).re = (F w).re - (F cb).re := by simp only [hG, Complex.sub_re]
    rw [heq, hBnd]
    linarith
  have hBC := Commons.Analysis.Complex.borelCaratheodory_deriv_le hRpos hBndnn hGan hGc hGre
  have hGs := bc_oscillation_bound hRpos hBndnn hGan hGc hGre
  -- the two-sided bound on the ball of radius `R/2`
  set K : ℝ := 4 * Bnd + (3 / d₀ * ℓ + Cn) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hFbound : ∀ z : ℂ, ‖z - cb‖ ≤ R / 2 →
      ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) z‖ ≤ K := by
    intro z hz
    have h1 : ‖F z‖ ≤ ‖G z‖ + ‖F cb‖ := by
      have heq : F z = G z + F cb := by simp only [hG]; ring
      rw [heq]; exact norm_add_le _ _
    have h2 := hGs z hz
    have h3 : ‖F cb‖ ≤ 3 / d₀ * ℓ + Cn := by
      have heq : ‖F cb‖
          = ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) cb‖ := by
        simp only [hF, logDeriv_apply, neg_div, norm_div, norm_neg]
      rw [heq]; exact hcbval
    have h4 : ‖F z‖ ≤ 4 * Bnd + (3 / d₀ * ℓ + Cn) := by linarith only [h1, h2, h3]
    have heq : ‖F z‖ = ‖logDeriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C) z‖ := by
      simp only [hF, logDeriv_apply, neg_div, norm_div, norm_neg]
    rw [heq] at h4
    rw [hK]
    exact h4
  have hK_le : K ≤ (8 * C₁ + 15 / d₀ + 5 * Cn + 1) * ℓ := by
    rw [hK, hBnd]
    have h5 : Cn ≤ Cn * ℓ := by nlinarith only [hCn.le, hℓ1]
    have h6 : 3 / d₀ * ℓ * 5 = 15 / d₀ * ℓ := by ring
    have h7 : 3 / d₀ * ℓ * 4 = 12 / d₀ * ℓ := by ring
    nlinarith only [h5, hℓ1, hCn, hd₀pos, hC₁, h6, h7]
  set σ₂ : ℝ := 1 + eps with hσ₂
  have hσ₂1 : 1 < σ₂ := by rw [hσ₂]; linarith only [hepspos]
  have hσ₂2 : σ₂ ≤ 2 := by rw [hσ₂]; linarith only [heps4]
  have hseg : ∀ u ∈ Set.Icc σ σ₂, ‖((u : ℂ) + (τ : ℂ) * Complex.I) - cb‖ ≤ R / 2 := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have heq : ((u : ℂ) + (τ : ℂ) * Complex.I) - cb
        = (((u - (1 + eps / 3) : ℝ)) : ℂ) := by
      rw [hcb]; push_cast; ring
    have hu2' : u - 1 ≤ eps := by rw [hσ₂] at hu2; linarith only [hu2]
    have hu1' : -(eps / 3) ≤ u - 1 := by linarith only [hσ', hc24, hu1]
    have habs : |u - (1 + eps / 3)| ≤ 2 * eps / 3 := by
      rw [abs_le]; constructor <;> linarith only [hu1', hu2']
    rw [heq, Complex.norm_real, Real.norm_eq_abs, hR]
    have heq3 : 4 * eps / 3 / 2 = 2 * eps / 3 := by ring
    linarith only [habs, heq3.le, heq3.ge]
  have hsegball : ∀ u ∈ Set.Icc σ σ₂, ((u : ℂ) + (τ : ℂ) * Complex.I) ∈ Metric.ball cb R := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm]
    linarith only [hseg u hu, hRpos]
  have hσ₂_nz : DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
      ((σ₂ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    have h2 : σ₂ - 1 = eps := by rw [hσ₂]; ring
    have h6 : eps ≤ (c₁ / 2) / ℓ := by
      rw [heps, div_le_div_iff₀ hℓpos hℓpos]
      nlinarith only [hd₀c₁, hd₀pos, hℓpos]
    have h4d : (c₁ / 2) / ℓ ≤ c₁ / ℓ := by
      rw [div_le_div_iff₀ hℓpos hℓpos]
      nlinarith only [hc₁, hℓpos]
    have h7 : eps ≤ c₁ / ℓ := le_trans h6 h4d
    have h8 : 1 - c₁ / ℓ ≤ σ₂ := by linarith only [h2, h7, hepspos]
    rw [hℓ] at h8
    exact hzf σ₂ τ (by linarith only [hτ]) h8 (by linarith only [hσ₂2])
  have hnorm₂ : 0 < ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
      ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hσ₂_nz
  have hlow : 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
      ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 1 + ℓ / d₀ := by
    have h := LFunction_inv_le_of_one_lt_re (χ := Work.FIArea6Hecke.R.chi4C) (σ := σ₂)
      (t := τ) hσ₂1 (by linarith only [hσ₂2])
    have h2 : σ₂ - 1 = eps := by rw [hσ₂]; ring
    have h3 : 1 + 1 / (σ₂ - 1) = 1 + ℓ / d₀ := by rw [h2, heps]; field_simp
    rw [h3] at h
    exact h
  have hlog₂ : Real.log (1 / (1 + ℓ / d₀)) ≤ Real.log
      ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hlow' : 1 / (1 + ℓ / d₀) ≤ ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
      have h := one_div_le_one_div_of_le (one_div_pos.mpr hnorm₂) hlow
      rwa [one_div_one_div] at h
    exact Real.log_le_log (one_div_pos.mpr (by positivity)) hlow'
  have hσ₂σ : σ₂ - σ ≤ 4 * d₀ / (3 * ℓ) := by
    have h1 : σ₂ - σ ≤ σ₂ - (1 - (min c₁ 1 / 24) / ℓ) := by linarith only [hσ']
    have h2 : σ₂ - (1 - (min c₁ 1 / 24) / ℓ) = eps + (min c₁ 1 / 24) / ℓ := by
      rw [hσ₂]; ring
    have h3 : eps + (min c₁ 1 / 24) / ℓ ≤ eps + eps / 3 := by linarith only [hc24]
    have h4 : eps + eps / 3 = 4 * d₀ / (3 * ℓ) := by rw [heps]; field_simp; ring
    linarith only [h1, h2.le, h2.ge, h3, h4.le, h4.ge]
  have hexpbound : K * (σ₂ - σ) ≤ 4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1) :=
    final_estimate hK_le hKnn hℓpos hd₀pos (by positivity) hσ₂σ
  by_cases hcase : σ ≤ σ₂
  · obtain ⟨Fp, _hFpdiff, hFpder, _hFpc, hFpre⟩ :=
      Commons.Analysis.Complex.logPrimitiveOnBall_analytic (g := DirichletCharacter.LFunction
        Work.FIArea6Hecke.R.chi4C) hLan hRpos hball_nz
    set Φ : ℝ → ℂ := fun u => Fp ((u : ℂ) + (τ : ℂ) * Complex.I) with hΦ
    have hΦderiv : ∀ u ∈ Set.Icc σ σ₂,
        HasDerivWithinAt Φ (deriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
          ((u : ℂ) + (τ : ℂ) * Complex.I)
          / DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
            ((u : ℂ) + (τ : ℂ) * Complex.I)) (Set.Icc σ σ₂) u := by
      intro u hu
      have hmem := hsegball u hu
      have hγ : HasDerivAt (fun u : ℝ => ((u : ℂ) + (τ : ℂ) * Complex.I)) 1 u := by
        have h1 : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 u := Complex.ofRealCLM.hasDerivAt
        simpa using h1.add_const ((τ : ℂ) * Complex.I)
      have hcomp := (hFpder _ hmem).comp u hγ
      have hcomp' : HasDerivAt (fun u : ℝ => Fp ((u : ℂ) + (τ : ℂ) * Complex.I))
          (deriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
            ((u : ℂ) + (τ : ℂ) * Complex.I)
            / DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
              ((u : ℂ) + (τ : ℂ) * Complex.I)) u := by
        simpa [Function.comp_def] using hcomp
      exact hcomp'.hasDerivWithinAt
    have hΦK : ∀ u ∈ Set.Icc σ σ₂,
        ‖deriv (DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
          ((u : ℂ) + (τ : ℂ) * Complex.I)
          / DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
            ((u : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ K :=
      fun u hu => hFbound _ (hseg u hu)
    have hmv := norm_sub_le_of_hasDerivWithinAt_Icc_chi4 hcase hΦderiv hΦK
    have hlogdiff : Real.log ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖
        - Real.log ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ K * (σ₂ - σ) := by
      have hb1 : ((σ : ℂ) + (τ : ℂ) * Complex.I) ∈ Metric.ball cb R :=
        hsegball σ (Set.left_mem_Icc.mpr hcase)
      have hb2 : ((σ₂ : ℂ) + (τ : ℂ) * Complex.I) ∈ Metric.ball cb R :=
        hsegball σ₂ (Set.right_mem_Icc.mpr hcase)
      have e1 : (Φ σ).re = Real.log ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by rw [hΦ]; exact hFpre _ hb1
      have e2 : (Φ σ₂).re = Real.log ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ₂ : ℂ) + (τ : ℂ) * Complex.I)‖ := by rw [hΦ]; exact hFpre _ hb2
      have h4 : (Φ σ₂).re - (Φ σ).re ≤ ‖Φ σ₂ - Φ σ‖ := by
        have := Complex.re_le_norm (Φ σ₂ - Φ σ)
        rw [Complex.sub_re] at this; exact this
      rw [e1, e2] at h4
      linarith only [h4, hmv]
    have hloglow : Real.log ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≥ Real.log (1 / (1 + ℓ / d₀)) - 4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1) := by
      linarith only [hlogdiff, hlog₂, hexpbound]
    have hpos_norm : 0 < ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
      refine norm_pos_iff.mpr ?_
      exact hball_nz _ (hsegball σ (Set.left_mem_Icc.mpr hcase))
    have hnorm_ge : Real.exp (Real.log (1 / (1 + ℓ / d₀))
        - 4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) ≤
        ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
      have h5 := Real.exp_le_exp.mpr hloglow
      rwa [Real.exp_log hpos_norm] at h5
    have hexp_eq : Real.exp (Real.log (1 / (1 + ℓ / d₀))
        - 4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))
        = (1 + ℓ / d₀)⁻¹ * Real.exp (-(4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))) := by
      rw [Real.exp_sub, Real.exp_log (one_div_pos.mpr (by positivity)), Real.exp_neg, one_div]
      ring
    rw [hexp_eq] at hnorm_ge
    have hfinal : 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (1 + ℓ / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) := by
      rw [div_le_iff₀ hpos_norm]
      have hprod : (1 + ℓ / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))
          * ((1 + ℓ / d₀)⁻¹
            * Real.exp (-(4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)))) = 1 := by
        have hA : (1 + ℓ / d₀) ≠ 0 := by positivity
        calc (1 + ℓ / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))
              * ((1 + ℓ / d₀)⁻¹
                * Real.exp (-(4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))))
            = ((1 + ℓ / d₀) * (1 + ℓ / d₀)⁻¹)
              * (Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))
                * Real.exp (-(4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)))) := by ring
          _ = 1 := by
              rw [mul_inv_cancel₀ hA, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have h2 := mul_le_mul_of_nonneg_left hnorm_ge
        (by positivity : (0:ℝ) ≤ (1 + ℓ / d₀)
          * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)))
      linarith only [hprod, h2]
    have hℓdiv : (1 + ℓ / d₀) ≤ (1 + 1 / d₀) * ℓ := by
      have h3 : 1 + ℓ / d₀ ≤ ℓ + ℓ / d₀ := by linarith only [hℓ1]
      have h4 : ℓ + ℓ / d₀ = (1 + 1 / d₀) * ℓ := by ring
      linarith only [h3, h4.le, h4.ge]
    calc 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (1 + ℓ / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) := hfinal
      _ ≤ ((1 + 1 / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))) * ℓ := by
          have h := mul_le_mul_of_nonneg_right hℓdiv
            (Real.exp_pos (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1))).le
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  · push_neg at hcase
    have hσ1 : 1 < σ := by rw [hσ₂] at hcase; linarith only [hcase, hepspos]
    have h := LFunction_inv_le_of_one_lt_re (χ := Work.FIArea6Hecke.R.chi4C) (σ := σ)
      (t := τ) hσ1 hσ2
    have h2 : 1 / (σ - 1) ≤ ℓ / d₀ := by
      rw [div_le_div_iff₀ (by linarith only [hσ1]) hd₀pos]
      have h3 : d₀ / ℓ < σ - 1 := by rw [hσ₂] at hcase; linarith only [heps, hcase, hepspos]
      have h4 : d₀ = ℓ * (d₀ / ℓ) := by field_simp
      have h5 : ℓ * (d₀ / ℓ) ≤ ℓ * (σ - 1) := mul_le_mul_of_nonneg_left h3.le hℓpos.le
      linarith only [h4, h5]
    have h6 : 1 + ℓ / d₀ ≤ (1 + 1 / d₀) * ℓ := by
      have h3 : 1 + ℓ / d₀ ≤ ℓ + ℓ / d₀ := by linarith only [hℓ1]
      have h4 : ℓ + ℓ / d₀ = (1 + 1 / d₀) * ℓ := by ring
      linarith only [h3, h4.le, h4.ge]
    have h9 : (1 : ℝ) ≤ Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) := by
      have h10 : 0 ≤ 4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1) := by positivity
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) := Real.exp_le_exp.mpr h10
    have h8 : (1 + 1 / d₀) * ℓ ≤ (1 + 1 / d₀)
        * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) * ℓ := by
      have h11 : 0 ≤ (1 + 1 / d₀) := by positivity
      have h12 : ℓ ≤ Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) * ℓ :=
        le_mul_of_one_le_left hℓpos.le h9
      have h13 : (1 + 1 / d₀) * ℓ
          ≤ (1 + 1 / d₀) * (Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) * ℓ) :=
        mul_le_mul_of_nonneg_left h12 h11
      linarith only [h13]
    calc 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 1 + 1 / (σ - 1) := h
      _ ≤ 1 + ℓ / d₀ := by linarith only [h2]
      _ ≤ (1 + 1 / d₀) * ℓ := h6
      _ ≤ (1 + 1 / d₀) * Real.exp (4 * d₀ / 3 * (8 * C₁ + 15 / d₀ + 5 * Cn + 1)) * ℓ := h8


/-- The compact piece `|t| ≤ 2`: non-vanishing in a logarithmic-width strip around `σ = 1` and
the inverse bound there. -/
theorem chi4C_smallT :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ε ≤ 1 / 4 ∧
      (∀ σ t : ℝ, |t| ≤ 3 → 1 - ε ≤ σ → σ ≤ 2 →
        DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
          ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) ∧
      (∀ σ t : ℝ, |t| ≤ 3 → 1 - ε ≤ σ → σ ≤ 2 →
        1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) := by
  obtain ⟨czf, hczf, hzf⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  have hzf4 : ∀ σ t : ℝ, t ≠ 0 → 1 - czf / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    fun σ t ht h _ => hzf Work.FIArea6Hecke.R.chi4C chi4C_isPrimitive chi4C_ne_one σ t ht h
  obtain ⟨β₁, hβ₁1, hβ₁⟩ := Work.FIArea6Hecke.R.real_zeros_bounded_above
    (Lam := DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C)
    (fun z _ => ((DirichletCharacter.differentiable_LFunction chi4C_ne_one).analyticAt z).analyticWithinAt)
    ⟨2, by norm_num, DirichletCharacter.LFunction_ne_zero_of_one_le_re _
      (Or.inl chi4C_ne_one) (by norm_num)⟩
  have hlog16pos : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have hczf' : 0 < czf / Real.log 20 := div_pos hczf hlog16pos
  have hβ₁pos : 0 < 1 - β₁ := by linarith only [hβ₁1]
  set ε : ℝ := min (min (1 / 4) (czf / Real.log 20)) (1 - β₁) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (lt_min (lt_min (by norm_num) hczf') hβ₁pos) (by norm_num)
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]
    have h1 : min (min (1 / 4) (czf / Real.log 20)) (1 - β₁)
        ≤ min (1 / 4) (czf / Real.log 20) := min_le_left _ _
    have h2 : min (1 / 4) (czf / Real.log 20) ≤ 1 / 4 := min_le_left _ _
    linarith only [h1, h2]
  have hεzf : ε ≤ czf / Real.log 20 := by
    rw [hε]
    have h1 : min (min (1 / 4) (czf / Real.log 20)) (1 - β₁)
        ≤ min (1 / 4) (czf / Real.log 20) := min_le_left _ _
    have h2 : min (1 / 4) (czf / Real.log 20) ≤ czf / Real.log 20 := min_le_right _ _
    linarith only [h1, h2, hczf']
  have hεβ : ε ≤ 1 - β₁ := by
    rw [hε]
    have h1 : min (min (1 / 4) (czf / Real.log 20)) (1 - β₁) ≤ 1 - β₁ := min_le_right _ _
    linarith only [h1, hβ₁pos]
  have hεhalf : ε ≤ (1 - β₁) / 2 := by
    rw [hε]
    have h1 : min (min (1 / 4) (czf / Real.log 20)) (1 - β₁) ≤ 1 - β₁ := min_le_right _ _
    linarith only [h1]
  have hne : ∀ σ t : ℝ, |t| ≤ 3 → 1 - ε ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t ht hσ hσ2 hzero
    rcases eq_or_ne t 0 with rfl | ht0
    · have hσ0 : 0 < σ := by linarith only [hσ, hεpos, hε4]
      have hσ1 : σ < 1 := by
        by_contra hcon
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _
          (Or.inl chi4C_ne_one) (le_of_not_gt hcon) (by simpa using hzero)
      have h := hβ₁ σ hσ0 hσ1 (by simpa using hzero)
      linarith only [h, hσ, hεhalf, hεpos]
    · have hlogcmp : Real.log (4 * (|t| + 2)) ≤ Real.log 20 := by
        apply Real.log_le_log (by linarith only [abs_nonneg t])
        linarith only [ht, abs_nonneg t]
      have h3 : czf / Real.log 20 ≤ czf / Real.log (4 * (|t| + 2)) := by
        rw [div_le_div_iff₀ hlog16pos (Real.log_pos (by linarith only [abs_nonneg t]))]
        exact mul_le_mul_of_nonneg_left hlogcmp hczf.le
      have h4 : ε ≤ czf / Real.log (4 * (|t| + 2)) := le_trans hεzf h3
      exact hzf4 σ t ht0 (by linarith only [h4, hσ]) hσ2 hzero
  set S : Set ℂ := {z : ℂ | 1 - ε ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 3} with hS
  have hScompact : IsCompact S := by
    have hclosed : IsClosed S := by
      rw [hS]
      exact (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
    have hbdd : Bornology.IsBounded S := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨5, fun z hz => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hz
      have h4 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h5 : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith only [h1, hε4], h2⟩
      have h6 : |z.im| ≤ 3 := by simpa using h3
      linarith only [h4, h5, h6]
    exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩
  have hcont : ContinuousOn (fun z : ℂ => 1 / ‖DirichletCharacter.LFunction
      Work.FIArea6Hecke.R.chi4C z‖) S := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((DirichletCharacter.differentiable_LFunction chi4C_ne_one).continuous.norm).continuousOn
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hz
      have hz3 : |z.im| ≤ 3 := by simpa using h3
      have hz' : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
      rw [hz']
      exact norm_ne_zero_iff.mpr (hne z.re z.im hz3 h1 h2)
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn hcont
  refine ⟨ε, |C| + 1, hεpos, by positivity, hε4, hne, ?_⟩
  intro σ t ht hσ hσ2
  have hz : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ S :=
    ⟨by simpa using hσ, by simpa using hσ2, by simpa using ht⟩
  have h := hC _ hz
  have hnn : 0 ≤ 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h
  linarith only [h, le_abs_self C]

end

theorem Lchi4InvSharp :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ σ t : ℝ,
      1 - c / Real.log (4 * (|t| + 2)) ≤ σ → σ ≤ 2 →
        1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * Real.log (4 * (|t| + 2)) := by
  obtain ⟨Cw, hCw, hwzs⟩ := chi4C_weightedZeroSum
  obtain ⟨czf, hczf, hzf⟩ := chi4C_zeroFree_offAxis
  have hc24pos : 0 < min czf 1 / 24 := by
    refine div_pos (lt_min hczf one_pos) (by norm_num)
  have hc24half : min czf 1 / 24 ≤ czf / 2 := by
    have h1 : min czf 1 ≤ czf := min_le_left _ _
    linarith only [h1, hczf]
  have hc24one : min czf 1 / 24 ≤ 1 := by
    have h1 : min czf 1 ≤ 1 := min_le_right _ _
    linarith only [h1]
  obtain ⟨Cb, hCb, hbound⟩ := chi4C_oneSidedBound hCw hczf hwzs hzf
    (c := min czf 1 / 24) hc24pos hc24half hc24one
  have hzf' : ∀ σ τ : ℝ, 1 ≤ |τ| → 1 - min czf 1 / 24 / Real.log (4 * (|τ| + 2)) ≤ σ →
      σ ≤ 2 → DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
        ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    intro σ τ hτ h h2
    refine hzf σ τ hτ ?_ h2
    have hpos : 0 < Real.log (4 * (|τ| + 2)) := Real.log_pos (by linarith only [abs_nonneg τ])
    have h1 : min czf 1 / 24 ≤ czf := by
      have h3 : min czf 1 ≤ czf := min_le_left _ _
      linarith only [h3, hczf]
    have h4 : (min czf 1 / 24) / Real.log (4 * (|τ| + 2))
        ≤ czf / Real.log (4 * (|τ| + 2)) :=
      div_le_div_of_nonneg_right h1 hpos.le
    linarith only [h, h4]
  obtain ⟨clip, Clip, hclip, hClip, hlip⟩ := chi4C_invBound_largeT (c₁ := min czf 1 / 24)
    hc24pos hCb hbound hzf'
  obtain ⟨ε, Csm, hε, hCsm, hε4, hne_sm, hsm⟩ := chi4C_smallT
  refine ⟨min clip (2 * ε), max Clip Csm, lt_min hclip (by linarith),
    lt_max_of_lt_left hClip, ?_⟩
  intro σ t hσ hσ2
  have hlog8 : (2 : ℝ) ≤ Real.log (4 * (|t| + 2)) := by
    have h1 : (8 : ℝ) ≤ 4 * (|t| + 2) := by linarith only [abs_nonneg t]
    have h2 : Real.log 8 ≤ Real.log (4 * (|t| + 2)) := Real.log_le_log (by norm_num) h1
    have h3 : (2 : ℝ) ≤ Real.log 8 := by
      have h5 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      have h6 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      rw [h5]; linarith only [h6]
    linarith only [h2, h3]
  have hlogpos : 0 < Real.log (4 * (|t| + 2)) := by linarith only [hlog8]
  by_cases ht : |t| ≤ 3
  · have hle : min clip (2 * ε) / Real.log (4 * (|t| + 2)) ≤ ε := by
      rw [div_le_iff₀ hlogpos]
      have h2 : min clip (2 * ε) ≤ 2 * ε := min_le_right _ _
      nlinarith only [h2, hlog8, hε]
    have hσ' : 1 - ε ≤ σ := by linarith only [hσ, hle]
    have h := hsm σ t ht hσ' hσ2
    have h3 : (1 : ℝ) ≤ Real.log (4 * (|t| + 2)) := le_trans (by norm_num) hlog8
    have h4 : 0 ≤ max Clip Csm := le_trans hClip.le (le_max_left _ _)
    calc 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Csm := h
      _ ≤ max Clip Csm * Real.log (4 * (|t| + 2)) := by
          calc Csm ≤ max Clip Csm * 1 := by rw [mul_one]; exact le_max_right _ _
            _ ≤ max Clip Csm * Real.log (4 * (|t| + 2)) :=
                mul_le_mul_of_nonneg_left h3 h4
  · push_neg at ht
    have h1 : min clip (2 * ε) ≤ clip := min_le_left _ _
    have h2 : min clip (2 * ε) / Real.log (4 * (|t| + 2))
        ≤ clip / Real.log (4 * (|t| + 2)) :=
      div_le_div_of_nonneg_right h1 hlogpos.le
    have hσ' : 1 - clip / Real.log (4 * (|t| + 2)) ≤ σ := by linarith only [hσ, h2]
    have h := hlip σ t (by linarith only [ht]) hσ' hσ2
    calc 1 / ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Clip * Real.log (4 * (|t| + 2)) := h
      _ ≤ max Clip Csm * Real.log (4 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos.le

end Work.FIArea6Road
