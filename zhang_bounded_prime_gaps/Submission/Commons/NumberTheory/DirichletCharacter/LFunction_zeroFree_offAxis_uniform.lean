import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight

open Complex DirichletCharacter Metric Filter Topology
open Commons.NumberTheory.DirichletCharacter
open scoped Real BigOperators Topology

set_option maxHeartbeats 8000000

namespace Commons.NumberTheory.DirichletCharacter
set_option autoImplicit false
noncomputable section

private lemma re_inv_shift (x T : ℝ) (u : ℂ) :
    (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - u)).re
      = (x - u.re) / ((x - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have h : ((x : ℂ) + Complex.I * (T : ℂ)) - u
      = ((x - u.re : ℝ) : ℂ) + ((T - u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  rw [h, one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_sub,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im, sub_zero, mul_one, zero_mul, add_zero]
  ring

private lemma re_finsum (f : ℂ → ℂ) (hfs : Function.HasFiniteSupport f) :
    (∑ᶠ u, f u).re = ∑ᶠ u, (f u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

private theorem pf_diff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s s₁ : ℂ)
    (hs : completedLFunction χ s ≠ 0) (hs₁ : completedLFunction χ s₁ ≠ 0) :
    Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u)))
      atTop (nhds (logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₁)) := by
  have h1 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
  have h2 := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s₁ hs₁
  have hsub := h1.sub h2
  have hgoal : (deriv (completedLFunction χ) s / completedLFunction χ s -
        deriv (completedLFunction χ) 0 / completedLFunction χ 0) -
      (deriv (completedLFunction χ) s₁ / completedLFunction χ s₁ -
        deriv (completedLFunction χ) 0 / completedLFunction χ 0) =
      deriv (completedLFunction χ) s / completedLFunction χ s -
        deriv (completedLFunction χ) s₁ / completedLFunction χ s₁ := by ring
  simp only [logDeriv_apply]
  rw [← hgoal]
  refine hsub.congr' ?_
  filter_upwards with R
  have hfs : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  have hfs₁ : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s₁ - u) + 1 / u)) :=
    ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset
      (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
  rw [← finsum_sub_distrib hfs hfs₁]
  exact finsum_congr fun u => by ring

/-- The rebased partial fraction gives: for `Re s > 1`, the real part of the log-derivative
of the completed `L`-function at `s` dominates the one at `-1 + i·Im s`. -/
theorem completedLFunction_logDeriv_re_ge_neg_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (σ T : ℝ) (hσ : 1 < σ) :
    (logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))).re
      ≤ (logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (T : ℂ))).re := by
  have hΛdiff : Differentiable ℂ (completedLFunction χ) := differentiable_completedLFunction hχ
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛdiff _
  have hΛs : completedLFunction χ ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
    intro h0
    have hzs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim _ h0
    have hre : (((σ : ℂ) + Complex.I * (T : ℂ))).re = σ := by simp
    linarith [hzs.2, hσ]
  have hΛs₁ : completedLFunction χ ((-1 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 := by
    intro h0
    have hzs := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim _ h0
    have hre : (((-1 : ℂ) + Complex.I * (T : ℂ))).re = -1 := by simp
    linarith [hzs.1]
  have hpf := pf_diff χ hχ hχprim ((σ : ℂ) + Complex.I * (T : ℂ)) ((-1 : ℂ) + Complex.I * (T : ℂ))
    hΛs hΛs₁
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (((σ : ℂ) + Complex.I * (T : ℂ)) - u) - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u = 0
    · simp [hD]
    · have hzero : completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R) hD
      have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hzero
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      apply mul_nonneg
      · exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u
      · rw [Complex.sub_re, re_inv_shift σ T u]
        have hA : 0 ≤ (σ - u.re) / ((σ - u.re) ^ 2 + (T - u.im) ^ 2) :=
          div_nonneg (by linarith [hσ, hstrip.2]) (by positivity)
        have hB : (1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)).re ≤ 0 := by
          rw [show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, re_inv_shift (-1) T u]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith [hstrip.1]) (by positivity)
        linarith
  have hnn : ∀ R : ℝ, 0 ≤ (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (((σ : ℂ) + Complex.I * (T : ℂ)) - u) - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)))).re := by
    intro R
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (((σ : ℂ) + Complex.I * (T : ℂ)) - u) - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u))) :=
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by rw [Function.mem_support] at hu ⊢; exact fun h => hu (by simp [h]))
    rw [re_finsum _ hfs]
    exact finsum_nonneg (hpoint R)
  have hlim : Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (((σ : ℂ) + Complex.I * (T : ℂ)) - u) - 1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)))).re) atTop
      (nhds ((logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (T : ℂ))
        - logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))).re)) :=
    (Complex.continuous_re.tendsto _).comp hpf
  have hge : 0 ≤ (logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (T : ℂ))
      - logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (T : ℂ))).re :=
    isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall hnn)
  rw [Complex.sub_re] at hge
  linarith

end
end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open Commons.NumberTheory.DirichletCharacter
open scoped Real BigOperators Topology

/-- Rebasing at `s = σ + iγ` above a zero `β + iγ ≤`: the real part of `Λ'/Λ` at `s` gains
the pole `1/(σ-β)`. -/
theorem completedLFunction_logDeriv_re_pole_rebased_uniform {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hz : completedLFunction χ ((β : ℂ) + Complex.I * (γ : ℂ)) = 0) :
    (logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (γ : ℂ))).re
      ≥ (logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (γ : ℂ))).re
        + 1 / (σ - β) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (γ : ℂ) with hs
  set s₁ : ℂ := (-1 : ℂ) + Complex.I * (γ : ℂ) with hs₁
  set ρ : ℂ := (β : ℂ) + Complex.I * (γ : ℂ) with hρ
  have hρre : ρ.re = β := by simp [hρ]
  have hρim : ρ.im = γ := by simp [hρ]
  have hΛdiff : Differentiable ℂ (completedLFunction χ) := differentiable_completedLFunction hχ
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛdiff _
  have hΛne : ∀ z : ℂ, completedLFunction χ z = 0 → 0 < z.re ∧ z.re < 1 := fun z hz =>
    Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim z hz
  have hΛs : completedLFunction χ s ≠ 0 := by
    intro h0; have := hΛne s h0; rw [show s.re = σ from by simp [hs]] at this; linarith [hσ, this.2]
  have hΛs₁ : completedLFunction χ s₁ ≠ 0 := by
    intro h0; have := hΛne s₁ h0; rw [show s₁.re = -1 from by simp [hs₁]] at this; linarith [this.1]
  have hpf := pf_diff χ hχ hχprim s s₁ hΛs hΛs₁
  -- the kernel at the zero `ρ` equals `1/(σ-β)`
  have hKρ : ((1 / (s - ρ) - 1 / (s₁ - ρ))).re = 1 / (σ - β) + 1 / (1 + β) := by
    have hsp : s - ρ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hs, hρ, hρre, hρim]
    have hs₁p : s₁ - ρ = ((-1 - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hs₁, hρ, hρre, hρim]
    have h1 : (σ - β) ≠ 0 := by linarith [hσ, hβ1]
    have h2 : (-1 - β) ≠ 0 := by linarith [hβ0]
    rw [hsp, hs₁p, Complex.sub_re]
    have e1 : (1 / (((σ - β : ℝ)) : ℂ)).re = 1 / (σ - β) := by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    have e2 : (1 / (((-1 - β : ℝ)) : ℂ)).re = 1 / (-1 - β) := by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [e1, e2]
    field_simp
    ring
  -- pointwise nonnegativity
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u = 0
    · simp [hD]
    · have hzero : completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R) hD
      have hstrip := hΛne u hzero
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      apply mul_nonneg
      · exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u
      · rw [Complex.sub_re, re_inv_shift σ γ u]
        have hA : 0 ≤ (σ - u.re) / ((σ - u.re) ^ 2 + (γ - u.im) ^ 2) :=
          div_nonneg (by linarith [hσ, hstrip.2]) (by positivity)
        have hB : (1 / (((-1 : ℂ) + Complex.I * (γ : ℂ)) - u)).re ≤ 0 := by
          rw [show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, re_inv_shift (-1) γ u]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith [hstrip.1]) (by positivity)
        linarith
  have hbig : ∀ᶠ R : ℝ in atTop,
      1 / (σ - β) ≤ (∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u)))).re := by
    rw [eventually_atTop]
    refine ⟨max ‖ρ‖ 0, fun R hR => ?_⟩
    have hρball : ρ ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (le_max_left _ _) hR
    have hDρ : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hΛdiff
        (fun hcon => (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
          (congrFun hcon 0)) hρball (by rw [hρ]; exact hz)
    have hmρ : (1 : ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
      have hnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by
        exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) ρ
      have hne : (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) ≠ 0 := by
        intro h0
        exact hDρ (by exact_mod_cast h0)
      have h1 : (0 : ℝ) < (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := lt_of_le_of_ne hnn (Ne.symm hne)
      have h2 : (1 : ℤ) ≤ (MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall 0 R)) ρ := by exact_mod_cast h1
      exact_mod_cast h2
    have hρterm : 1 / (σ - β) ≤ ((((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall 0 R)) ρ : ℤ) : ℂ) * (1 / (s - ρ) - 1 / (s₁ - ρ))).re := by
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero, hKρ]
      have hpos1 : 0 ≤ 1 / (σ - β) := div_nonneg zero_le_one (by linarith [hσ, hβ1])
      have hpos2 : 0 ≤ 1 / (1 + β) := div_nonneg zero_le_one (by linarith [hβ0])
      calc 1 / (σ - β) ≤ 1 * (1 / (σ - β) + 1 / (1 + β)) := by
              rw [one_mul]; linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hmρ (by linarith)
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))) :=
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by rw [Function.mem_support] at hu ⊢; intro hd; exact hu (by simp [hd]))
    have hfs' : Function.HasFiniteSupport (fun u : ℂ =>
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re) :=
      hfs.subset (fun u hu => by rw [Function.mem_support] at hu ⊢; intro h0; exact hu (by rw [h0]; simp))
    have hle := single_le_finsum ρ hfs' (fun j => hpoint R j)
    rw [re_finsum _ hfs]
    exact le_trans hρterm hle
  have hlim : Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u)))).re) atTop
      (nhds ((logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₁).re)) :=
    (Complex.continuous_re.tendsto _).comp hpf
  have hge : 1 / (σ - β) ≤
      (logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₁).re :=
    ge_of_tendsto hlim hbig
  rw [Complex.sub_re] at hge
  simp only [hs, hs₁] at hge ⊢
  linarith

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open Commons.NumberTheory.DirichletCharacter
open scoped Real BigOperators Topology

/-- Gamma-factor log-derivative bound on the strip `1 < Re s ≤ 5/4`. -/
private lemma norm_logDeriv_gammaFactor_le_strip' {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ τ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 5 / 4) :
    ‖logDeriv (gammaFactor χ) ((σ : ℂ) + Complex.I * (τ : ℂ))‖ ≤
      Real.log Real.pi / 2 + (1 / 2) * (Real.log (2 + |τ|) + 8) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun]
    have := norm_logDeriv_Gammaℝ_le σ τ (by linarith) (by linarith)
    simpa [hs] using this
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext hO.gammaFactor_def
    rw [hfun]
    have hsr : 0 < (s + 1).re := by rw [Complex.add_re]; simp [hs]; linarith
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ (s + 1) hsr
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
      have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    rw [hldcomp]
    have hS : s + 1 = ((σ + 1 : ℝ) : ℂ) + Complex.I * (τ : ℂ) := by rw [hs]; push_cast; ring
    rw [hS]
    have := norm_logDeriv_Gammaℝ_le (σ + 1) τ (by linarith) (by linarith)
    simpa using this

/-- Uniform (in the modulus) regular bound for the logarithmic derivative of `L(·, χ)`
on `1 < Re s ≤ 5/4`. -/
theorem LFunction_logDeriv_re_regular_uniform {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 →
      (-logDeriv (LFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
        8 * (Real.log (N : ℝ) + Real.log (2 + |τ|) + 1) := by
  intro σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs
  have hsre : 0 < s.re := by rw [hs]; simp; linarith
  have hLs : LFunction χ s ≠ 0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re
    (χ := χ) (s := s) (Or.inl hχ) (by rw [hs]; simp; linarith)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs
  have hreg : -(logDeriv (completedLFunction χ) s).re ≤
      Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 3 / 2 := by
    have h1 := completedLFunction_logDeriv_re_ge_neg_one χ hχ hχprim σ τ hσ1
    have h2 := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight
      χ hχ hχprim τ
    rw [hs]
    linarith [h1, h2]
  have hgam : (logDeriv (gammaFactor χ) s).re ≤
      Real.log Real.pi / 2 + (1 / 2) * (Real.log (2 + |τ|) + 8) :=
    le_trans (Complex.re_le_norm _) (norm_logDeriv_gammaFactor_le_strip' χ hσ1 hσ2)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hlogτ : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hsplit : -(logDeriv (LFunction χ) s).re
      = -(logDeriv (completedLFunction χ) s).re + (logDeriv (gammaFactor χ) s).re := by
    rw [hdec, Complex.add_re]; ring
  rw [Complex.neg_re, hsplit]
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  simp only [hs]
  nlinarith [hreg, hgam, hpi, hlogN, hlogτ]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology

/-- Uniform (in the modulus) pole bound for the logarithmic derivative of `L(·, χ)`. -/
theorem LFunction_logDeriv_re_pole_uniform_sharp {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∀ σ τ β : ℝ, 1 < σ → σ ≤ 5 / 4 → 0 < β → β < 1 →
      LFunction χ ((β : ℂ) + Complex.I * (τ : ℂ)) = 0 →
      (-logDeriv (LFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
        -1 / (σ - β) + 8 * (Real.log (N : ℝ) + Real.log (2 + |τ|) + 1) := by
  intro σ τ β hσ1 hσ2 hβ0 hβ1 hz
  set s : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs
  have hsre : 0 < s.re := by rw [hs]; simp; linarith
  have hLs : LFunction χ s ≠ 0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re
    (χ := χ) (s := s) (Or.inl hχ) (by rw [hs]; simp; linarith)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs
  have hΛz : completedLFunction χ ((β : ℂ) + Complex.I * (τ : ℂ)) = 0 := by
    rw [Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (β : ℂ) + Complex.I * (τ : ℂ)) (by simp; linarith), hz, zero_mul]
  have hpol := completedLFunction_logDeriv_re_pole_rebased_uniform χ hχ hχprim hσ1 hβ0 hβ1 hΛz
  have h2 := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight
    χ hχ hχprim τ
  have hreg : -(logDeriv (completedLFunction χ) s).re ≤
      -(1 / (σ - β)) + (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 3 / 2) := by
    rw [hs]
    have hb1 : -(logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re
        ≤ -(logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (τ : ℂ))).re - 1 / (σ - β) := by
      linarith [hpol]
    have hb3 : -(logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re
        ≤ (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 3 / 2) - 1 / (σ - β) :=
      hb1.trans (sub_le_sub_right h2 _)
    linarith [hb3]
  have hgam : (logDeriv (gammaFactor χ) s).re ≤
      Real.log Real.pi / 2 + (1 / 2) * (Real.log (2 + |τ|) + 8) :=
    le_trans (Complex.re_le_norm _) (norm_logDeriv_gammaFactor_le_strip' χ hσ1 hσ2)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hlogτ : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hsplit : -(logDeriv (LFunction χ) s).re
      = -(logDeriv (completedLFunction χ) s).re + (logDeriv (gammaFactor χ) s).re := by
    rw [hdec, Complex.add_re]; ring
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  rw [Complex.neg_re, hsplit, neg_div]
  nlinarith [hreg, hgam, hpi, hlogN, hlogτ]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter MeromorphicOn Filter Set
open scoped Real BigOperators Topology

private lemma bracket_nonneg {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hcase : z = w ^ 2 ∨ w = 0) : 0 ≤ 3 + 4 * w.re + z.re := by
  rcases hcase with h | h
  · rw [h, sq]
    have hns : (w * w).re = w.re * w.re - w.im * w.im := by
      rw [Complex.mul_re]
    have hnorm : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (1 + w.re), hw, hnorm, norm_nonneg w]
  · rw [h, Complex.zero_re]
    have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have h2 : -(1:ℝ) ≤ z.re := by
      have h3 := Complex.re_le_norm (-z)
      rw [Complex.neg_re] at h3
      have h4 : ‖(-z : ℂ)‖ = ‖z‖ := norm_neg z
      rw [h4] at h3
      linarith
    linarith

private lemma summable_LSeries_term {N : ℕ} (χ : DirichletCharacter ℂ N) {σ τ : ℝ}
    (hσ : 1 < σ) :
    Summable (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) ((σ : ℂ) + Complex.I * (τ : ℂ))) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ σ) ?_ ?_
  · exact Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ
  · intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn]
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hre : (((σ : ℂ) + Complex.I * (τ : ℂ))).re = σ := by simp
      rw [hre, if_neg hn]
      have hval : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := norm_le_one χ (n : ZMod N)
      have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
      have hpos : (0:ℝ) < (n:ℝ) ^ σ := Real.rpow_pos_of_pos (by linarith) σ
      calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod N)‖ / (n:ℝ) ^ σ
          ≤ ArithmeticFunction.vonMangoldt n * 1 / (n:ℝ) ^ σ := by
            gcongr
        _ = ArithmeticFunction.vonMangoldt n / (n:ℝ) ^ σ := by ring

/-- The termwise inequality behind the three-four-one method: the combined `n`-th term of the
three Dirichlet series has nonnegative real part. -/
private lemma termwise_nonneg {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → (ψ (a : ZMod M)) = ((χ (a : ZMod N)) : ℂ) ^ 2)
    {σ τ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
      + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
          ((σ : ℂ) + Complex.I * (τ : ℂ)) n
      + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ))
          ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ)) n).re := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    set s₁ : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs1
    set s₂ : ℂ := (σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ) with hs2
    set c : ℂ := (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) with hc
    set e : ℝ := (n : ℝ) ^ (-σ) with he
    have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    have h0 : (n : ℂ) ^ (-(σ : ℂ)) = ((e : ℝ) : ℂ) := by
      have hneg : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
      rw [he, hbase, hneg, ← Complex.ofReal_cpow (le_of_lt hpos)]
    have h1 : (n : ℂ) ^ (-s₁) = ((e : ℝ) : ℂ) * c := by
      have harg : -s₁ = -(σ : ℂ) + (-(Complex.I * (τ : ℂ))) := by rw [hs1]; push_cast; ring
      calc (n : ℂ) ^ (-s₁) = (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [harg, Complex.cpow_add _ _ hn0]
        _ = ((e : ℝ) : ℂ) * c := by rw [h0, hc]
    have h2 : (n : ℂ) ^ (-s₂) = ((e : ℝ) : ℂ) * c ^ 2 := by
      have harg : -s₂ = -(σ : ℂ) + (-(Complex.I * (τ : ℂ))) + (-(Complex.I * (τ : ℂ))) := by
        rw [hs2]; push_cast; ring
      calc (n : ℂ) ^ (-s₂)
          = (n : ℂ) ^ (-(σ : ℂ) + (-(Complex.I * (τ : ℂ)))) *
              (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [harg, Complex.cpow_add _ _ hn0]
        _ = ((n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) *
              (n : ℂ) ^ (-(Complex.I * (τ : ℂ))) := by
            rw [Complex.cpow_add _ _ hn0]
        _ = ((e : ℝ) : ℂ) * c ^ 2 := by rw [h0, hc]; ring
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    rw [← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_neg]
    rw [h0, h1, h2]
    have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hfac : 3 * ((ArithmeticFunction.vonMangoldt n : ℂ) * ((e : ℝ) : ℂ))
        + 4 * ((ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (((e : ℝ) : ℂ) * c))
        + (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ) * (((e : ℝ) : ℂ) * c ^ 2)
        = (((e : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) *
            (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2))) := by
      ring
    rw [hfac, Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, zero_mul, sub_zero]
    have hw : ‖(χ (n : ZMod N) : ℂ) * c‖ ≤ 1 := by
      rw [norm_mul]
      have h1 : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := norm_le_one χ (n : ZMod N)
      have h2 : ‖c‖ = 1 := by
        rw [hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simp
      rw [h2, mul_one]
      exact h1
    have hz : ‖(ψ (n : ZMod M) : ℂ) * c ^ 2‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      have h1 : ‖(ψ (n : ZMod M) : ℂ)‖ ≤ 1 := norm_le_one ψ (n : ZMod M)
      have h2 : ‖c‖ = 1 := by
        rw [hc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simp
      rw [h2, one_pow, mul_one]
      exact h1
    have hcase : (ψ (n : ZMod M) : ℂ) * c ^ 2 = ((χ (n : ZMod N) : ℂ) * c) ^ 2
        ∨ (χ (n : ZMod N) : ℂ) * c = 0 := by
      by_cases hcop : IsCoprime (n : ℤ) (N : ℤ)
      · left
        have h := hval (n : ℤ) hcop
        simp only [Int.cast_natCast] at h
        rw [h]; ring
      · right
        have : (χ (n : ZMod N) : ℂ) = 0 := by
          have hcast : (n : ZMod N) = ((n : ℤ) : ZMod N) := by push_cast; ring
          rw [hcast, DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)]
          exact hcop
        rw [this, zero_mul]
    have hZ : 0 ≤ (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2).re := by
      simpa [Complex.add_re] using bracket_nonneg hw hz hcase
    have he0 : 0 ≤ e := by
      rw [he]; positivity
    have hprod : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
        (3 + 4 * ((χ (n : ZMod N) : ℂ) * c) + (ψ (n : ZMod M) : ℂ) * c ^ 2).re :=
      mul_nonneg hΛ hZ
    have := mul_nonneg he0 hprod
    simpa using this

lemma three_four_one_nonneg_uniform {N M : ℕ} [NeZero N] [NeZero M]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → (ψ (a : ZMod M)) = ((χ (a : ZMod N)) : ℂ) ^ 2)
    {σ τ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re
      + (-logDeriv (DirichletCharacter.LFunction ψ)
          ((σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ))).re := by
  classical
  set s₁ : ℂ := (σ : ℂ) + Complex.I * (τ : ℂ) with hs1
  set s₂ : ℂ := (σ : ℂ) + Complex.I * ((2 * τ : ℝ) : ℂ) with hs2
  have hs1re : s₁.re = σ := by simp [hs1]
  have hs2re : s₂.re = σ := by simp [hs2]
  have hs1im : s₁.im = τ := by simp [hs1]
  have hs2im : s₂.im = 2 * τ := by simp [hs2]
  have hσ1 : (1:ℝ) < s₁.re := hs1re ▸ hσ
  have hσ2 : (1:ℝ) < s₂.re := hs2re ▸ hσ
  -- the three series identities
  have hζ : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) := by
    have h := LFunction_logDeriv_eq_neg_LSeries_vonMangoldt (1 : DirichletCharacter ℂ 1)
      (s := (σ : ℂ)) (by simpa using hσ)
    rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply] at h
    have h2 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 : DirichletCharacter ℂ 1) (n : ZMod 1))
        = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
        have : (n : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [h1, mul_one]
    rw [h2] at h
    have h3 := congrArg Neg.neg h
    simp only [neg_neg] at h3
    simpa [neg_div] using h3
  have hχ : -logDeriv (DirichletCharacter.LFunction χ) s₁
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁ := by
    rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ (s := s₁) hσ1, neg_neg]
  have hψ : -logDeriv (DirichletCharacter.LFunction ψ) s₂
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ)) s₂ := by
    rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt ψ (s := s₂) hσ2, neg_neg]
  rw [hζ, hχ, hψ]
  -- summability of the three series
  have hsζ : Summable (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ : ℂ)) := by
    have h := summable_LSeries_term (1 : DirichletCharacter ℂ 1) (τ := 0) hσ
    have h2 : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 : DirichletCharacter ℂ 1) (n : ZMod 1))
        = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
        have : (n : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [h1, mul_one]
    rw [h2] at h
    simpa using h
  have hsχ : Summable (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁) := by
    have := summable_LSeries_term χ (σ := σ) (τ := τ) hσ
    simpa [s₁] using this
  have hsψ : Summable (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod M) : ℂ)) s₂) := by
    have := summable_LSeries_term ψ (σ := σ) (τ := 2 * τ) hσ
    simpa [s₂] using this
  -- combine into one complex number
  have hsplit : 3 * (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s₁).re
      + (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (ψ (n : ZMod M) : ℂ)) s₂).re
      = ((3 : ℂ) * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
        + 4 * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁
        + LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hsplit]
  have hstep : (3 : ℂ) * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)
      + 4 * LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s₁
      + LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (ψ (n : ZMod M) : ℂ)) s₂
      = ∑' n : ℕ, (3 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (σ : ℂ) n
        + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁ n
        + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂ n) := by
    have h1 := Summable.tsum_add (hsζ.mul_left (3:ℂ)) (hsχ.mul_left (4:ℂ))
    have h2 := Summable.tsum_add ((hsζ.mul_left (3:ℂ)).add (hsχ.mul_left (4:ℂ))) hsψ
    have h3 := tsum_mul_left (L := SummationFilter.unconditional ℕ) (a := (3:ℂ))
      (f := fun n : ℕ => LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ) n)
    have h4 := tsum_mul_left (L := SummationFilter.unconditional ℕ) (a := (4:ℂ))
      (f := fun n : ℕ => LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s₁ n)
    simp only [LSeries]
    calc (3 : ℂ) * (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ : ℂ) n)
        + 4 * (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (χ (n : ZMod N) : ℂ)) s₁ n)
        + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ψ (n : ZMod M) : ℂ)) s₂ n)
        = (∑' n : ℕ, (3:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
              (σ : ℂ) n)
          + (∑' n : ℕ, (4:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)) s₁ n)
          + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h3, h4]
      _ = (∑' n : ℕ, ((3:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
            + (4:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ (n : ZMod N) : ℂ)) s₁ n))
          + (∑' n : ℕ, LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h1]
      _ = ∑' n : ℕ, ((3:ℂ) * LSeries.term (fun n : ℕ =>
              (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
            + (4:ℂ) * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (χ (n : ZMod N) : ℂ)) s₁ n
            + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
              (ψ (n : ZMod M) : ℂ)) s₂ n) := by rw [h2]
  rw [hstep]
  have hsumm : Summable (fun n : ℕ => 3 * LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n
      + 4 * LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s₁ n
      + LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (ψ (n : ZMod M) : ℂ)) s₂ n) :=
    ((hsζ.mul_left (3:ℂ)).add (hsχ.mul_left (4:ℂ))).add hsψ
  rw [Complex.re_tsum hsumm]
  exact tsum_nonneg (fun n => termwise_nonneg χ ψ hval hσ n)




end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology

/-- `Re (1/((-1 : ℂ) + iT - u)) = (-1 - Re u)/(((-1 - Re u)^2 + (T - Im u)^2))`. -/
private lemma re_inv_neg1 (T : ℝ) (u : ℂ) :
    (1 / (((-1 : ℂ) + Complex.I * (T : ℂ)) - u)).re
      = (-1 - u.re) / ((-1 - u.re) ^ 2 + (T - u.im) ^ 2) := by
  rw [show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, re_inv_shift (-1) T u]

/-- Two-pole rebasing at height `γ`: keeping the two conjugate zeros `β ± iγ` gives, on the
line `Im = γ`, the doubled pole `1/(σ-β) + (σ-β)/((σ-β)²+4γ²)`. -/
theorem completedLFunction_logDeriv_re_two_poles {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 0)
    (hz : completedLFunction χ ((β : ℂ) + Complex.I * (γ : ℂ)) = 0)
    (hzc : completedLFunction χ ((β : ℂ) - Complex.I * (γ : ℂ)) = 0) :
    (logDeriv (completedLFunction χ) ((σ : ℂ) + Complex.I * (γ : ℂ))).re
      ≥ (logDeriv (completedLFunction χ) ((-1 : ℂ) + Complex.I * (γ : ℂ))).re
        + 1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) := by
  set s : ℂ := (σ : ℂ) + Complex.I * (γ : ℂ) with hs
  set s₁ : ℂ := (-1 : ℂ) + Complex.I * (γ : ℂ) with hs₁
  set ρ : ℂ := (β : ℂ) + Complex.I * (γ : ℂ) with hρ
  set ρc : ℂ := (β : ℂ) - Complex.I * (γ : ℂ) with hρc
  have hρre : ρ.re = β := by simp [hρ]
  have hρim : ρ.im = γ := by simp [hρ]
  have hρcre : ρc.re = β := by simp [hρc]
  have hρcim : ρc.im = -γ := by simp [hρc]
  have hρne : ρ ≠ ρc := by
    intro h
    have := congrArg Complex.im h
    rw [hρim, hρcim] at this
    exact hγ (by linarith)
  have hΛdiff : Differentiable ℂ (completedLFunction χ) := differentiable_completedLFunction hχ
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ (completedLFunction χ) (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛdiff _
  have hΛne : ∀ z : ℂ, completedLFunction χ z = 0 → 0 < z.re ∧ z.re < 1 := fun z hz =>
    Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim z hz
  have hΛs : completedLFunction χ s ≠ 0 := by
    intro h0; have := hΛne s h0; rw [show s.re = σ from by simp [hs]] at this; linarith [hσ, this.2]
  have hΛs₁ : completedLFunction χ s₁ ≠ 0 := by
    intro h0; have := hΛne s₁ h0; rw [show s₁.re = -1 from by simp [hs₁]] at this; linarith [this.1]
  have hpf := pf_diff χ hχ hχprim s s₁ hΛs hΛs₁
  have hspos : 0 < σ - β := by linarith [hσ, hβ1]
  have hfour : 0 < (σ - β) ^ 2 + 4 * γ ^ 2 := by positivity
  have hKρ : 1 / (σ - β) ≤ (1 / (s - ρ) - 1 / (s₁ - ρ)).re := by
    rw [Complex.sub_re, re_inv_shift σ γ ρ, re_inv_neg1 γ ρ, hρre, hρim]
    have hA : (σ - β) / ((σ - β) ^ 2 + (γ - γ) ^ 2) = 1 / (σ - β) := by
      simp only [sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero, pow_two]
      field_simp
    have hB : (-1 - β) / ((-1 - β) ^ 2 + (γ - γ) ^ 2) ≤ 0 := by
      simp only [sub_self, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [hA]; linarith
  have hKρc : (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) ≤ (1 / (s - ρc) - 1 / (s₁ - ρc)).re := by
    rw [Complex.sub_re, re_inv_shift σ γ ρc, re_inv_neg1 γ ρc, hρcre, hρcim]
    rw [show (γ - -γ : ℝ) = 2 * γ by ring, mul_pow, show (2:ℝ)^2 = 4 by norm_num]
    have hB : (-1 - β) / ((-1 - β) ^ 2 + 4 * γ ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u = 0
    · simp [hD]
    · have hzero : completedLFunction χ u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R) hD
      have hstrip := hΛne u hzero
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      apply mul_nonneg
      · exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u
      · rw [Complex.sub_re, re_inv_shift σ γ u, re_inv_neg1 γ u]
        have hA : 0 ≤ (σ - u.re) / ((σ - u.re) ^ 2 + (γ - u.im) ^ 2) :=
          div_nonneg (by linarith [hσ, hstrip.2]) (by positivity)
        have hB : (-1 - u.re) / ((-1 - u.re) ^ 2 + (γ - u.im) ^ 2) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith [hstrip.1]) (by positivity)
        linarith
  have hmult : ∀ (R : ℝ) (u : ℂ), (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u ≠ 0 →
      (1 : ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by
    intro R u hDu
    have hnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by
      exact_mod_cast Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u
    have hne : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) ≠ 0 := by
      intro h0; exact hDu (by exact_mod_cast h0)
    have h1 : (0 : ℝ) < _ := lt_of_le_of_ne hnn (Ne.symm hne)
    have h2 : (1 : ℤ) ≤ (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u := by
      exact_mod_cast h1
    exact_mod_cast h2
  -- generic term identity
  have htermeq : ∀ (R : ℝ) (u : ℂ),
      ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u))).re
      = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) *
        ((1 / (s - u) - 1 / (s₁ - u)).re) := by
    intro R u
    rw [Complex.mul_re]
    have hDre : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
        = (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
    have hDim : ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im = 0 := by simp
    rw [hDre, hDim, zero_mul, sub_zero]
  have hbig : ∀ᶠ R : ℝ in atTop,
      1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) ≤ (∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u)))).re := by
    rw [eventually_atTop]
    refine ⟨max ‖ρ‖ ‖ρc‖, ?_⟩
    intro R hR
    have hρball : ρ ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_trans (le_max_left _ _) hR
    have hρcball : ρc ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_trans (le_max_right _ _) hR
    have hDρ : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hΛdiff
        (fun hcon => (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
          (congrFun hcon 0)) hρball (by rw [hρ]; exact hz)
    have hDρc : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρc ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hΛdiff
        (fun hcon => (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
          (congrFun hcon 0)) hρcball (by rw [hρc]; exact hzc)
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))) :=
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by rw [Function.mem_support] at hu ⊢; intro hd; exact hu (by simp [hd]))
    have hsupp : (Function.support (fun u : ℂ =>
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re)).Finite :=
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by
          rw [Function.mem_support] at hu ⊢
          intro hd
          exact hu (by rw [htermeq R u, hd]; simp))
    let S : Finset ℂ := hsupp.toFinset
    have hSmem : ∀ u : ℂ, u ∈ S ↔
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re ≠ 0 := by
      intro u; dsimp [S]; rw [Set.Finite.mem_toFinset, Function.mem_support]
    have hsm : ∀ u ∈ S, 0 ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u))).re := fun u _ => hpoint R u
    have hmemρ : ρ ∈ S := (hSmem ρ).mpr (by
      rw [htermeq R ρ]
      have hKpos : 0 < (1 / (s - ρ) - 1 / (s₁ - ρ)).re := lt_of_lt_of_le (one_div_pos.mpr hspos) hKρ
      exact ne_of_gt (mul_pos (lt_of_lt_of_le one_pos (hmult R ρ hDρ)) hKpos))
    have hmemρc : ρc ∈ S := (hSmem ρc).mpr (by
      rw [htermeq R ρc]
      have hKpos : 0 < (1 / (s - ρc) - 1 / (s₁ - ρc)).re :=
        lt_of_lt_of_le (div_pos hspos hfour) hKρc
      exact ne_of_gt (mul_pos (lt_of_lt_of_le one_pos (hmult R ρc hDρc)) hKpos))
    have hρterm : 1 / (σ - β) ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℂ) *
        (1 / (s - ρ) - 1 / (s₁ - ρ))).re := by
      rw [htermeq R ρ]
      have hKnn : 0 ≤ (1 / (s - ρ) - 1 / (s₁ - ρ)).re :=
        le_trans (le_of_lt (one_div_pos.mpr hspos)) hKρ
      calc 1 / (σ - β) ≤ (1 / (s - ρ) - 1 / (s₁ - ρ)).re := hKρ
        _ = 1 * (1 / (s - ρ) - 1 / (s₁ - ρ)).re := by rw [one_mul]
        _ ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℝ) *
              ((1 / (s - ρ) - 1 / (s₁ - ρ)).re) := mul_le_mul_of_nonneg_right (hmult R ρ hDρ) hKnn
    have hρcterm : (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) ≤ ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρc : ℤ) : ℂ) *
        (1 / (s - ρc) - 1 / (s₁ - ρc))).re := by
      rw [htermeq R ρc]
      have hnn : 0 ≤ (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) := div_nonneg (le_of_lt hspos) (le_of_lt hfour)
      calc (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
          ≤ 1 * ((σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)) := by rw [one_mul]
        _ ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρc : ℤ) : ℝ) *
              ((σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)) := mul_le_mul_of_nonneg_right (hmult R ρc hDρc) hnn
        _ ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρc : ℤ) : ℝ) *
              ((1 / (s - ρc) - 1 / (s₁ - ρc)).re) :=
              mul_le_mul_of_nonneg_left hKρc (le_trans zero_le_one (hmult R ρc hDρc))
    have hsub : Function.support (fun u : ℂ =>
        ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re) ⊆ (S : Set ℂ) := by
      intro u hu; rw [Set.Finite.coe_toFinset]; exact hu
    rw [re_finsum _ hfs, finsum_eq_sum_of_support_subset _ hsub]
    have hpairle : (∑ u ∈ ({ρ, ρc} : Finset ℂ), ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re) ≤ ∑ u ∈ S, ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => hpoint R u)
      intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hmemρ
      · exact hmemρc
    have hpair : (∑ u ∈ ({ρ, ρc} : Finset ℂ), ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
          (1 / (s - u) - 1 / (s₁ - u))).re)
        = ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρ : ℤ) : ℂ) *
            (1 / (s - ρ) - 1 / (s₁ - ρ))).re
          + ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) ρc : ℤ) : ℂ) *
            (1 / (s - ρc) - 1 / (s₁ - ρc))).re := by
      rw [Finset.sum_insert (by simpa [Finset.mem_singleton] using hρne), Finset.sum_singleton]
    linarith [hpairle, hpair, hρterm, hρcterm]
  have hlim : Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) - 1 / (s₁ - u)))).re) atTop
      (nhds ((logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₁).re)) :=
    (Complex.continuous_re.tendsto _).comp hpf
  have hge : 1 / (σ - β) + (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) ≤
      (logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₁).re :=
    ge_of_tendsto hlim hbig
  rw [Complex.sub_re] at hge
  rw [hs, hs₁] at hge
  linarith

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology

/-- Conversion of the two-poles completed-L bound to the `L`-function, with the uniform constant. -/
theorem LFunction_logDeriv_re_two_poles_uniform {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∀ σ γ β : ℝ, 1 < σ → σ ≤ 5 / 4 → 0 < β → β < 1 → γ ≠ 0 →
      LFunction χ ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
      completedLFunction χ ((β : ℂ) - Complex.I * (γ : ℂ)) = 0 →
      (-logDeriv (LFunction χ) ((σ : ℂ) + Complex.I * (γ : ℂ))).re ≤
        -1 / (σ - β) - (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) +
          8 * (Real.log (N : ℝ) + Real.log (2 + |γ|) + 1) := by
  intro σ γ β hσ1 hσ2 hβ0 hβ1 hγ hz hzc
  set s : ℂ := (σ : ℂ) + Complex.I * (γ : ℂ) with hs
  have hsre : 0 < s.re := by rw [hs]; simp; linarith
  have hLs : LFunction χ s ≠ 0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re
    (χ := χ) (s := s) (Or.inl hχ) (by rw [hs]; simp; linarith)
  have hdec := logDeriv_completedLFunction_eq_add χ hχ s hsre hLs
  have hΛz : completedLFunction χ ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 := by
    rw [Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (β : ℂ) + Complex.I * (γ : ℂ)) (by simp; linarith), hz, zero_mul]
  have hpol := completedLFunction_logDeriv_re_two_poles χ hχ hχprim hσ1 hβ0 hβ1 hγ hΛz hzc
  have h2 := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_re_tight χ hχ hχprim γ
  have hreg : -(logDeriv (completedLFunction χ) s).re ≤
      -(1 / (σ - β)) - (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) +
        (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |γ|) + 3 / 2) := by
    rw [hs]
    linarith [hpol, h2]
  have hgam : (logDeriv (gammaFactor χ) s).re ≤
      Real.log Real.pi / 2 + (1 / 2) * (Real.log (2 + |γ|) + 8) :=
    le_trans (Complex.re_le_norm _) (norm_logDeriv_gammaFactor_le_strip' χ hσ1 hσ2)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hlogτ : 0 ≤ Real.log (2 + |γ|) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have hsplit : -(logDeriv (LFunction χ) s).re
      = -(logDeriv (completedLFunction χ) s).re + (logDeriv (gammaFactor χ) s).re := by
    rw [hdec, Complex.add_re]; ring
  have hpi : Real.log Real.pi / 2 ≤ 1 := by
    have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
    have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log (2:ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  rw [Complex.neg_re, hsplit]
  have hcnb : -(1 / (σ - β)) ≤ 0 := by
    apply neg_nonpos.mpr; exact le_of_lt (div_pos one_pos (by linarith))
  have hcnb2 : -((σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)) ≤ 0 := by
    apply neg_nonpos.mpr; exact div_nonneg (by linarith) (by positivity)
  have hr' : -(logDeriv (completedLFunction χ) s).re ≤
      -(1 / (σ - β)) - (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) +
        (Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |γ|) + 3 / 2) := hreg
  have e : -(1 / (σ - β)) - (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2)
      = -1 / (σ - β) - (σ - β) / ((σ - β) ^ 2 + 4 * γ ^ 2) := by
    rw [neg_div]
  rw [e] at hr'
  nlinarith [hr', hgam, hpi, hlogN, hlogτ, hcnb, hcnb2]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter
open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology

/-- Uniform upper bound for `-Re (ζ'/ζ)` on `1 < Re s ≤ 2` and `|Im s| ≥ 1/2`, via the
elementary sign argument for the Riemann ξ-function. -/
theorem zeta_logDeriv_re_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → 1 / 2 ≤ |t| →
      (-deriv riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ)) /
          riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        C * (Real.log (2 + |t|) + 1) := by
  obtain ⟨Cξ, hCξpos, hξ⟩ := Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨Cξ + 1 / 2 * Real.log Real.pi + 6, by linarith, ?_⟩
  intro σ t hσ1 hσ2 ht
  have hlogpi : (Complex.log (Real.pi : ℂ)).re = Real.log Real.pi := by
    rw [show Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from
      (Complex.ofReal_log (le_of_lt Real.pi_pos)).symm]
    simp
  have hd : (Complex.digamma (1 + ((σ : ℂ) + Complex.I * (t : ℂ)) / 2)).re ≤
      Real.log (2 + |t / 2|) + 8 := by
    have harg : 1 + ((σ : ℂ) + Complex.I * (t : ℂ)) / 2 =
        ((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    exact le_trans (Complex.re_le_norm _)
      (Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound (1 + σ / 2) (t / 2)
        (by linarith) (by linarith))
  have hinv : (1 / (((σ : ℂ) + Complex.I * (t : ℂ)) - 1)).re ≤ 2 := by
    rw [re_inv_shift σ t 1]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    have hkey : (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (σ - 1 - 1 / 2), sq_abs t, ht, abs_nonneg t]
    linarith
  have hre := Commons.NumberTheory.Zeta.logDerivRe_eq ((σ : ℂ) + Complex.I * (t : ℂ))
    (by simp; linarith)
  have hξl : -Cξ ≤ (logDeriv Commons.NumberTheory.Zeta.xi ((σ : ℂ) + Complex.I * (t : ℂ))).re :=
    hξ ((σ : ℂ) + Complex.I * (t : ℂ)) (by simp; linarith)
  have hlog2t : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log (by positivity)
    have : |t / 2| ≤ |t| := by rw [abs_div]; norm_num
    linarith
  have hlogpos : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  rw [hre, hlogpi]
  nlinarith [hξl, hd, hinv, hlog2t, hlogpos, hCξpos, hpi, Real.pi_gt_three]

end Commons.NumberTheory.DirichletCharacter


open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Commons.NumberTheory.DirichletCharacter
noncomputable section

private lemma isUnit_zmod_of_isCoprime {N : ℕ} {a : ℤ} (ha : IsCoprime a (N : ℤ)) :
    IsUnit (a : ZMod N) :=
  (ZMod.coe_int_isUnit_iff_isCoprime a N).mpr (isCoprime_comm.mpr ha)

/-- Final arithmetic step: `4/s ≤ (39/10)·A·ℓ` and `x = 1/(Aℓ)` give `1/(100Aℓ) ≤ s - x`. -/
private lemma arith_final {A ℓ s x : ℝ} (hℓ : 1 ≤ ℓ) (hx : x = 1 / (A * ℓ))
    (hspos : 0 < s) (h : 4 * (1 / s) ≤ (39 / 10) * A * ℓ) : 1 / (100 * A * ℓ) ≤ s - x := by
  have he : 4 * (1 / s) = 4 / s := by ring
  rw [he] at h
  have h4 : 0 < 4 / s := div_pos (by norm_num) hspos
  have hcpos : 0 < (39 / 10) * A * ℓ := lt_of_lt_of_le h4 h
  have hAl : 0 < A * ℓ := by nlinarith [hcpos]
  have hs : 4 / ((39 / 10) * A * ℓ) ≤ s := by
    rw [div_le_iff₀ hcpos]
    have h2 := (div_le_iff₀ hspos).mp h
    linarith [h2]
  have h1 : (4 : ℝ) / ((39 / 10) * A * ℓ) - 1 / (A * ℓ) = (1 / 39) / (A * ℓ) := by
    field_simp
    ring
  have h2 : (1 : ℝ) / (100 * (A * ℓ)) ≤ (1 / 39) / (A * ℓ) := by
    have h100 : (1 : ℝ) / (100 * (A * ℓ)) = (1 / 100) / (A * ℓ) := by
      rw [div_div]
    rw [h100]
    exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hAl)
  have e : (1 : ℝ) / (100 * A * ℓ) = 1 / (100 * (A * ℓ)) := by ring_nf
  rw [e, hx]
  linarith [hs, h1, h2]

/-- For `|t| ≥ x/2`, `1/‖x + 2it‖ ≤ 5/(7x)`. -/
private lemma inv_norm_le {x t : ℝ} (hx : 0 < x) (ht : x / 2 ≤ |t|) :
    1 / ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ ≤ 5 / (7 * x) := by
  have hx2 : x ^ 2 ≤ (2 * t) ^ 2 := by
    have h : x ≤ 2 * |t| := by linarith
    nlinarith [h, abs_nonneg t, sq_abs t, sq_nonneg (x - 1)]
  have hw2 : ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ ^ 2 = x ^ 2 + (2 * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul]
    ring
  have hkey : ((7 / 5) * x) ^ 2 ≤ ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ ^ 2 := by
    rw [hw2]; nlinarith [hx2, hx]
  have hwge : (7 / 5) * x ≤ ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ := by
    calc (7 / 5) * x = Real.sqrt (((7 / 5) * x) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ ^ 2) := Real.sqrt_le_sqrt hkey
      _ = ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖ := Real.sqrt_sq (norm_nonneg _)
  calc 1 / ‖((x : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))‖
      ≤ 1 / ((7 / 5) * x) := one_div_le_one_div_of_le (by positivity) hwge
    _ = 5 / (7 * x) := by field_simp

/-- Uniform zero-free region for Dirichlet L-functions, off the real axis. -/
theorem LFunction_zeroFree_offAxis_uniform :
    ∃ c : ℝ, 0 < c ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ σ t : ℝ, t ≠ 0 →
        1 - c / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨Cζ, hCζpos, hCζ⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨C₂, δ₂, hC₂pos, hδ₂pos, hz₂⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
  obtain ⟨Cu, hCupos, hzu⟩ := zeta_logDeriv_re_uniform
  set A : ℝ := 10^8 * (Cζ + Cu + C₂ + 1) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hA1 : (1:ℝ) ≤ A := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  have hA4 : (4:ℝ) ≤ A := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  have hACζ : 3*Cζ ≤ A/100 := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  have hACu : 5*Cu ≤ A/100 := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  have hAC₂ : C₂ ≤ A/100 := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  have hA48 : (48:ℝ) ≤ A/100 := by rw [hA]; nlinarith [hCζpos, hCupos, hC₂pos]
  refine ⟨1/(1000*A), by positivity, ?_⟩
  intro N hN χ hχprim hχ σ t ht hσ hzero
  haveI : NeZero N := hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hNprod : (2:ℝ) ≤ (N:ℝ) * (|t| + 2) := by
    have h2 : (2:ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    calc (2:ℝ) = 1 * 2 := by norm_num
      _ ≤ (N:ℝ) * (|t| + 2) := mul_le_mul hN1 h2 (by norm_num) (by linarith)
  set L : ℝ := Real.log ((N:ℝ) * (|t| + 2)) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hLhalf : (1/2:ℝ) ≤ L := by
    rw [hL]
    have h1 : Real.log 2 ≤ Real.log ((N:ℝ) * (|t| + 2)) := Real.log_le_log (by norm_num) hNprod
    have h2 : (1/2:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  set ℓ : ℝ := L + 1 with hℓ
  have hℓ1 : (1:ℝ) ≤ ℓ := by rw [hℓ]; linarith
  have hℓpos : 0 < ℓ := by rw [hℓ]; linarith
  have hℓ2 : (3/2:ℝ) ≤ ℓ := by rw [hℓ]; linarith
  set x : ℝ := 1 / (A * ℓ) with hx
  have hxpos : 0 < x := by rw [hx]; exact div_pos one_pos (by positivity)
  have hxinv : 1 / x = A * ℓ := by rw [hx]; field_simp
  set σ' : ℝ := 1 + x with hσ'
  have hσ'1 : 1 < σ' := by rw [hσ']; linarith
  have hσ'2 : σ' ≤ 5/4 := by
    rw [hσ']
    have hx4 : x ≤ 1/4 := by
      rw [hx, div_le_iff₀ (by positivity : 0 < A * ℓ)]
      have h : (4:ℝ) ≤ A * ℓ := by nlinarith [hA4, hℓ1]
      linarith
    linarith
  have hx4 : x ≤ 1/4 := by
    rw [hx, div_le_iff₀ (by positivity : 0 < A * ℓ)]
    have h : (4:ℝ) ≤ A * ℓ := by nlinarith [hA4, hℓ1]
    linarith
  have hσ'1δ : 1 - δ₂ ≤ σ' := by linarith [hδ₂pos, hσ'1]
  have hσ'2b : σ' ≤ 2 := by linarith [hσ'2]
  have hℓeq : Real.log (N:ℝ) + Real.log (2 + |t|) + 1 = ℓ := by
    rw [hℓ, hL, Real.log_mul (by positivity) (by positivity)]
    have h2t : (2:ℝ) + |t| = |t| + 2 := by ring
    rw [h2t]
  have hlogN0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hlogt0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog2t : Real.log (2 + |2*t|) ≤ Real.log (2 + |t|) + 1 := by
    have h2t' : |2*t| = 2*|t| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h4 : 2 + |2*t| ≤ 2*(2 + |t|) := by rw [h2t']; nlinarith [abs_nonneg t]
    have hl := Real.log_le_log (by positivity) h4
    rw [Real.log_mul (by norm_num) (by positivity)] at hl
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hlogt_le_ℓ : Real.log (2 + |t|) + 1 ≤ ℓ := by
    have h2t : (2:ℝ) + |t| = |t| + 2 := by ring
    have hLt : Real.log (2 + |t|) = Real.log (|t| + 2) := by rw [h2t]
    rw [hℓ, hL, hLt, Real.log_mul (by positivity) (by positivity)]
    linarith [hlogN0]
  have hz' : LFunction χ ((σ:ℂ) + Complex.I * (t:ℂ)) = 0 := by
    rw [mul_comm]; exact hzero
  have hσpos : 0 < σ := by
    have hL2 : 1 / L ≤ 2 := by rw [div_le_iff₀ hLpos]; linarith [hLhalf]
    have h3 : (1/(1000*A)) ≤ 1/4000 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 1000*A)]
      nlinarith [hA4]
    have h4 : (1/(1000*A)) * (1/L) ≤ (1/4000)*2 :=
      mul_le_mul h3 hL2 (by positivity) (by norm_num)
    have h5 : (1/(1000*A)) / L = (1/(1000*A)) * (1/L) := by ring
    linarith [hσ, h4, h5]
  have hΛz : completedLFunction χ ((σ:ℂ) + Complex.I * (t:ℂ)) = 0 := by
    rw [Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
      (s := (σ:ℂ) + Complex.I * (t:ℂ)) (by simp; exact hσpos), hz', zero_mul]
  have hstrip := zerosInStrip χ hχ hχprim ((σ:ℂ) + Complex.I * (t:ℂ)) hΛz
  have hσlt1 : σ < 1 := by
    have h1 := hstrip.2
    rwa [show (((σ:ℂ) + Complex.I * (t:ℂ))).re = σ from by simp] at h1
  set s : ℝ := σ' - σ with hs
  have hspos : 0 < s := by rw [hs, hσ']; linarith
  have hsx : x < s := by rw [hs, hσ']; linarith
  have hT1 : (-deriv riemannZeta (σ':ℂ) / riemannZeta (σ':ℂ)).re ≤ 1/x + Cζ := by
    have hb := hCζ σ' hσ'1 hσ'2b
    have hx1 : σ' - 1 = x := by rw [hσ']; ring
    rw [hx1] at hb
    linarith [hb]
  have hkey : 1 / (100 * A * ℓ) ≤ s - x := by
    rcases eq_or_ne (χ * χ) 1 with hsq | hsq
    · have hχinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right hsq
      have hzcL : LFunction χ ((σ:ℂ) - Complex.I * (t:ℂ)) = 0 := by
        have h := LFunction_conj χ hχ ((σ:ℂ) + Complex.I * (t:ℂ))
        have hstar : (starRingEnd ℂ) ((σ:ℂ) + Complex.I * (t:ℂ)) = (σ:ℂ) - Complex.I * (t:ℂ) := by
          simp [map_add, map_mul]; ring
        rw [hz', map_zero, hχinv, hstar] at h
        exact h.symm
      have hzc : completedLFunction χ ((σ:ℂ) - Complex.I * (t:ℂ)) = 0 := by
        rw [Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ
          (s := (σ:ℂ) - Complex.I * (t:ℂ)) (by simp; linarith), hzcL, zero_mul]
      rcases lt_or_ge (1/2:ℝ) |t| with htbig | htsmall
      · -- |t| > 1/2
        have hT2 : (-logDeriv (LFunction χ) ((σ':ℂ) + Complex.I * (t:ℂ))).re ≤ -(1/s) + 8*ℓ := by
          have hb := LFunction_logDeriv_re_two_poles_uniform χ hχ hχprim σ' t σ
            hσ'1 hσ'2 hσpos hσlt1 ht hz' hzc
          rw [← hs, hℓeq] at hb
          rw [neg_div] at hb
          have hnn : (0:ℝ) ≤ s / (s^2 + 4*t^2) :=
            div_nonneg (le_of_lt hspos) (by nlinarith [hspos, sq_nonneg t, sq_nonneg s])
          linarith [hb, hnn]
        have hval1 : ∀ a : ℤ, IsCoprime a (N:ℤ) →
            ((1 : DirichletCharacter ℂ 1) (a : ZMod 1)) = ((χ (a : ZMod N)) : ℂ)^2 := by
          intro a ha
          have h1 : (χ (a : ZMod N))^2 = 1 := by
            have h := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (a : ZMod N)) hsq
            rw [MulChar.mul_apply, MulChar.one_apply (isUnit_zmod_of_isCoprime ha)] at h
            rw [sq]; exact h
          rw [h1]
          show (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
          rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _]
          exact map_one _
        have h341 := three_four_one_nonneg_uniform χ (1 : DirichletCharacter ℂ 1) hval1
          (σ := σ') (τ := t) hσ'1
        have hT3 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ 1))
            ((σ':ℂ) + Complex.I * ((2*t:ℝ):ℂ))).re ≤ 5*Cu*ℓ := by
          rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply]
          have h2t : (1/2:ℝ) ≤ |2*t| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
          have hb := hzu σ' (2*t) hσ'1 hσ'2b h2t
          rw [neg_div] at hb
          have hlog : Real.log (2 + |2*t|) + 1 ≤ 2*ℓ := by
            linarith [hlog2t, hlogt_le_ℓ, hℓ1]
          nlinarith [hb, hlog, hCupos, hℓpos]
        have hcomb : 4*(1/s) ≤ 3*A*ℓ + 3*Cζ + 32*ℓ + 5*Cu*ℓ := by
          linarith [h341, hT1, hT2, hT3, hxinv]
        have h39 : 4*(1/s) ≤ (39/10)*A*ℓ := by
          nlinarith [hcomb, hACζ, hACu, hA48, hℓ1, hApos, hℓpos, hCζpos, hCupos]
        exact arith_final hℓ1 hx hspos h39
      · rcases lt_or_ge |t| (x/2) with hts | htm
        · -- |t| < x/2
          have hT2 : (-logDeriv (LFunction χ) ((σ':ℂ) + Complex.I * (t:ℂ))).re ≤
              -(3/2)*(1/s) + 8*ℓ := by
            have hb := LFunction_logDeriv_re_two_poles_uniform χ hχ hχprim σ' t σ
              hσ'1 hσ'2 hσpos hσlt1 ht hz' hzc
            rw [← hs, hℓeq] at hb
            rw [neg_div] at hb
            have h2tlt : 2*|t| < x := by linarith
            have h4t : (2*t)^2 ≤ s^2 := by
              nlinarith [h2tlt, hsx, abs_nonneg t, sq_abs t]
            have hden : s^2 + 4*t^2 ≤ 2*s^2 := by nlinarith [h4t]
            have hsecond : (1/2)*(1/s) ≤ s/(s^2 + 4*t^2) := by
              have he : 1/(2*s) = s/(2*s^2) := by field_simp
              have h1 : 1/(2*s) ≤ s/(s^2 + 4*t^2) := by
                rw [he]
                exact div_le_div_of_nonneg_left (le_of_lt hspos) (by positivity) hden
              have h2 : 1/(2*s) = (1/2)*(1/s) := by ring
              linarith [h1, h2]
            linarith [hb, hsecond]
          have hval1 : ∀ a : ℤ, IsCoprime a (N:ℤ) →
              ((1 : DirichletCharacter ℂ 1) (a : ZMod 1)) = ((χ (a : ZMod N)) : ℂ)^2 := by
            intro a ha
            have h1 : (χ (a : ZMod N))^2 = 1 := by
              have h := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (a : ZMod N)) hsq
              rw [MulChar.mul_apply, MulChar.one_apply (isUnit_zmod_of_isCoprime ha)] at h
              rw [sq]; exact h
            rw [h1]
            show (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
            rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _]
            exact map_one _
          have h341 := three_four_one_nonneg_uniform χ (1 : DirichletCharacter ℂ 1) hval1
            (σ := σ') (τ := t) hσ'1
          set w : ℂ := (σ':ℂ) + Complex.I * ((2*t:ℝ):ℂ) with hw
          have hT3 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ 1)) w).re ≤ C₂ + 1/x := by
            rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply]
            have h2t : |2*t| ≤ 2 := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
              linarith [hts, hx4]
            have hb := hz₂ (2*t) σ' h2t (by linarith [hσ'1]) hσ'1δ hσ'2b
            have hre : (-(deriv riemannZeta w / riemannZeta w)).re ≤ ‖deriv riemannZeta w / riemannZeta w‖ := by
              have h := Complex.re_le_norm (-(deriv riemannZeta w / riemannZeta w))
              rwa [norm_neg] at h
            have hwge : x ≤ ‖w - 1‖ := by
              have e : w - 1 = (x:ℂ) + Complex.I * ((2*t:ℝ):ℂ) := by
                rw [hw, hσ']; push_cast; ring
              rw [e]
              calc x = ((x:ℂ) + Complex.I * ((2*t:ℝ):ℂ)).re := by simp
                _ ≤ ‖((x:ℂ) + Complex.I * ((2*t:ℝ):ℂ))‖ := Complex.re_le_norm _
            have h1w : 1 / ‖w - 1‖ ≤ 1/x := one_div_le_one_div_of_le hxpos hwge
            have hbeq : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₂ + 1/‖w - 1‖ := hb
            linarith [hre, hbeq, h1w]
          have hcomb : 6*(1/s) ≤ 4*A*ℓ + 3*Cζ + 32*ℓ + C₂ := by
            linarith [h341, hT1, hT2, hT3, hxinv]
          have h39 : 4*(1/s) ≤ (39/10)*A*ℓ := by
            nlinarith [hcomb, hACζ, hAC₂, hA48, hℓ1, hApos, hℓpos, hCζpos]
          exact arith_final hℓ1 hx hspos h39
        · -- x/2 ≤ |t| ≤ 1/2
          have hT2 : (-logDeriv (LFunction χ) ((σ':ℂ) + Complex.I * (t:ℂ))).re ≤ -(1/s) + 8*ℓ := by
            have hb := LFunction_logDeriv_re_pole_uniform_sharp χ hχ hχprim σ' t σ
              hσ'1 hσ'2 hσpos hσlt1 hz'
            rw [← hs, hℓeq] at hb
            rw [neg_div] at hb
            linarith [hb]
          have hval1 : ∀ a : ℤ, IsCoprime a (N:ℤ) →
              ((1 : DirichletCharacter ℂ 1) (a : ZMod 1)) = ((χ (a : ZMod N)) : ℂ)^2 := by
            intro a ha
            have h1 : (χ (a : ZMod N))^2 = 1 := by
              have h := congrArg (fun ψ : DirichletCharacter ℂ N => ψ (a : ZMod N)) hsq
              rw [MulChar.mul_apply, MulChar.one_apply (isUnit_zmod_of_isCoprime ha)] at h
              rw [sq]; exact h
            rw [h1]
            show (1 : DirichletCharacter ℂ 1) (a : ZMod 1) = 1
            rw [show (a : ZMod 1) = 1 from Subsingleton.elim _ _]
            exact map_one _
          have h341 := three_four_one_nonneg_uniform χ (1 : DirichletCharacter ℂ 1) hval1
            (σ := σ') (τ := t) hσ'1
          set w : ℂ := (σ':ℂ) + Complex.I * ((2*t:ℝ):ℂ) with hw
          have hT3 : (-logDeriv (LFunction (1 : DirichletCharacter ℂ 1)) w).re ≤ C₂ + 5/(7*x) := by
            rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply]
            have h2t : |2*t| ≤ 2 := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
              linarith [htsmall]
            have hb := hz₂ (2*t) σ' h2t (by linarith [hσ'1]) hσ'1δ hσ'2b
            have hre : (-(deriv riemannZeta w / riemannZeta w)).re ≤ ‖deriv riemannZeta w / riemannZeta w‖ := by
              have h := Complex.re_le_norm (-(deriv riemannZeta w / riemannZeta w))
              rwa [norm_neg] at h
            have hwge : x ≤ ‖w - 1‖ := by
              have e : w - 1 = (x:ℂ) + Complex.I * ((2*t:ℝ):ℂ) := by
                rw [hw, hσ']; push_cast; ring
              rw [e]
              calc x = ((x:ℂ) + Complex.I * ((2*t:ℝ):ℂ)).re := by simp
                _ ≤ ‖((x:ℂ) + Complex.I * ((2*t:ℝ):ℂ))‖ := Complex.re_le_norm _
            have h1w : 1 / ‖w - 1‖ ≤ 5/(7*x) := by
              have e : w - 1 = ((x:ℂ) + Complex.I * ((2*t:ℝ):ℂ)) := by
                rw [hw, hσ']; push_cast; ring
              rw [e]
              exact inv_norm_le hxpos htm
            have hbeq : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₂ + 1/‖w - 1‖ := hb
            linarith [hre, hbeq, h1w]
          have hcomb : 4*(1/s) ≤ 3*A*ℓ + 3*Cζ + 32*ℓ + C₂ + 5/(7*x) := by
            linarith [h341, hT1, hT2, hT3, hxinv]
          have h5x : 5/(7*x) = (5/7)/x := by rw [div_div]
          have h5xA : 5/(7*x) = (5/7)*(A*ℓ) := by rw [h5x, ← hxinv]; ring
          have h39 : 4*(1/s) ≤ (39/10)*A*ℓ := by
            rw [h5xA] at hcomb
            nlinarith [hcomb, hACζ, hAC₂, hA48, hℓ1, hApos, hℓpos, hCζpos]
          exact arith_final hℓ1 hx hspos h39
    · -- χ * χ ≠ 1
      set χ₂ : DirichletCharacter ℂ N := χ * χ with hχ₂
      have hχ₂ne : χ₂ ≠ 1 := by rw [hχ₂]; exact hsq
      let M : ℕ := χ₂.conductor
      haveI hM : NeZero M := ⟨χ₂.conductor_ne_zero⟩
      set ψ : DirichletCharacter ℂ M := χ₂.primitiveCharacter with hψ
      have hψprim : ψ.IsPrimitive := by rw [hψ]; exact χ₂.primitiveCharacter_isPrimitive
      have hψne : ψ ≠ 1 := by
        intro h1
        have hM1 : M = 1 := by
          have hp : ψ.IsPrimitive := hψprim
          rw [h1] at hp
          have hc := (isPrimitive_def (1 : DirichletCharacter ℂ M)).mp hp
          rw [conductor_one] at hc
          exact hc.symm
        exact hχ₂ne (eq_one_iff_conductor_eq_one.mpr hM1)
      have hval : ∀ a : ℤ, IsCoprime a (N:ℤ) → ψ (a : ZMod M) = ((χ (a : ZMod N)) : ℂ)^2 := by
        intro a ha
        have hcl := DFunLike.congr_fun (changeLevel_primitiveCharacter χ₂) (a : ZMod N)
        have hcast := changeLevel_eq_cast_of_dvd' (χ := χ₂.primitiveCharacter) χ₂.conductor_dvd_level ha
        rw [hcast] at hcl
        rw [hψ, hcl, hχ₂, MulChar.mul_apply]
        ring
      have h341 := three_four_one_nonneg_uniform χ ψ hval (σ := σ') (τ := t) hσ'1
      have hT2 : (-logDeriv (LFunction χ) ((σ':ℂ) + Complex.I * (t:ℂ))).re ≤ -(1/s) + 8*ℓ := by
        have hb := LFunction_logDeriv_re_pole_uniform_sharp χ hχ hχprim σ' t σ
          hσ'1 hσ'2 hσpos hσlt1 hz'
        rw [← hs, hℓeq] at hb
        rw [neg_div] at hb
        linarith [hb]
      have hT3 : (-logDeriv (LFunction ψ) ((σ':ℂ) + Complex.I * ((2*t:ℝ):ℂ))).re ≤ 16*ℓ := by
        have hb := LFunction_logDeriv_re_regular_uniform ψ hψne hψprim σ' (2*t) hσ'1 hσ'2
        have hMle : (M:ℝ) ≤ (N:ℝ) := by
          exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ₂.conductor_dvd_level)
        have hlog : Real.log (M:ℝ) + Real.log (2 + |2*t|) + 1 ≤ 2*ℓ := by
          have h1 : Real.log (M:ℝ) ≤ Real.log (N:ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ₂.conductor_ne_zero)) hMle
          linarith [h1, hlog2t, hlogt_le_ℓ, hℓ1, hℓeq]
        linarith [hb, hlog]
      have hcomb : 4*(1/s) ≤ 3*A*ℓ + 3*Cζ + 48*ℓ := by
        linarith [h341, hT1, hT2, hT3, hxinv]
      have h39 : 4*(1/s) ≤ (39/10)*A*ℓ := by
        nlinarith [hcomb, hACζ, hA48, hℓ1, hApos, hℓpos, hCζpos]
      exact arith_final hℓ1 hx hspos h39
  have h1σ : 1 - σ = s - x := by rw [hs, hσ']; ring
  have hcfin : (1/(1000*A)) / L < 1 - σ := by
    have hlt : (1/(1000*A)) / L < 1/(100*A*ℓ) := by
      have h1 : (1/(1000*A)) / L = 1/(1000*A*L) := by
        rw [div_div]
      have h2 : 1/(1000*A*L) < 1/(100*A*ℓ) := by
        rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 1000*A*L)
          (by positivity : (0:ℝ) < 100*A*ℓ)]
        nlinarith [hLhalf, hApos, hℓpos]
      linarith [h1, h2]
    linarith [hlt, hkey, h1σ]
  have hthis : 1 - σ ≤ (1/(1000*A)) / L := by linarith [hσ]
  linarith [hcfin, hthis]

end
end Commons.NumberTheory.DirichletCharacter
