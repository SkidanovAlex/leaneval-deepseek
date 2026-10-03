import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped BigOperators

noncomputable section

private lemma re_finsum_of_finiteSupport' (g : ℂ → ℂ) (hfs : Function.HasFiniteSupport g) :
    (∑ᶠ u, g u).re = ∑ᶠ u, (g u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

/-- Real part of `1/(z - u)` in coordinates (the rebasing kernel). -/
private lemma re_inv_sub_coord' (z u : ℂ) :
    (1 / (z - u)).re
      = (z.re - u.re) / ((z.re - u.re) ^ 2 + (z.im - u.im) ^ 2) := by
  have h : z - u = ((z.re - u.re : ℝ) : ℂ) + ((z.im - u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  rw [h, one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    sub_zero, mul_one, zero_mul, add_zero]
  ring

/-- **Pointwise nonnegativity of the rebasing kernel (base point `-2`).** -/
theorem re_rebase_nonneg_negTwo {σ γ : ℝ} (hσ : 1 < σ) {u : ℂ} (hu1 : -1 ≤ u.re)
    (hu2 : u.re ≤ σ) :
    0 ≤ (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
        - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u)).re := by
  have hz : (((σ : ℂ) + (γ : ℂ) * Complex.I)).re = σ := by simp
  have hzi : (((σ : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
  have hz1 : (((-2 : ℂ) + (γ : ℂ) * Complex.I)).re = -2 := by simp
  have hz1i : (((-2 : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
  rw [Complex.sub_re, re_inv_sub_coord', re_inv_sub_coord', hz, hzi, hz1, hz1i]
  have hA : 0 ≤ (σ - u.re) / ((σ - u.re) ^ 2 + (γ - u.im) ^ 2) :=
    div_nonneg (by linarith) (by positivity)
  have hB : (-2 - u.re) / ((-2 - u.re) ^ 2 + (γ - u.im) ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **The rebasing kernel at the zero itself (base point `-2`).** -/
theorem re_rebase_at_zero_negTwo {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))
        - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re
      = 1 / (σ - β) + 1 / (2 + β) := by
  have hsp : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = ((σ - β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hs₁p : ((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (((-2 - β : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hsp, hs₁p, Complex.sub_re,
    show (1 / (((σ - β : ℝ)) : ℂ)).re = 1 / (σ - β) from by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re],
    show (1 / (((-2 - β : ℝ)) : ℂ)).re = 1 / (-2 - β) from by
      rw [one_div, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]]
  have key : (1 : ℝ) / (σ - β) - 1 / (-2 - β) = 1 / (σ - β) + 1 / (2 + β) := by
    rw [show (-2 - β : ℝ) = -(2 + β) by ring, one_div, one_div, one_div, inv_neg]
    ring
  exact key

/-- The same, in the form used downstream: the kernel is at least `1/(σ-β)`. -/
theorem le_re_rebase_at_zero_negTwo {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    1 / (σ - β) ≤
      (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))
        - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re := by
  rw [re_rebase_at_zero_negTwo hσ hβ0 hβ1]
  have h : 0 ≤ 1 / (2 + β) := by positivity
  linarith

/-- **Rebasing with base point `-2`.** -/
theorem re_logDeriv_rebase_negTwo (Lam : ℂ → ℂ) (hDiff : Differentiable ℂ Lam)
    (hpf : ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((Work.FIArea6Hecke.R.divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
        (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hzeros : ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    {σ β γ : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hρ : Lam ((β : ℂ) + (γ : ℂ) * Complex.I) = 0)
    (hs : Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0)
    (hs₁ : Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re
        + 1 / (σ - β)
      ≤ (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  have hAn : ∀ r : ℝ, AnalyticOnNhd ℂ Lam (Metric.closedBall 0 r) := fun r =>
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff _
  have hupper : ∀ u : ℂ, Lam u = 0 → u.re ≤ σ := fun u hu => by
    have := (hzeros u hu).2
    linarith
  have hlower : ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re := fun u hu => (hzeros u hu).1
  -- pointwise nonnegativity of every kernel
  have hpoint : ∀ (R : ℝ) (u : ℂ),
      0 ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))).re := by
    intro R u
    by_cases hD : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u = 0
    · rw [hD]; simp
    · have hzero : Lam u = 0 :=
        Commons.Analysis.Complex.zero_of_divisor_ne_zero (hAn R) hD
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)).im
          = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      exact mul_nonneg (Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) u)
        (re_rebase_nonneg_negTwo (σ := σ) (γ := γ) (u := u) hσ (hlower u hzero) (hupper u hzero))
  -- the finitely-supported sum is at least the contribution of the zero `ρ = β + iγ`
  have hbig : ∀ᶠ R : ℝ in Filter.atTop,
      1 / (σ - β) ≤ (∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
              - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u)))).re := by
    rw [Filter.eventually_atTop]
    refine ⟨max ‖(β : ℂ) + (γ : ℂ) * Complex.I‖ 0, fun R hR => ?_⟩
    have hρball : ((β : ℂ) + (γ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (le_max_left _ _) hR
    have hLamne : Lam ≠ 0 := fun hcon => hs (by rw [hcon]; rfl)
    have hDρ : (MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
        ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
      Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hDiff hLamne hρball hρ
    have hmρ : (1 : ℝ) ≤ (((MeromorphicOn.divisor Lam
        (Metric.closedBall 0 R)) ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℝ) := by
      have hnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor Lam
          (Metric.closedBall 0 R)) ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℝ) :=
        Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAn R) _
      have hne : (((MeromorphicOn.divisor Lam
          (Metric.closedBall 0 R)) ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℝ) ≠ 0 := by
        intro h0
        exact hDρ (by exact_mod_cast h0)
      have h1 : (0 : ℝ) < (((MeromorphicOn.divisor Lam
          (Metric.closedBall 0 R)) ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℝ) :=
        lt_of_le_of_ne hnn (Ne.symm hne)
      have h2 : (1 : ℤ) ≤ (MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
          ((β : ℂ) + (γ : ℂ) * Complex.I) := by exact_mod_cast h1
      exact_mod_cast h2
    have hρterm : 1 / (σ - β) ≤ ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
        ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)))).re := by
      rw [Complex.mul_re]
      have hDre : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
          ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℂ)).re
          = (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
              ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℝ) := by simp
      have hDim : ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R))
          ((β : ℂ) + (γ : ℂ) * Complex.I) : ℤ) : ℂ)).im = 0 := by simp
      rw [hDre, hDim, zero_mul, sub_zero]
      calc 1 / (σ - β) ≤ 1 * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))
              - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re := by
              rw [one_mul]
              exact le_re_rebase_at_zero_negTwo (σ := σ) (β := β) (γ := γ) hσ hβ0 hβ1
        _ ≤ _ := mul_le_mul_of_nonneg_right hmρ
              (re_rebase_nonneg_negTwo (σ := σ) (γ := γ) (u := (β : ℂ) + (γ : ℂ) * Complex.I) hσ
                (hlower _ hρ) (hupper _ hρ))
    have hfs : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
              - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))) :=
      ((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset
        (fun u hu => by rw [Function.mem_support] at hu ⊢; intro hd; exact hu (by simp [hd]))
    have hfs' : Function.HasFiniteSupport (fun u : ℂ =>
        ((((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
              - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))).re) :=
      hfs.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢; intro h0; exact hu (by rw [h0]; simp))
    have hle := single_le_finsum ((β : ℂ) + (γ : ℂ) * Complex.I) hfs' (fun j => hpoint R j)
    rw [re_finsum_of_finiteSupport' _ hfs]
    exact le_trans hρterm hle
  have hlim : Filter.Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (((σ : ℂ) + (γ : ℂ) * Complex.I) - u)
            - 1 / (((-2 : ℂ) + (γ : ℂ) * Complex.I) - u))).re) Filter.atTop
      (nhds ((deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (hpf ((σ : ℂ) + (γ : ℂ) * Complex.I) ((-2 : ℂ) + (γ : ℂ) * Complex.I) hs hs₁)
  have hge : 1 / (σ - β) ≤
      (deriv Lam ((σ : ℂ) + (γ : ℂ) * Complex.I) / Lam ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re :=
    ge_of_tendsto hlim hbig
  rw [Complex.sub_re] at hge
  linarith
end

end Work.FIArea6Hecke.R
