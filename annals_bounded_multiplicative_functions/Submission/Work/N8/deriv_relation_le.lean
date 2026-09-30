import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial

theorem deriv_relation_le {p γ₁ γ₂ : Polynomial ℝ} {c₁ c₂ A t : ℝ} (ht : 0 < t)
    (h₁ : |deriv (fun s ↦ p.eval s - c₁ * Real.log s - γ₁.eval s) t| ≤ A)
    (h₂ : |deriv (fun s ↦ p.eval s - c₂ * Real.log s - γ₂.eval s) t| ≤ A) :
    |(γ₁ - γ₂).derivative.eval t + (c₁ - c₂) / t| ≤ 2 * A := by
  have hd₁ : deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t
      = p.derivative.eval t - c₁ / t - γ₁.derivative.eval t := by
    have hlog : DifferentiableAt ℝ (fun s => c₁ * Real.log s) t :=
      (Real.differentiableAt_log (ne_of_gt ht)).const_mul c₁
    have hdiff : DifferentiableAt ℝ (fun s => p.eval s - c₁ * Real.log s) t :=
      (p.differentiableAt).sub hlog
    rw [show (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s)
          = (fun s => p.eval s - c₁ * Real.log s) - (fun s => γ₁.eval s) from rfl]
    rw [deriv_sub hdiff γ₁.differentiableAt]
    rw [show (fun s => p.eval s - c₁ * Real.log s)
          = (fun s => p.eval s) - (fun s => c₁ * Real.log s) from rfl]
    rw [deriv_sub p.differentiableAt hlog]
    rw [deriv_const_mul c₁ (Real.differentiableAt_log (ne_of_gt ht))]
    rw [Polynomial.deriv p, Polynomial.deriv γ₁, Real.deriv_log]
    ring
  have hd₂ : deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t
      = p.derivative.eval t - c₂ / t - γ₂.derivative.eval t := by
    have hlog : DifferentiableAt ℝ (fun s => c₂ * Real.log s) t :=
      (Real.differentiableAt_log (ne_of_gt ht)).const_mul c₂
    have hdiff : DifferentiableAt ℝ (fun s => p.eval s - c₂ * Real.log s) t :=
      (p.differentiableAt).sub hlog
    rw [show (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s)
          = (fun s => p.eval s - c₂ * Real.log s) - (fun s => γ₂.eval s) from rfl]
    rw [deriv_sub hdiff γ₂.differentiableAt]
    rw [show (fun s => p.eval s - c₂ * Real.log s)
          = (fun s => p.eval s) - (fun s => c₂ * Real.log s) from rfl]
    rw [deriv_sub p.differentiableAt hlog]
    rw [deriv_const_mul c₂ (Real.differentiableAt_log (ne_of_gt ht))]
    rw [Polynomial.deriv p, Polynomial.deriv γ₂, Real.deriv_log]
    ring
  have key : deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t
             - deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t
           = -((γ₁ - γ₂).derivative.eval t + (c₁ - c₂) / t) := by
    rw [hd₁, hd₂]
    simp only [Polynomial.derivative_sub, Polynomial.eval_sub]
    ring
  have htri : |deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t
             - deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t|
            ≤ |deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t|
            + |deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t| := by
    have := abs_add_le (deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t)
        (-(deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t))
    simpa [sub_eq_add_neg, abs_neg] using this
  have hfin : |deriv (fun s => p.eval s - c₁ * Real.log s - γ₁.eval s) t
             - deriv (fun s => p.eval s - c₂ * Real.log s - γ₂.eval s) t| ≤ 2 * A := by
    refine le_trans htri ?_
    linarith
  rw [key] at hfin
  simp only [abs_neg] at hfin
  exact hfin

end Work.N8
