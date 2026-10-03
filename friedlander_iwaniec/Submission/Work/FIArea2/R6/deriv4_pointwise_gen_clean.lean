import Mathlib
import Submission.Work.FIArea2.R6.GenRegion
import Submission.Work.FIArea2.R6.deriv4_pointwise_gen

namespace Work.FIArea2.R6

/-- `deriv` commutes with viewing a real function as a complex-valued function. -/
lemma deriv_ofReal_comp (g : ℝ → ℝ) (x : ℝ) :
    deriv (fun y : ℝ => ((g y : ℝ) : ℂ)) x = ((deriv g x : ℝ) : ℂ) := by
  by_cases hg : DifferentiableAt ℝ g x
  · exact (hg.hasDerivAt.ofReal_comp).deriv
  · have hg' : ¬ DifferentiableAt ℝ (fun y : ℝ => ((g y : ℝ) : ℂ)) x := by
      intro h
      have := Complex.reCLM.differentiableAt.comp x h
      exact hg (by simpa [Function.comp_def] using this)
    rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hg']
    simp

/-- Iterated derivatives commute with the embedding `ℝ → ℂ`. -/
lemma iteratedDeriv_ofReal_comp (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => ((f y : ℝ) : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun y : ℝ => ((f y : ℝ) : ℂ))
        = fun y => ((iteratedDeriv n f y : ℝ) : ℂ) := by
      funext y; exact ih y
    rw [hfun]
    exact deriv_ofReal_comp _ _

theorem deriv4_pointwise_gen_clean (M γ A B Cder : ℝ) (F : ℝ → ℝ)
    (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : B ≤ 64 * M) (hCder : 1 ≤ Cder)
    (hF : ContDiff ℝ 4 F)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * M ^ (-(j : ℝ)))
    (t₁ t₂ : ℝ) :
    ‖iteratedDeriv 4 (fun s : ℝ => (F (Work.FIArea2.gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹
        * Set.indicator (Work.FIArea2.R6.regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂) :=
  deriv4_pointwise_gen M γ A B Cder F hM hγ0 hγ1 hB hCder hF hfsupp hfd t₁ t₂

end Work.FIArea2.R6
