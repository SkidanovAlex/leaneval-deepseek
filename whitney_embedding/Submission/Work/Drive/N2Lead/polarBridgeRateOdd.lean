import Mathlib
import Submission.Work.Drive.N2Lead.polarBridgeRate
import Submission.Work.Drive.N2Lead.mobiusGeomDefs

namespace Work.Drive.N2Lead

/-- `deriv` of a pointwise negation (local copy, so that this module does not depend on the
saddle-certificate file). -/
private lemma polar_deriv_neg_fun (g : ℝ → ℂ) (w : ℝ) : deriv (fun u => -g u) w = -deriv g w := by
  by_cases hd : DifferentiableAt ℝ g w
  · exact (hd.hasDerivAt.neg).deriv
  · have h1 : ¬ DifferentiableAt ℝ (fun u : ℝ => -g u) w := by
      intro hcon
      refine hd ?_
      have := hcon.neg
      simpa using this
    rw [deriv_zero_of_not_differentiableAt h1, deriv_zero_of_not_differentiableAt hd, neg_zero]

theorem polarBridgeRateOdd {η m : ℝ} (hη : 0 < η) (hm : 1 < m)
    {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m),
      Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hmono : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0)
    {φ : ℝ} (hφ : |φ| ≤ Work.Drive.N2Lead.mobiusPhiE η m) :
    0 < (star ((r (φ + Real.pi) : ℂ) * Complex.exp (((φ + Real.pi : ℝ) : ℂ) * Complex.I) + 1)
        * deriv (fun ψ : ℝ => (r ψ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) (φ + Real.pi)).im := by
  set G : ℝ → ℂ := fun x => (r x : ℂ) * Complex.exp ((x : ℂ) * Complex.I) with hG
  -- `π`-antiperiodicity of the polar curve (from `π`-periodicity of the profile)
  have hA : ∀ x : ℝ, G (x + Real.pi) = -G x := by
    intro x
    show (r (x + Real.pi) : ℂ) * Complex.exp (((x + Real.pi : ℝ) : ℂ) * Complex.I)
      = -((r x : ℂ) * Complex.exp ((x : ℂ) * Complex.I))
    have h1 : r (x + Real.pi) = r x := hrpi x
    have h2 : (((x + Real.pi : ℝ)) : ℂ) * Complex.I
        = ((x : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hder : deriv G (φ + Real.pi) = -deriv G φ := by
    have heq : G = fun x : ℝ => -G (x + Real.pi) := by
      funext x
      rw [hA x, neg_neg]
    have step : deriv G φ = deriv (fun x : ℝ => -G (x + Real.pi)) φ :=
      congrArg (fun F : ℝ → ℂ => deriv F φ) heq
    rw [polar_deriv_neg_fun, deriv_comp_add_const] at step
    rw [step]
    ring
  show 0 < (star (G (φ + Real.pi) + 1) * deriv G (φ + Real.pi)).im
  rw [hder, hA φ]
  have hstar : star (-G φ + 1) = -star (G φ - 1) := by
    rw [show -G φ + 1 = -(G φ - 1) by ring, star_neg]
  rw [hstar, neg_mul_neg]
  have h := Work.Drive.N2Lead.polarBridgeRate (η := η) (m := m) hη hm hr hrpos hrev hlo hmono hφ
  simpa [hG] using h

end Work.Drive.N2Lead
