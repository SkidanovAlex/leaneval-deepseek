import Mathlib
import Submission.Work.Pert.EuDefs

/-!
# PERT · `Work.Pert.EuDecomp`

The elementary decomposition of the deviation `E_u = τ₀ ∘ τ_f - id` of the composite chart
`τ₀ ∘ τ_f` around the two centres `±iη` (Shishikura (4.2.x), used in `Work.Pert.PertCoordClose`).

Writing `s = euS α = 2πiα` and `t = euT α η = 2παη` and using `τ₀ w = -1/w`,
`τ_f z = σ/(1 - e^{-sz})`, the deviation has the closed form

  `Eu σ α ζ = (e^{-sζ} - 1 - σζ)/σ`.

The normalisation `1 - σu₀ = e^s` of the statement gives `1 - e^s = σu₀` and
`euPsi α = (e^s - 1)/s = -σu₀/s`.  All four identities below are then pure algebra in the
multiplicative cocycle `e^{-s(ζ-w)} = e^{-sζ}·e^{sw}` together with the two evaluations
`e^{s(iη)} = e^{-t}`, `e^{s(-iη)} = e^{t}` of the centres.
-/

namespace Work.Pert

open Complex

noncomputable section

/-- The closed form of the deviation: `Eu σ α ζ = (e^{-sζ} - 1 - σζ)/σ`, `s = euS α`. -/
private lemma eu_closed {σ α : ℂ} (hσ : σ ≠ 0) (ζ : ℂ) :
    Eu σ α ζ = (Complex.exp (-(euS α * ζ)) - 1 - σ * ζ) / σ := by
  have harg : -(2 * Real.pi * Complex.I * α * ζ) = -(euS α * ζ) := by rw [euS]
  simp only [Eu, MandelDim.tau0, tauC, harg]
  field_simp
  ring

/-- Algebraic core of the first two identities: with `ψ = -σu₀/s` and `es = 1 - σu₀` (so that
`1 - es = σu₀`), the difference of the two closed forms is exactly the stated expression. -/
private lemma eu_first_alg {σ u₀ s ψ A B x w es : ℂ} (hσ : σ ≠ 0) (hu₀ : u₀ ≠ 0)
    (hψ : ψ = -σ * u₀ / s) (hes : es = 1 - σ * u₀) :
    (A * B - 1 - σ * (x + w)) / σ - (B - 1 - σ * w) / σ
      = x * (u₀ * B / ψ - 1) + u₀ * B * (A - 1 + s * x) / (1 - es) := by
  subst hψ; subst hes
  field_simp
  ring

/-- Algebraic core of the third identity (`Eu(iη) - Eu(-iη)`), with `sinh t` split as
`(e^t - e^{-t})/2` and the relation `c·s = -t` (`c = iη`). -/
private lemma eu_third_alg {σ u₀ s ψ t c : ℂ} (hσ : σ ≠ 0) (hu₀ : u₀ ≠ 0)
    (hψ : ψ = -σ * u₀ / s) (hcs : c * s = -t) :
    (Complex.exp t - 1 - σ * c) / σ - (Complex.exp (-t) - 1 - σ * (-c)) / σ
      = 2 * c * (u₀ * ((Complex.exp t - Complex.exp (-t)) / 2) / (t * ψ) - 1) := by
  subst hψ
  by_cases ht : t = 0
  · rw [ht]; field_simp; ring_nf
  · field_simp
    linear_combination (Complex.exp t - Complex.exp (-t)) * hcs

/-- Algebraic core of the fourth identity (`Eu(iη) + Eu(-iη)`). -/
private lemma eu_fourth_alg {σ t c : ℂ} (hσ : σ ≠ 0) :
    (Complex.exp t - 1 - σ * c) / σ + (Complex.exp (-t) - 1 - σ * (-c)) / σ
      = 2 * (Complex.cosh t - 1) / σ := by
  rw [show 2 * (Complex.cosh t - 1) = Complex.exp t + Complex.exp (-t) - 2 from by
    rw [mul_sub, Complex.two_cosh]; ring]
  field_simp
  ring

theorem EuDecomp {σ α u₀ : ℂ} {η : ℝ}
    (hσ : σ ≠ 0) (hα : α ≠ 0) (hu₀ : u₀ ≠ 0)
    (heq : 1 - σ * u₀ = Complex.exp (euS α)) :
    (∀ ζ : ℂ, Eu σ α ζ - Eu σ α (Complex.I * (η : ℂ))
        = (ζ - Complex.I * (η : ℂ)) * (u₀ * Complex.exp (euT α η) / euPsi α - 1)
          + u₀ * Complex.exp (euT α η)
            * (Complex.exp (-(euS α * (ζ - Complex.I * (η : ℂ)))) - 1
                + euS α * (ζ - Complex.I * (η : ℂ)))
            / (1 - Complex.exp (euS α)))
    ∧ (∀ ζ : ℂ, Eu σ α ζ - Eu σ α (-(Complex.I * (η : ℂ)))
        = (ζ + Complex.I * (η : ℂ)) * (u₀ * Complex.exp (-(euT α η)) / euPsi α - 1)
          + u₀ * Complex.exp (-(euT α η))
            * (Complex.exp (-(euS α * (ζ + Complex.I * (η : ℂ)))) - 1
                + euS α * (ζ + Complex.I * (η : ℂ)))
            / (1 - Complex.exp (euS α)))
    ∧ Eu σ α (Complex.I * (η : ℂ)) - Eu σ α (-(Complex.I * (η : ℂ)))
        = 2 * Complex.I * (η : ℂ)
          * (u₀ * Complex.sinh (euT α η) / (euT α η * euPsi α) - 1)
    ∧ Eu σ α (Complex.I * (η : ℂ)) + Eu σ α (-(Complex.I * (η : ℂ)))
        = 2 * (Complex.cosh (euT α η) - 1) / σ := by
  have hEu : ∀ z : ℂ, Eu σ α z = (Complex.exp (-(euS α * z)) - 1 - σ * z) / σ :=
    fun z => eu_closed hσ z
  have hpsi : euPsi α = -σ * u₀ / euS α := by
    have h : Complex.exp (euS α) = 1 - σ * u₀ := heq.symm
    rw [euPsi, h]; ring
  have h1es : Complex.exp (euS α) = 1 - σ * u₀ := heq.symm
  have hsc : euS α * (Complex.I * (η : ℂ)) = -(euT α η) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [euS, euT]; linear_combination (2 * (Real.pi : ℂ) * α * (η : ℂ)) * hI
  have hsinh : Complex.sinh (euT α η)
      = (Complex.exp (euT α η) - Complex.exp (-(euT α η))) / 2 := by
    rw [← Complex.two_sinh]; ring
  have e1 : -(euS α * (Complex.I * (η : ℂ))) = euT α η := by rw [hsc, neg_neg]
  have e2 : -(euS α * (-(Complex.I * (η : ℂ)))) = -(euT α η) := by
    simp only [mul_neg, neg_neg, hsc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ζ
    set w : ℂ := Complex.I * (η : ℂ) with hw
    set x : ℂ := ζ - w with hx
    have hζ : ζ = x + w := by rw [hx]; ring
    have hsw : -(euS α * w) = euT α η := by rw [hsc, neg_neg]
    have heexp : Complex.exp (-(euS α * ζ))
        = Complex.exp (-(euS α * x)) * Complex.exp (euT α η) := by
      have harg : -(euS α * ζ) = -(euS α * x) + euT α η := by
        rw [hζ, mul_add, neg_add, hsw]
      rw [harg, Complex.exp_add]
    rw [hEu ζ, hEu w, heexp, hsw, hζ]
    exact eu_first_alg hσ hu₀ hpsi h1es
  · intro ζ
    set w : ℂ := -(Complex.I * (η : ℂ)) with hw
    set x : ℂ := ζ + Complex.I * (η : ℂ) with hx
    have hζ : ζ = x + w := by rw [hx, hw]; ring
    have hsw : -(euS α * w) = -(euT α η) := by
      simp only [hw, mul_neg, neg_neg, hsc]
    have heexp : Complex.exp (-(euS α * ζ))
        = Complex.exp (-(euS α * x)) * Complex.exp (-(euT α η)) := by
      have harg : -(euS α * ζ) = -(euS α * x) + -(euT α η) := by
        rw [hζ, mul_add, neg_add, hsw]
      rw [harg, Complex.exp_add]
    rw [hEu ζ, hEu w, heexp, hsw, hζ]
    exact eu_first_alg hσ hu₀ hpsi h1es
  · rw [hEu (Complex.I * (η : ℂ)), hEu (-(Complex.I * (η : ℂ))), e1, e2, hsinh]
    rw [show (2 : ℂ) * Complex.I * (η : ℂ) = 2 * (Complex.I * (η : ℂ)) from by ring]
    exact eu_third_alg hσ hu₀ hpsi (by rw [mul_comm, hsc])
  · rw [hEu (Complex.I * (η : ℂ)), hEu (-(Complex.I * (η : ℂ))), e1, e2]
    exact eu_fourth_alg hσ

end

end Work.Pert
