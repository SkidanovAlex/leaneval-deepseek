import Mathlib
import Submission.Work.OddEnvelope.Defs

namespace Work.OddEnvelope.Shape

open Set

/-- `kSlope h y` is the logarithmic-derivative-type quotient
`σ ↦ (y σ + σ * y' σ + h' σ) / y' σ`.  Its derivative on `(0,∞)` is

`(2 (y' σ)² - y σ (y'' σ) + (h'' σ) (y' σ) - (h' σ) (y'' σ)) / (y' σ)²`,

so the *shape* hypothesis `hshape` (positivity of the numerator) makes the derivative
positive, and `kSlope h y` is strictly increasing on `(0,∞)`. -/
theorem kSlope_strictMonoOn_Cinf {h y : ℝ → ℝ}
    (hy : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) y (Set.Ioi 0)) (hyd : ∀ s, 0 < s → deriv y s < 0)
    (hh : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) h (Set.Ioi 0))
    (hshape : ∀ s, 0 < s →
      0 < 2 * (deriv y s) ^ 2 - y s * deriv (deriv y) s +
        deriv (deriv h) s * deriv y s - deriv h s * deriv (deriv y) s) :
    StrictMonoOn (Work.OddEnvelope.kSlope h y) (Set.Ioi 0) := by
  have hderivy : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (deriv y) (Set.Ioi 0) :=
    hy.deriv_of_isOpen isOpen_Ioi (by simp)
  have hderivh : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (deriv h) (Set.Ioi 0) :=
    hh.deriv_of_isOpen isOpen_Ioi (by simp)
  have hcont : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (Work.OddEnvelope.kSlope h y) (Set.Ioi 0) := by
    rw [show Work.OddEnvelope.kSlope h y
        = fun σ => (y σ + σ * deriv y σ + deriv h σ) / deriv y σ from rfl]
    exact ((hy.add (contDiffOn_id.mul hderivy)).add hderivh).div hderivy
      (fun σ hσ => ne_of_lt (hyd σ hσ))
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont.continuousOn
  intro σ hσ
  rw [interior_Ioi] at hσ
  have hσpos : 0 < σ := hσ
  have hy_d : HasDerivAt y (deriv y σ) σ :=
    (hy.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσpos)
  have hdy_d : HasDerivAt (deriv y) (deriv (deriv y) σ) σ :=
    (hderivy.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσpos)
  have hdh_d : HasDerivAt (deriv h) (deriv (deriv h) σ) σ :=
    (hderivh.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσpos)
  have hnum : HasDerivAt (fun τ => y τ + τ * deriv y τ + deriv h τ)
      (deriv y σ + (deriv y σ + σ * deriv (deriv y) σ) + deriv (deriv h) σ) σ := by
    have key : (fun τ => y τ + τ * deriv y τ + deriv h τ)
        = (y + id * deriv y + deriv h) := by
      funext τ; simp [Pi.add_apply, Pi.mul_apply]
    rw [key]
    exact ((hy_d.add ((hasDerivAt_id σ).mul hdy_d)).add hdh_d).congr_deriv
      (by simp only [id_eq, one_mul])
  have hne : deriv y σ ≠ 0 := ne_of_lt (hyd σ hσpos)
  have hk : HasDerivAt (Work.OddEnvelope.kSlope h y)
      (((deriv y σ + (deriv y σ + σ * deriv (deriv y) σ) + deriv (deriv h) σ) * deriv y σ
        - (y σ + σ * deriv y σ + deriv h σ) * deriv (deriv y) σ) / (deriv y σ) ^ 2) σ := by
    rw [show Work.OddEnvelope.kSlope h y
        = fun τ => (y τ + τ * deriv y τ + deriv h τ) / deriv y τ from rfl]
    exact hnum.div hdy_d hne
  have hderiv_eq : deriv (Work.OddEnvelope.kSlope h y) σ =
      (2 * (deriv y σ) ^ 2 - y σ * deriv (deriv y) σ + deriv (deriv h) σ * deriv y σ
        - deriv h σ * deriv (deriv y) σ) / (deriv y σ) ^ 2 := by
    rw [hk.deriv]
    ring
  rw [hderiv_eq]
  exact div_pos (hshape σ hσpos) (sq_pos_of_ne_zero hne)

end Work.OddEnvelope.Shape
