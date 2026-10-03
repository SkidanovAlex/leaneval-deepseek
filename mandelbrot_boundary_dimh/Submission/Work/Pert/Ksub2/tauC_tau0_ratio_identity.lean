import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert.Ksub2

/-- Pure field identity: for `a, y, u ≠ 0` and `F ≠ 1`,
`((1-E)/u)/(1-F) - y = y*((E-1)/a/(u*((F-1)/(a/y))) - 1)`. -/
private lemma div_identity (a y u E F : ℂ)
    (ha : a ≠ 0) (hy : y ≠ 0) (hu : u ≠ 0) (hF : F ≠ 1) :
    ((1 - E) / u) / (1 - F) - y
      = y * ((E - 1) / a / (u * ((F - 1) / (a / y))) - 1) := by
  have h1F : (1 - F) ≠ 0 := sub_ne_zero.mpr hF.symm
  have hF1 : (F - 1) ≠ 0 := sub_ne_zero.mpr hF
  have hay : a / y ≠ 0 := div_ne_zero ha hy
  field_simp
  ring

theorem tauC_tau0_ratio_identity {u0 σ α y : ℂ}
    (hσ : σ = (1 - Complex.exp (2 * Real.pi * Complex.I * α)) / u0)
    (hα : α ≠ 0) (hy : y ≠ 0) (hu0 : u0 ≠ 0)
    (he : Complex.exp (2 * Real.pi * Complex.I * α / y) ≠ 1) :
    σ / (1 - Complex.exp (2 * Real.pi * Complex.I * α / y)) - y
      = y * ((Complex.exp (2 * Real.pi * Complex.I * α) - 1) / (2 * Real.pi * Complex.I * α)
          / (u0 * ((Complex.exp (2 * Real.pi * Complex.I * α / y) - 1)
              / (2 * Real.pi * Complex.I * α / y))) - 1) := by
  rw [hσ]
  have ha : (2 * Real.pi * Complex.I * α : ℂ) ≠ 0 := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    exact mul_ne_zero h2 hα
  exact div_identity (2 * Real.pi * Complex.I * α) y u0
    (Complex.exp (2 * Real.pi * Complex.I * α))
    (Complex.exp (2 * Real.pi * Complex.I * α / y)) ha hy hu0 he

end Work.Pert.Ksub2
