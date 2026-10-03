import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs

namespace Work.FIArea6Hecke

open scoped BigOperators

noncomputable section

/-- The Gaussian conjugation `γ ↦ γ̄` of `R.gconjInt` is an involution. -/
lemma gconjInt_invol (z : GaussianInt) : Work.FIArea6Hecke.R.gconjInt (Work.FIArea6Hecke.R.gconjInt z) = z := by
  simp [Work.FIArea6Hecke.R.gconjInt]

/-- `R.gconjInt` preserves the norm form `gnorm`. -/
lemma gnorm_gconjInt (z : GaussianInt) :
    Work.FIPlan.gnorm (Work.FIArea6Hecke.R.gconjInt z) = Work.FIPlan.gnorm z := by
  simp [Work.FIPlan.gnorm, Work.FIArea6Hecke.R.gconjInt, Zsqrtd.norm]

/-- `z ↦ z̄` as an equivalence of `ℤ[i]`. -/
def gconjEquiv : GaussianInt ≃ GaussianInt where
  toFun := Work.FIArea6Hecke.R.gconjInt
  invFun := Work.FIArea6Hecke.R.gconjInt
  left_inv := gconjInt_invol
  right_inv := gconjInt_invol

/-- The embedding `ℤ[i] → ℂ` intertwines `R.gconjInt` with complex conjugation. -/
lemma starRingEnd_toComplex (z : GaussianInt) :
    (starRingEnd ℂ) (z : ℂ) = (Work.FIArea6Hecke.R.gconjInt z : ℂ) := by
  simp [Work.FIArea6Hecke.R.gconjInt, GaussianInt.toComplex]

/-- `Complex.exp` is fixed by conjugation at real arguments (here stated for a complex number
fixed by conjugation). -/
lemma star_exp_of_star_eq_self (w : ℂ) (hw : (starRingEnd ℂ) w = w) :
    (starRingEnd ℂ) (Complex.exp w) = Complex.exp w := by
  rw [← Complex.exp_conj w, hw]

/-- **Complex conjugation of the all-`z` theta series.**  Summing the conjugate of the theta
summand and re-indexing by the involution `γ ↦ γ̄` of `ℤ[i]` exchanges `χ₀(z)` for
`χ₀(z̄)`; the weight `(γ : ℂ)^m` becomes `(γ̄ : ℂ)^m` and the Gaussian `e^{-πv|γ|²}` is fixed
because it is real. -/
theorem tsumGconjEqStarAllZTheta (chi₀ : GaussianInt → ℂ) (m : ℕ) (v : ℝ) :
    (∑' γ : GaussianInt, star (chi₀ (Work.FIArea6Hecke.R.gconjInt γ)) * (γ : ℂ) ^ m *
        Complex.exp (-(Real.pi * v * (Work.FIPlan.gnorm γ : ℝ))))
      = star (Work.FIArea6Hecke.R.allZTheta chi₀ m v) := by
  rw [Work.FIArea6Hecke.R.allZTheta, tsum_star]
  trans ∑' z : GaussianInt, star (chi₀ z) * (Work.FIArea6Hecke.R.gconjInt z : ℂ) ^ m *
      Complex.exp (-(Real.pi * v * (Work.FIPlan.gnorm z : ℝ)))
  · rw [← Equiv.tsum_eq gconjEquiv
      (fun γ : GaussianInt => star (chi₀ (Work.FIArea6Hecke.R.gconjInt γ)) * (γ : ℂ) ^ m *
        Complex.exp (-(Real.pi * v * (Work.FIPlan.gnorm γ : ℝ))))]
    apply tsum_congr
    intro c
    simp only [gconjEquiv, Equiv.coe_fn_mk, gconjInt_invol, gnorm_gconjInt]
  · apply tsum_congr
    intro z
    simp only [RCLike.star_def]
    rw [map_mul, map_mul, map_pow, starRingEnd_toComplex]
    have hw : (starRingEnd ℂ) (-(Real.pi * v * (Work.FIPlan.gnorm z : ℝ))) =
        -(Real.pi * v * (Work.FIPlan.gnorm z : ℝ)) := by simp
    rw [star_exp_of_star_eq_self _ hw, mul_assoc]

end

end Work.FIArea6Hecke
