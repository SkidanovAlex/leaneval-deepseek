import Mathlib
import Submission.Work.LinnikAreas.RealZeroCount.Defs
import Submission.Work.LinnikAreas.siegelZeroSimple_ldUpper
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas

/-- The primitive character inducing a non-principal character is non-principal. -/
theorem primitiveCharacter_ne_one_of_ne_one' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  exact hχ (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1,
    DirichletCharacter.changeLevel_one χ.conductor_dvd_level])

/-- **Hadamard partial fraction at `T = 0`, radius `1`.**  If `Re (Λ′/Λ)(σ₁) ≤ B₁` for some real
`σ₁ ≥ 1`, then the divisor-weighted Hadamard kernel of `χ` over the unit ball is at most
`B₁ + log N + ½ log 2 + 3/2`, where `N = χ.conductor`.

This is `Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le` with `T = 0`,
`R = 1`, and the kernel `realKernel` of `RealZeroCount/Defs.lean`. -/
theorem divisorKernelFinsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor] {σ₁ B₁ : ℝ} (hσ₁ : 1 ≤ σ₁)
    (hB : (logDeriv (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (σ₁ : ℂ)).re ≤ B₁) :
    divisorKernelFinsum q χ σ₁
      ≤ B₁ + Real.log ((χ.conductor : ℕ) : ℝ) + Real.log 2 / 2 + 3 / 2 := by
  classical
  have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one_of_ne_one' χ hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hB' : (logDeriv (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      ((σ₁ : ℂ) + Complex.I * ((0 : ℝ) : ℂ))).re ≤ B₁ := by simpa using hB
  have h := Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
    χ.primitiveCharacter hψ hψprim 0 σ₁ B₁ hσ₁ hB' 1
  have hrewrite : divisorKernelFinsum q χ σ₁
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor
            (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) *
          ((σ₁ - u.re) / ((σ₁ - u.re) ^ 2 + (0 - u.im) ^ 2)
            + (1 + u.re) / ((1 + u.re) ^ 2 + (0 - u.im) ^ 2)) := by
    rw [divisorKernelFinsum]
    refine finsum_congr (fun u => ?_)
    simp only [realKernel]
    ring_nf
  rw [hrewrite]
  refine le_trans h ?_
  rw [abs_zero, add_zero]
  linarith

end Work.LinnikAreas
