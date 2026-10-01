import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmTermDefs
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp

namespace Work.LinnikAreas.Density4

/-- Inverse Mellin transform of the `n`-th summand: for `X > 0` and every `n`,
`(1/(2π)) ∫_ℝ SsmTerm n t dt = Ψ(n)Θ(n)χ(n) · n^{-ρ} · e^{-n/X}`.

Indeed `SsmTerm n t = Ψ(n)Θ(n)χ(n)·n^{-ρ}·(n/X)^{-(1+it)}Γ(1+it)`, so the constant
`Ψ(n)Θ(n)χ(n)·n^{-ρ}` factors out of the integral, and the remaining integral is the inverse
Mellin transform of `Γ` at the parameter `c = 1` and `y = n/X` (`mellin_kernel_exp`),
which equals `e^{-n/X}`. -/
theorem SsmTerm_integral (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (n : ℕ) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t
      = Work.LinnikAreas.Density4.mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ)
          * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: the summand vanishes because `Ψ(0) = 0`.
    subst hn
    simp only [Work.LinnikAreas.Density4.SsmTerm_zero, Work.LinnikAreas.Density4.mollCoeff_zero]
    simp
  -- `n ≥ 1`: factor the constant `Ψ(n)Θ(n)χ(n)·n^{-ρ}` out of the integral.
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hy : 0 < (n : ℝ) / X := div_pos hnpos hX
  set C : ℂ := Work.LinnikAreas.Density4.mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) with hC
  have hfun : (fun t : ℝ => Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t)
      = fun t : ℝ => C * (((((n : ℝ) / X : ℝ)) : ℂ) ^ (-((1 : ℝ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℝ) + (t : ℂ) * Complex.I)) := by
    funext t
    simp only [Work.LinnikAreas.Density4.SsmTerm, hC, Complex.ofReal_one]
  have h1 : ∫ t : ℝ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t
      = C * ∫ t : ℝ, (((((n : ℝ) / X : ℝ)) : ℂ) ^ (-((1 : ℝ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℝ) + (t : ℂ) * Complex.I)) := by
    rw [hfun, MeasureTheory.integral_const_mul]
  -- Inverse Mellin transform of `Γ` on the line `Re s = 1`, at `y = n/X > 0`.
  have h2 : (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (((((n : ℝ) / X : ℝ)) : ℂ) ^ (-((1 : ℝ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℝ) + (t : ℂ) * Complex.I))
      = ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ) := by
    simpa using Work.LinnikAreas.Density4.mellin_kernel_exp 1 one_pos ((n : ℝ) / X) hy
  calc (1 / (2 * Real.pi)) * ∫ t : ℝ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t
      = (1 / (2 * Real.pi)) * (C * ∫ t : ℝ,
          (((((n : ℝ) / X : ℝ)) : ℂ) ^ (-((1 : ℝ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℝ) + (t : ℂ) * Complex.I))) := by rw [h1]
    _ = C * ((1 / (2 * Real.pi)) * ∫ t : ℝ,
          (((((n : ℝ) / X : ℝ)) : ℂ) ^ (-((1 : ℝ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℝ) + (t : ℂ) * Complex.I))) := by ring
    _ = C * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ) := by rw [h2]
    _ = Work.LinnikAreas.Density4.mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ)
          * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
        rw [hC, ← neg_div]

end Work.LinnikAreas.Density4
