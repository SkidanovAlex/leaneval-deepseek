import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase

namespace Work.LinnikAreas.TuranOther

open Complex Filter
open scoped Topology

/-- An entire function which is not identically zero has finite order of vanishing at every
point: if its order of vanishing were infinite, it would vanish in a whole neighbourhood, hence
everywhere by the identity theorem. -/
lemma analyticOrderAt_ne_top_of_diff_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : f ≠ 0) (u : ℂ) : analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have hf_an : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have h0_an : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ := fun z _ => analyticAt_const
  have hev : f =ᶠ[𝓝 u] (0 : ℂ → ℂ) := analyticOrderAt_eq_top.mp htop
  exact hne (hf_an.eq_of_eventuallyEq h0_an hev)

/-- The order of vanishing of a product of two entire functions which are not identically zero is
the sum of the orders of vanishing of the factors. -/
lemma analyticOrderNatAt_mul_of_differentiable {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f ≠ 0) (hg0 : g ≠ 0) (u : ℂ) :
    analyticOrderNatAt (f * g) u = analyticOrderNatAt f u + analyticOrderNatAt g u :=
  analyticOrderNatAt_mul (hf.analyticAt u) (hg.analyticAt u)
    (analyticOrderAt_ne_top_of_diff_ne_zero hf hf0 u)
    (analyticOrderAt_ne_top_of_diff_ne_zero hg hg0 u)

/-- **Order of vanishing of `L(χ,·)` versus `Λ(χ,·)` and the inverse archimedean Gamma factor.**

For a non-principal Dirichlet character `χ` and the integer `a ∈ {0,1}` attached to its parity
(`a = 0` when `χ` is even, `a = 1` when `χ` is odd), the completed L-function satisfies
`Λ(χ,s) = L(χ,s) · Gammaℝ (s+a)` as functions of `s` (the Gamma factor is the one which the
completion multiplies in).  Both `Λ(χ,·)` and `(Gammaℝ (·+a))⁻¹` are entire, so on multiplying the
identity by the inverse Gamma factor we obtain

`L(χ,·) = Λ(χ,·) * (Gammaℝ (·+a))⁻¹`

and the order of vanishing of a product of entire functions is additive.  This yields the stated
identity for all `u : ℂ`, including the trivial zeros of `L(χ,·)` (where the Gamma factor has a
pole and `(Gammaℝ (·+a))⁻¹` has a simple zero). -/
theorem lFunctionOrderAddInvGammaR {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (a : ℕ)
    (ha0 : χ.Even → a = 0) (ha1 : χ.Odd → a = 1) (u : ℂ) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) u =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u
        + analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹) u := by
  have hN : N ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  -- the archimedean factor `gammaFactor χ` is `Gammaℝ (· + a)`
  have hgamma : ∀ z : ℂ, DirichletCharacter.gammaFactor χ z = Complex.Gammaℝ (z + (a:ℂ)) := by
    intro z
    rcases χ.even_or_odd with hE | hO
    · rw [DirichletCharacter.Even.gammaFactor_def hE, ha0 hE]; simp
    · rw [DirichletCharacter.Odd.gammaFactor_def hO, ha1 hO]; norm_num
  -- the factorization `L = Λ * (Gammaℝ (·+a))⁻¹` as functions
  have hfun : DirichletCharacter.LFunction χ
      = DirichletCharacter.completedLFunction χ
        * (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) := by
    funext s
    rw [Pi.mul_apply, ← div_eq_mul_inv, ← hgamma s]
    exact DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN)
  have hΛd : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hGd : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (a:ℂ))
  -- both factors are entire and not identically zero, so their orders of vanishing are finite
  have hΛ0 : DirichletCharacter.completedLFunction χ ≠ 0 := by
    have hL0 : DirichletCharacter.LFunction χ ≠ 0 := by
      intro h
      have h2 := congr_fun h (2:ℂ)
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num) h2
    intro h
    apply hL0
    funext s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN), congr_fun h s]
    simp
  have hG0 : (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) ≠ 0 := by
    intro h
    have h1 := congr_fun h (1 - (a:ℂ))
    simp only [Pi.zero_apply] at h1
    rw [show (1 - (a:ℂ)) + (a:ℂ) = 1 by ring, Complex.Gammaℝ_one] at h1
    norm_num at h1
  rw [hfun]
  exact analyticOrderNatAt_mul_of_differentiable hΛd hGd hΛ0 hG0 u

end Work.LinnikAreas.TuranOther
