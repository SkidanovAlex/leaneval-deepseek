/-
# Swapping the order of integration in the two-dimensional coefficient `coeff2`

`coeff2 σ p₁ p₂ = ∫₀¹ ∫₀¹ σ(x,y) e(-p₁x - p₂y) dx dy` (`Work.KMTPlan.A6.SymToolbox`), the
`(p₁,p₂)`-th Fourier coefficient of the kernel symbol `σ` on the unit square.  This file proves
that the two orders of integration give the same value, i.e. the elementary Fubini statement

  `∫₀¹ ∫₀¹ F = ∫₀¹ ∫₀¹ F`   (with the roles of `x` and `y` exchanged),

for the continuous integrand `F x y = σ x y * e(-p₁x - p₂y)`.  The two iterated integrals are the
two sides of `Work.KMTPlan.A6.coeff2` read in the two possible orders; the identity is what lets
downstream arguments treat `coeff2` as a genuine two-dimensional coefficient (e.g. to compare it
with the transposed symbol `σ(y,x)`).

The proof is Fubini on the compact square: rewriting the interval integrals as integrals against
`volume.restrict (Ioc 0 1)`, noting `volume.restrict (Ioc 0 1) = volume.restrict (Icc 0 1)`
(differing by the null set `{0}`), and applying `MeasureTheory.integral_integral_swap`; the
integrability hypothesis is the compactness of `[0,1]²` together with continuity of the integrand.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral

/-- **Fubini on the unit square for a continuous integrand.**  The two iterated integrals of a
continuous `g : ℝ → ℝ → ℂ` over `[0,1] × [0,1]` agree. -/
lemma KMTPlan_integral_integral_swap_unit (g : ℝ → ℝ → ℂ) (hg : Continuous (Function.uncurry g)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, g x y)
      = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, g x y := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simp only [intervalIntegral.integral_of_le h01]
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  refine MeasureTheory.integral_integral_swap ?_
  rw [MeasureTheory.Measure.prod_restrict]
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hg.continuousOn

theorem SymToolbox_coeff2_swap (σ : ℝ → ℝ → ℂ) (p₁ p₂ : ℤ)
    (hcont : Continuous (fun p : ℝ × ℝ => σ p.1 p.2)) :
    Work.KMTPlan.A6.coeff2 σ p₁ p₂
      = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          σ x y * Work.KMTPlan.A6.eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := by
  have hg : Continuous (Function.uncurry
      (fun x y : ℝ => σ x y * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y))) := by
    show Continuous (fun p : ℝ × ℝ => σ p.1 p.2 * eeC (-(p₁ : ℝ) * p.1 - (p₂ : ℝ) * p.2))
    exact hcont.mul (by unfold eeC; fun_prop)
  unfold coeff2
  exact KMTPlan_integral_integral_swap_unit _ hg

end Work.KMTPlan.A6
