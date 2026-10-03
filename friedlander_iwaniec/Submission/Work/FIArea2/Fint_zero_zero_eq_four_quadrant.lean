import Mathlib
import Submission.Work.FIArea2.Sec6Hzero
import Submission.Work.FIArea2.lemma_7_6_identity

namespace Work.FIArea2

open MeasureTheory

/-- A real function which is even (`f (-x) = f x`) satisfies `∫ f = 2 ∫_{t>0} f`.
Immediate from `integral_comp_abs` (`∫ x, f |x| = 2 ∫_{x > 0} f x`), since `f ∘ |·| = f`. -/
lemma integral_eq_two_mul_integral_Ioi_of_neg {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) :
    ∫ x, f x = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  calc ∫ x, f x = ∫ x, f |x| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show f x = f |x|
        rcases le_total 0 x with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, hf x]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := integral_comp_abs

/-- **The evenness reduction of (6.8) at `u = 0`.**  The quartic `g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴`
of (7.1) is even in each variable, so the `F₀`-integral (6.11) over `ℝ²` is four times its
restriction to the quadrant:

`(Fint F γ 0 0).re = 4 ∫_{t₁>0} ∫_{t₂>0} F(g(t₁,t₂)) dt₂ dt₁`.

This is the bridge between `Work.FIArea2.Fint_zero_zero` (`Fint F γ 0 0 = ∫_{ℝ²}F(g)`, the object
(9.1) computes with) and the exact normalisation `Work.FIArea2.lemma_7_6_identity`
(`4∫∫_{quadrant} f(g) = (1/2)·A(γ)·∫f(u)u^{−1/2}du` with `A` the elliptic integral (7.8)), hence
between the Poisson main term `Fint F γ 0 0` and the paper's (7.10)
`F₀(z₁,z₂) = f̂(0)·2log(2|z₁z₂|/Δ) + O(δ²log δ^{−2})` (`Work.FIArea2.lemma_7_2_core`).
Route: `Work.FIArea2.Fint_zero_zero`, then `∫_{ℝ²} = 4∫∫_{quadrant}` for a function even in each
coordinate (the reflection `t ↦ −t` preserves Lebesgue measure; the axes are null), and the
ℂ-to-ℝ identification through `MeasureTheory.integral_re`. -/
theorem Fint_zero_zero_eq_four_quadrant (F : ℝ → ℝ) (γ : ℝ)
    (hF : MeasureTheory.Integrable fun t : ℝ × ℝ => F (Work.FIArea2.gQuartic γ t)) :
    (Work.FIArea2.Fint F γ 0 0).re
      = 4 * ∫ t₁ in Set.Ioi (0 : ℝ), ∫ t₂ in Set.Ioi (0 : ℝ),
            F (Work.FIArea2.gQuartic γ (t₁, t₂)) := by
  -- the integrand, seen as a function of the pair, so that the evenness statements are clean
  set H : ℝ × ℝ → ℝ := fun t => F (gQuartic γ t) with hHdef
  have even₁ : ∀ t₁ t₂ : ℝ, H (-t₁, t₂) = H (t₁, t₂) := by
    intro t₁ t₂
    have h : gQuartic γ (-t₁, t₂) = gQuartic γ (t₁, t₂) := by
      unfold gQuartic
      ring
    simp only [hHdef, h]
  have even₂ : ∀ t₁ t₂ : ℝ, H (t₁, -t₂) = H (t₁, t₂) := by
    intro t₁ t₂
    have h : gQuartic γ (t₁, -t₂) = gQuartic γ (t₁, t₂) := by
      unfold gQuartic
      ring
    simp only [hHdef, h]
  -- Fubini, then peel off the two reflections
  have hfub : ∫ t : ℝ × ℝ, H t = ∫ t₁, ∫ t₂, H (t₁, t₂) :=
    integral_prod H (by rw [hHdef]; exact hF)
  have hquad : ∫ t : ℝ × ℝ, H t
      = 4 * ∫ t₁ in Set.Ioi (0 : ℝ), ∫ t₂ in Set.Ioi (0 : ℝ), H (t₁, t₂) := by
    rw [hfub]
    have h₁ : ∫ t₁, ∫ t₂, H (t₁, t₂)
        = ∫ t₁, 2 * ∫ t₂ in Set.Ioi (0 : ℝ), H (t₁, t₂) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t₁ => ?_)
      exact integral_eq_two_mul_integral_Ioi_of_neg (fun t₂ => even₂ t₁ t₂)
    rw [h₁, integral_const_mul]
    rw [integral_eq_two_mul_integral_Ioi_of_neg (f := fun t₁ => ∫ t₂ in Set.Ioi (0 : ℝ),
      H (t₁, t₂)) (fun t₁ => ?_)]
    · ring
    · exact setIntegral_congr_fun measurableSet_Ioi (fun t₂ _ => even₁ t₁ t₂)
  -- replace the ℂ-valued integral of (6.11) by the real one, then apply the reduction
  have hcast : (∫ t : ℝ × ℝ, ((F (gQuartic γ t) : ℝ) : ℂ))
      = ((∫ t : ℝ × ℝ, F (gQuartic γ t) : ℝ) : ℂ) := integral_ofReal
  calc (Fint F γ 0 0).re
      = (∫ t : ℝ × ℝ, ((F (gQuartic γ t) : ℝ) : ℂ)).re := by rw [Fint_zero_zero]
    _ = ∫ t : ℝ × ℝ, F (gQuartic γ t) := by rw [hcast]; simp
    _ = 4 * ∫ t₁ in Set.Ioi (0 : ℝ), ∫ t₂ in Set.Ioi (0 : ℝ),
          F (gQuartic γ (t₁, t₂)) := by simpa only [hHdef] using hquad

end Work.FIArea2
