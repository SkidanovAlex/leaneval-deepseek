import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HQoAux

/-- The elementary pointwise inequality: `(∑|aᵢ|)² ≤ 4 ∑ aᵢ²` (the identity
`4 ∑ aᵢ² - (∑ aᵢ)² = ∑_{i<j} (aᵢ - aⱼ)²`). -/
lemma sq_sum4_abs_le (a b c d : ℝ) :
    (|a| + |b| + |c| + |d|) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|), sq_nonneg (|a| - |d|),
             sq_nonneg (|b| - |c|), sq_nonneg (|b| - |d|), sq_nonneg (|c| - |d|),
             sq_abs a, sq_abs b, sq_abs c, sq_abs d]

theorem integral_sq_sum4_abs_le {s : Set (ℝ × ℝ)} {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ}
    (h₁ : MeasureTheory.IntegrableOn (fun x => (f₁ x) ^ 2) s)
    (h₂ : MeasureTheory.IntegrableOn (fun x => (f₂ x) ^ 2) s)
    (h₃ : MeasureTheory.IntegrableOn (fun x => (f₃ x) ^ 2) s)
    (h₄ : MeasureTheory.IntegrableOn (fun x => (f₄ x) ^ 2) s) :
    ∫ x in s, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
      ≤ 4 * ((∫ x in s, (f₁ x) ^ 2) + (∫ x in s, (f₂ x) ^ 2)
          + (∫ x in s, (f₃ x) ^ 2) + (∫ x in s, (f₄ x) ^ 2)) := by
  -- integrability of the comparison function `4 * (f₁² + f₂² + f₃² + f₄²)` on `s`
  have h1' : MeasureTheory.Integrable (fun x => (f₁ x) ^ 2) (MeasureTheory.volume.restrict s) := h₁
  have h2' : MeasureTheory.Integrable (fun x => (f₂ x) ^ 2) (MeasureTheory.volume.restrict s) := h₂
  have h3' : MeasureTheory.Integrable (fun x => (f₃ x) ^ 2) (MeasureTheory.volume.restrict s) := h₃
  have h4' : MeasureTheory.Integrable (fun x => (f₄ x) ^ 2) (MeasureTheory.volume.restrict s) := h₄
  have hGint : MeasureTheory.IntegrableOn
      (fun x => 4 * ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2 + (f₄ x) ^ 2)) s :=
    ((((h1'.add h2').add h3').add h4')).const_mul 4
  -- the pointwise comparison, integrated
  have hmono : ∫ x in s, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
      ≤ ∫ x in s, 4 * ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2 + (f₄ x) ^ 2) := by
    refine MeasureTheory.setIntegral_mono_of_nonneg
      (f := fun x => (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2)
      (g := fun x => 4 * ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2 + (f₄ x) ^ 2)) ?_ ?_ hGint
    · intro x _
      positivity
    · intro x _
      exact sq_sum4_abs_le (f₁ x) (f₂ x) (f₃ x) (f₄ x)
  -- linearity of the set integral on the comparison function
  have e1 : ∫ x in s, ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2 + (f₄ x) ^ 2)
      = (∫ x in s, ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2)) + (∫ x in s, (f₄ x) ^ 2) :=
    MeasureTheory.integral_add ((h1'.add h2').add h3') h4'
  have e2 : ∫ x in s, ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2)
      = (∫ x in s, ((f₁ x) ^ 2 + (f₂ x) ^ 2)) + (∫ x in s, (f₃ x) ^ 2) :=
    MeasureTheory.integral_add (h1'.add h2') h3'
  have e3 : ∫ x in s, ((f₁ x) ^ 2 + (f₂ x) ^ 2)
      = (∫ x in s, (f₁ x) ^ 2) + (∫ x in s, (f₂ x) ^ 2) :=
    MeasureTheory.integral_add h1' h2'
  calc ∫ x in s, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
      ≤ ∫ x in s, 4 * ((f₁ x) ^ 2 + (f₂ x) ^ 2 + (f₃ x) ^ 2 + (f₄ x) ^ 2) := hmono
    _ = 4 * ((∫ x in s, (f₁ x) ^ 2) + (∫ x in s, (f₂ x) ^ 2)
          + (∫ x in s, (f₃ x) ^ 2) + (∫ x in s, (f₄ x) ^ 2)) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [e1, e2, e3]

end Work.FTS.StrongEps.HQoAux
