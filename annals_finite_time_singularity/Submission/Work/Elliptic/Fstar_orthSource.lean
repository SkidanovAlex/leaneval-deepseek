import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The angular weight `sinCos2` is continuous. -/
lemma continuous_sinCos2 : Continuous (fun θ : ℝ => sinCos2 θ) := by
  simp only [sinCos2]; fun_prop

/-- `orthSource F` is orthogonal to `sin θ cos²θ`: the source left after adding `G sin 2θ`,
`F - (15/4) sin 2θ · F_*(z)`, has vanishing angular moment `F_*`. -/
theorem Fstar_orthSource (F : ℝ → ℝ → ℝ) (z : ℝ)
    (hF : ContinuousOn (fun θ : ℝ => F z θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Work.Elliptic.orthSource F) z = 0 := by
  have key : ∫ θ in Set.Icc (0 : ℝ) (π / 2),
      (F z θ - (15 / 4) * Real.sin (2 * θ) * Fstar F z) * sinCos2 θ = 0 := by
    have hf : IntegrableOn (fun θ : ℝ => F z θ * sinCos2 θ) (Set.Icc (0 : ℝ) (π / 2)) :=
      (hF.mul continuous_sinCos2.continuousOn).integrableOn_compact isCompact_Icc
    have hg : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) * sinCos2 θ)
        (Set.Icc (0 : ℝ) (π / 2)) := by
      have : Continuous fun θ : ℝ => Real.sin (2 * θ) * sinCos2 θ := by
        simp only [sinCos2]; fun_prop
      exact this.continuousOn.integrableOn_compact isCompact_Icc
    have hsin : ∫ θ in Set.Icc (0 : ℝ) (π / 2), Real.sin (2 * θ) * sinCos2 θ = 4 / 15 :=
      integral_sin_two_mul_sinCos2
    have hpt : EqOn (fun θ : ℝ => (F z θ - (15 / 4) * Real.sin (2 * θ) * Fstar F z) * sinCos2 θ)
        (fun θ : ℝ => F z θ * sinCos2 θ
          - ((15 / 4) * Fstar F z) * (Real.sin (2 * θ) * sinCos2 θ)) (Set.Icc (0 : ℝ) (π / 2)) :=
      fun θ _ => by ring
    rw [setIntegral_congr_fun measurableSet_Icc hpt]
    rw [integral_sub hf (hg.const_mul ((15 / 4) * Fstar F z)), integral_const_mul, hsin]
    rw [show (∫ θ in Set.Icc (0 : ℝ) (π / 2), F z θ * sinCos2 θ) = Fstar F z from rfl]
    ring
  exact key

end Work.Elliptic
