import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Kinetic

theorem box_cauchy_schwarz {s : Set (EuclideanSpace ℝ (Fin 3))} {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => f z * g z)
        (MeasureTheory.volume.restrict s) ∧
      |∫ z in s, f z * g z| ≤ Real.sqrt (∫ z in s, (f z) ^ 2)
        * Real.sqrt (∫ z in s, (g z) ^ 2) := by
  refine ⟨?_, ?_⟩
  · -- Integrability of the pointwise product of two `L²` functions: Hölder with `p = q = 2`.
    exact hf.integrable_mul hg
  · -- Cauchy–Schwarz / Hölder with conjugate exponents `2, 2`, for `volume.restrict s`.
    exact Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hf hg

end Work.BoseKinLoc.Kinetic
