import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- For a smooth compactly supported real function on `ℝ³`, each squared coordinate Fréchet
derivative is integrable, so the finite sum of the three integrals is the integral of the sum.
(`Work.BoseBoxFock.PCFU.sum_integral_fderivSq_eq`.) -/
theorem sum_integral_fderivSq_eq {G : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hs : HasCompactSupport G) :
    (∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      = ∫ u : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
        ‖fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  -- Each coordinate derivative is continuous (as the Fréchet derivative is) and compactly
  -- supported (its support is contained in that of `fderiv ℝ G`), hence so is its square.
  have hmain : ∀ k : Fin 3, Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ‖fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) := by
    intro k
    have hc : Continuous (fun u : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))) :=
      hcont.clm_apply continuous_const
    have hcs : HasCompactSupport (fun u : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))) :=
      (hs.fderiv ℝ).mono (fun u hu => fun h => hu (by simp [h]))
    exact (hc.norm.pow 2).integrable_of_hasCompactSupport
      (hcs.mono (fun u hu => fun h => hu (by simp [h])))
  -- Finite sums interchange with the integral.
  have h := integral_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (f := fun k u => ‖fderiv ℝ G u (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) Finset.univ
    (fun i _ => hmain i)
  simpa using h.symm

end Work.BoseBoxFock.PCFU
