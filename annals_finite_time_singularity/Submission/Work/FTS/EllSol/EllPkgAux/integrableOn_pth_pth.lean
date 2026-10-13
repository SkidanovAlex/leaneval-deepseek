import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

/-- **From an `L²`-type bound to a linear bound.**  The interval `Iθ` has finite measure and
`|x| ≤ x² + 1/4` for every real `x`, so an a.e.-strongly-measurable `g` with `g²` integrable on
`Iθ` is itself integrable on `Iθ`. -/
private theorem integrableOn_of_sq_of_aesm {g : ℝ → ℝ}
    (hg2 : IntegrableOn (fun s : ℝ => g s ^ 2) Work.Spaces.Iθ)
    (hsm : AEStronglyMeasurable g (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn g Work.Spaces.Iθ := by
  have hvol : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => (1 / 4 : ℝ)) Work.Spaces.Iθ :=
    integrableOn_const hvol
  have href : IntegrableOn (fun s : ℝ => g s ^ 2 + 1 / 4) Work.Spaces.Iθ :=
    hg2.add hconst
  refine Integrable.mono' href hsm ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (g s - 1 / 2), sq_nonneg (g s + 1 / 2)]

/-- The angular slice `θ ↦ ∂_θ (∂_θ u)(z,θ)` is a.e.-strongly-measurable on `Iθ`: on the open
interval it agrees with the derivative of `θ ↦ ∂_θ u (z,θ)`, and a derivative is Borel
measurable.  (This is the only place where the differentiability hypothesis is used.) -/
private theorem aesm_pth_pth {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => Work.Spaces.pth u z θ')
        (Work.Spaces.pth (Work.Spaces.pth u) z θ) θ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have heq0 : (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ)
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ : ℝ => deriv (fun θ' : ℝ => Work.Spaces.pth u z θ') θ) := by
    refine Set.EqOn.aeEq_restrict ?_ measurableSet_Ioo
    intro θ hθ
    exact ((hder θ hθ).deriv).symm
  have heq : (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => deriv (fun θ' : ℝ => Work.Spaces.pth u z θ') θ) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    exact heq0
  exact (aestronglyMeasurable_deriv (fun θ' : ℝ => Work.Spaces.pth u z θ')
    (volume.restrict Work.Spaces.Iθ)).congr heq.symm

theorem integrableOn_pth_pth {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth u) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt (fun θ' : ℝ => Work.Spaces.pth u z θ') (Work.Spaces.pth (Work.Spaces.pth u) z θ) θ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ) Work.Spaces.Iθ := by
  exact integrableOn_of_sq_of_aesm
    (integrableOn_sq_of_integrableOn
      (g := fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth u) z θ) hint)
    (aesm_pth_pth hder)

end Work.FTS.EllSol.EllPkgAux
