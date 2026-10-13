import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `weakDiv_pair` — the divergence pairing of the pair `(q, Φ)` is additive

Writing `Φ := ∂ₜu − u×ω` (here `lamb u ω`), the weak divergence identity for `Φ` is the
*difference* of the weak divergence identity for `∂ₜu` (`hdiv`, vanishing because the slices
`u · s` are divergence-free) and the weak Poisson identity for the Lamb vector (`hpois`, the
defining property of the Newtonian potential `q = pressurePotential (lamb u ω · t)`):

  `∫ ⟪∂ₜu − u×ω, ∇φ⟫ = ∫ ⟪∂ₜu, ∇φ⟫ − ∫ ⟪u×ω, ∇φ⟫ = 0 − ∫ q Δφ = −∫ q Δφ`.

The only analytic input is that both pairings against the gradient of a compactly supported smooth
test function are integrable: `∇φ` is compactly supported and continuous, so each pairing is the
product of a continuous function with a compactly supported one.
-/

open MeasureTheory Filter Set Topology

namespace Work.FTS.PressureOn.Connect

theorem weakDiv_pair {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {t : ℝ}
    {φ : Work.FTS.PressureOn.R3 → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hφcs : HasCompactSupport φ)
    (hAc : Continuous fun x => Work.FTS.PressureOn.lamb u ω x t)
    (hBc : Continuous fun x => FiniteTimeSingularity.timeDeriv u x t)
    (hdiv : ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x) = 0)
    (hpois : ∫ x, Work.FTS.PressureOn.pressurePotential (Work.FTS.PressureOn.lamb u ω · t) x
        * Work.FTS.PressureOn.laplaceTrace φ x
      = ∫ x, inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t
        - Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)
      = -∫ x, Work.FTS.PressureOn.pressurePotential (Work.FTS.PressureOn.lamb u ω · t) x
          * Work.FTS.PressureOn.laplaceTrace φ x := by
  -- `∇φ` is continuous and compactly supported.
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm
        (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm.continuous.comp
        ((hφ 1).continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : Work.FTS.PressureOn.R3 →L[ℝ] ℝ =>
        (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  -- The two pairings with `∇φ` are continuous with compact support, hence integrable.
  have hcsA : HasCompactSupport
      (fun x => inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x)) :=
    hgradcs.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro hg
      exact hx (by simp [hg])
  have hcsB : HasCompactSupport
      (fun x => inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :=
    hgradcs.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro hg
      exact hx (by simp [hg])
  have hA : Integrable
      (fun x => inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x)) :=
    (hBc.inner hgradcont).integrable_of_hasCompactSupport hcsA
  have hB : Integrable
      (fun x => inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :=
    (hAc.inner hgradcont).integrable_of_hasCompactSupport hcsB
  -- Split the integral of the difference.
  have hsub : (∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t
        - Work.FTS.PressureOn.lamb u ω x t) (gradient φ x))
      = (∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x))
        - (∫ x, inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) := by
    rw [← integral_sub hA hB]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [inner_sub_left]
  rw [hsub, hdiv, hpois]
  ring

end Work.FTS.PressureOn.Connect
