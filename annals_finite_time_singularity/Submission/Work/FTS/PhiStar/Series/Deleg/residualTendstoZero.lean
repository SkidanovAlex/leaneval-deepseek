import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.EllipticEst.ModalSolution.eFam_parseval
import Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

open MeasureTheory Filter
open scoped BigOperators

/-- **The residual of the truncated angular mode series tends to zero in `L²(Iθ, cos θ dθ)`.**

For a slice `ψ` with `∫_{Iθ} ψ² cos θ < ∞` (and `ψ` a.e. strongly measurable), the partial
sums of its expansion in the Dirichlet eigenbasis `eFam m` of `Lzero`
(`eFam m θ = cos θ · gC (2m+1) (sin θ)`, orthogonal for the weight `cos θ dθ`) converge to `ψ`
in `L²(Iθ, cos θ dθ)`.

This is the combination of the two standard facts about the truncated expansion:

* Pythagoras (`Work.EllipticEst.ModalSolution.eFam_pythagoras`): the residual is the `L²`-norm
  defect
  `∫ (ψ - Σ_{m≤N} c_m e_m)² cos = ∫ ψ² cos - Σ_{m≤N} c_m² ∫ e_m² cos`,
  `c_m = cmode m (fun _ θ' => ψ θ') 0`;
* Parseval (`Work.EllipticEst.ModalSolution.eFam_parseval`): the defect itself tends to `0`,
  `Σ_{m≤N} c_m² ∫ e_m² cos → ∫ ψ² cos`.

Both are applied to the `z`-independent slice `fun _ θ' => ψ θ'` at `z = 0`, for which
`(fun _ θ' => ψ θ') 0 = ψ` definitionally. -/
theorem residualTendstoZero (ψ : ℝ → ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      Filter.atTop (nhds 0) := by
  have hmeas' : MeasureTheory.AEStronglyMeasurable ((fun _ θ' => ψ θ') 0)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hmeas
  have hz' : MeasureTheory.IntegrableOn
      (fun θ => (fun _ θ' => ψ θ') 0 θ ^ 2 * Real.cos θ) Work.Spaces.Iθ := hz
  -- Pythagoras identifies the residual with the `L²`-norm defect.
  have hkey : (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = fun N : ℕ => (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0) ^ 2 *
              (∫ θ in Work.Spaces.Iθ,
                Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    funext N
    exact Work.EllipticEst.ModalSolution.eFam_pythagoras
      (fun _ θ' => ψ θ') 0 N hmeas' hz'
  rw [hkey]
  -- Parseval says the defect tends to the full `L²`-mass, so the residual tends to `0`.
  have h1 : Filter.Tendsto (fun _ : ℕ => (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ))
      Filter.atTop (nhds (∫ θ in Work.Spaces.Iθ, ψ θ ^ 2 * Real.cos θ)) :=
    tendsto_const_nhds
  have h2 := h1.sub (Work.EllipticEst.ModalSolution.eFam_parseval
    (fun _ θ' => ψ θ') 0 hmeas' hz')
  simpa using h2

end Work.FTS.PhiStar.Series.Deleg
