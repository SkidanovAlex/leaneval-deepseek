/-
Copyright: work module for the Elgindi finite-time singularity project.

# The flat shifted form, and the target proposition, as plain `Prop`s

`Work.FTS.EllSol.ShiftedFlatAux` is the *shifted flat* inequality: for every shift `b` the
(rather than the `Ω`-weighted) inequality with the operator `∂_t - b`, the heavy weight
`σ_η = sin(2θ)^{-η}` on the three right-hand slots and the light weight `σ_a = sin(2θ)^{2-γ}`
on the left-hand one.  It is the per-shift statement obtained from the target by the
decomposition `Ω(t) = Σ_{k<5} C(4,k) e^{(k-3)t}` (`Work.FTS.EllSol.flatShiftDecomp`) applied to
`u_k = e^{b_k t}g`, `b_k = (k-3)/2`.

`Work.FTS.EllSol.FlatWeightedAux` is *verbatim* the statement of
`Work.FTS.EllSol.flat2DAgmonWeighted` (the target), packaged as a `Prop` so that the reduction
can be stated and proved without importing a file that contains a `sorry`.

Both definitions are `sorry`-free; nothing here is a proof obligation.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set
open scoped Real

noncomputable section

set_option autoImplicit false

/-- The `Ω`-weight of the target, `Ω(t) = (1 + e^t)^4 e^{-3t}` (the paper's `Wt`). -/
def omegaAux (t : ℝ) : ℝ := (1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))

/-- The heavy angular weight `σ_η = sin(2θ)^{-η}`. -/
def sigEtaAux (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The light angular weight `σ_a = sin(2θ)^{2-γ(α)}`. -/
def sigAAux (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- **The shifted flat inequality.**  For every shift `b`, `C²` data `u` on the open strip
vanishing at `θ = 0, π/2`, with the three right-hand slots (of `(∂_t-b)u`, `(∂_t-b)²u`,
`∂_θ²u`, weighted by `σ_η`) integrable, the `(1,1)`-slot of `(∂_t-b)u` with the light weight
`σ_a` is bounded by the first-order slot plus the geometric mean of the two second-order
slots.  The conclusion is the (junk-compatible) iterated Bochner integral of the target. -/
def ShiftedFlatAux : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (b : ℝ) (u : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 →
    ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, u t 0 = 0) → (∀ t : ℝ, u t (Real.pi / 2) = 0) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
        + b ^ 2 * u p.1 p.2) ^ 2 * sigEtaAux p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * sigEtaAux p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * sigEtaAux p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
        * sigAAux α p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) ∧
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
          * sigAAux α p.2)
      ≤ C * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * sigEtaAux p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
                  + b ^ 2 * u p.1 p.2) ^ 2 * sigEtaAux p.2)
              * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * sigEtaAux p.2)))

/-- The statement of `Work.FTS.EllSol.flat2DAgmonWeighted`, packaged as a `Prop`. -/
def FlatWeightedAux : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 →
    ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) →
    (∀ t : ℝ, g t 0 = 0) → (∀ t : ℝ, g t (Real.pi / 2) = 0) →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz g) p.1 p.2) ^ 2 * (1 + Real.exp p.1) ^ 4 * Real.exp (-(3 * p.1)) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth g) p.1 p.2) ^ 2 * (1 + Real.exp p.1) ^ 4 * Real.exp (-(3 * p.1)) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.pz g p.1 p.2) ^ 2 * (1 + Real.exp p.1) ^ 4 * Real.exp (-(3 * p.1)) * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) →
    (∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pth g) t θ) ^ 2 * ((1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ C * ((∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz g t θ) ^ 2 * ((1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + Real.sqrt ((∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz g) t θ) ^ 2 * ((1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              * (∫ t in Set.univ, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth g) t θ) ^ 2 * ((1 + Real.exp t) ^ 4 * Real.exp (-(3 * t))) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))

end

end Work.FTS.EllSol
