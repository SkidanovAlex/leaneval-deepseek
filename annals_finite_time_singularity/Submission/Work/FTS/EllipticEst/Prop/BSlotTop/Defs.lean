/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/Defs`: the slot abbreviations of the `B`-half of the induction step

The vocabulary of `Work.FTS.EllipticEst.remov.TopCoreB.BHalfClean`, in the namespace
`Work.FTS.EllipticEst.Prop.BSlotTop`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false

/-- The source slot, with the source written as `TT.ESW.Gsl`. -/
abbrev GsumC (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- The lower angular chain sum of `B = ∂_θθΨ`. -/
abbrev EsumrC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)

/-- The top plain angular slot of `Ψ`. -/
abbrev UslC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)

/-- The high angular slots of `Ψ`. -/
abbrev EjsumC (α : ℝ) (k : ℕ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)

/-- The `η`-weighted slot of `∂_θθΨ`. -/
abbrev EtaslC (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
    ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The low order terms `∫∫(Ψ')² w²` and `∫∫Ψ² w²`, as two separate integrals. -/
abbrev LoslC (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
    + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

end Work.FTS.EllipticEst.Prop.BSlotTop
