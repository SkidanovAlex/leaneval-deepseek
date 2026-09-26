import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.Gen
import Submission.Work.FunctionalEquations.MainGen

/-!
# The `k₀ = 1` bridge between the two structures

`Work.FE.InterpolationSolution n` and `Work.FE.InterpolationSolutionGen n 1` carry exactly
the same data (the index set is `Set.Ici 1` in both).  These two maps let a caller use
whichever one is convenient.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- The specialized structure is the `k₀ = 1` case of the general one. -/
def InterpolationSolution.toGen {n : ℕ} [NeZero n] (S : InterpolationSolution n) :
    InterpolationSolutionGen n 1 where
  toFunctionalEquationSolution := S.toFunctionalEquationSolution
  basis := S.basis
  expansion_F := S.expansion_F
  expansion_Ftilde := S.expansion_Ftilde
  expansion_F_radialDeriv := S.expansion_F_radialDeriv
  expansion_Ftilde_radialDeriv := S.expansion_Ftilde_radialDeriv
  fourier_basis := S.fourier_basis
  fourier_basis' := S.fourier_basis'
  value_F := S.value_F
  value_Ftilde := S.value_Ftilde
  value_radialDeriv_F := S.value_radialDeriv_F
  value_radialDeriv_Ftilde := S.value_radialDeriv_Ftilde
  growth_radial := S.growth_radial

/-- The `k₀ = 1` case of the general structure is the specialized one. -/
def InterpolationSolutionGen.toKOne {n : ℕ} [NeZero n] (S : InterpolationSolutionGen n 1) :
    InterpolationSolution n where
  toFunctionalEquationSolution := S.toFunctionalEquationSolution
  basis := S.basis
  expansion_F := S.expansion_F
  expansion_Ftilde := S.expansion_Ftilde
  expansion_F_radialDeriv := S.expansion_F_radialDeriv
  expansion_Ftilde_radialDeriv := S.expansion_Ftilde_radialDeriv
  fourier_basis := S.fourier_basis
  fourier_basis' := S.fourier_basis'
  value_F := S.value_F
  value_Ftilde := S.value_Ftilde
  value_radialDeriv_F := S.value_radialDeriv_F
  value_radialDeriv_Ftilde := S.value_radialDeriv_Ftilde
  growth_radial := S.growth_radial

/-- The general theorem at `k₀ = 1` gives the specialized theorem. -/
noncomputable def interpolationBasis_of_functionalEquations_of_gen {n : ℕ} [NeZero n]
    (S : InterpolationSolutionGen n 1) : Work.Core.InterpolationBasis n 1 :=
  interpolationBasis_of_functionalEquations_gen (by norm_num) S

end Work.FE
