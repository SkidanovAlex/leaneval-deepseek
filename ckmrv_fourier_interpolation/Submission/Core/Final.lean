import ChallengeDeps
import Submission.Core.Assembly
import Submission.Work.FunctionalEquations.MainGen
import Submission.Work.FunctionalEquations.Rigidity
import Submission.Work.Section8P.RigidityP
import Submission.Work.Interpolation.adapter_decay

/-!
# Final assembly of the CKMRV Fourier interpolation theorem

The challenge theorem is `CKMRV 8 1 ∧ CKMRV 24 2`.  Two reductions are already proved:

* `Submission.ckmrv_of_interpolationBasis` : an interpolation basis
  `Work.Core.InterpolationBasis n k₀` gives `CKMRV n k₀`;
* `Work.FE.interpolationBasis_of_functionalEquations_gen` (paper Theorem 3.1 with the basis
  starting at `k₀`) : a solution `Work.FE.InterpolationSolutionGen n k₀` of the functional
  equations, together with the coefficient data of Section 3.1 and the normalisations of
  Section 8, gives `Work.Core.InterpolationBasis n k₀`.

Combining them, the only remaining mathematical input is the construction of the two
solutions `InterpolationSolutionGen 8 1` and `InterpolationSolutionGen 24 2`, i.e. the
existence of the generating functions `F`, `F̃` for the `E₈` and Leech cases with the
functional equations, growth bounds and Section 8 normalisations (paper Sections 4-5 and
the uniqueness Lemma 3.4).
-/

open LeanEval.Analysis.CKMRVInterpolation
open Filter Topology
open scoped FourierTransform SchwartzMap

namespace Submission

/-- **The challenge theorem, from the two solutions of the functional equations.** -/
theorem ckmrv_of_interpolationSolutions (S8 : Work.FE.InterpolationSolutionGen 8 1)
    (S24 : Work.FE.InterpolationSolutionGen 24 2) : CKMRV 8 1 ∧ CKMRV 24 2 :=
  ⟨ckmrv_of_interpolationBasis 8 1
      (Work.FE.interpolationBasis_of_functionalEquations_gen (by norm_num) S8),
    ckmrv_of_interpolationBasis 24 2
      (Work.FE.interpolationBasis_of_functionalEquations_gen (by norm_num) S24)⟩

/-- **The challenge theorem from solutions of the functional equations alone.**  The paper's
uniqueness lemma (Section 8) is fully discharged here: `Work.Section8P` applies the proved statement
`Work.Rigidity.HomogeneousRigidityP` (the corrected, paper-faithful form of `lem:noPsolutions`, with its
moderate-growth hypothesis), so the only remaining input is the construction of the two solutions of the
functional equations, and -- for dimension 24 -- the decay `F, F̃ = o(e^{-2π Im τ})` in the strip. -/
theorem ckmrv_fourier_interpolation_of_functionalEquations
    (S8 : Work.FE.FunctionalEquationSolution 8) (S24 : Work.FE.FunctionalEquationSolution 24)
    (hdec : Work.FE.TendsToZeroInStrip 24 1 S24.F)
    (hdecT : Work.FE.TendsToZeroInStrip 24 1 S24.Ftilde) :
    CKMRV 8 1 ∧ CKMRV 24 2 := by
  obtain ⟨D8⟩ := Work.Section8P.interpolationBasis_eight_of_functionalEquations S8
  obtain ⟨basis24, hExp24⟩ := Work.FE.expansionData_of_functionalEquations (n := 24) S24
  obtain ⟨D24⟩ := Work.Section8P.interpolationBasis_twentyfour_of_functionalEquations S24 basis24
    hExp24 hdec hdecT
  exact ⟨ckmrv_of_interpolationBasis 8 1 D8, ckmrv_of_interpolationBasis 24 2 D24⟩

/-- **The challenge theorem from the hypothesis of Theorem 3.1 in the form of the kernel
construction.**  Given, for `d = 8` and `d = 24`, radial profiles `F, F̃ : UpperHalfPlane → ℝ → ℂ` satisfying
`Work.Kernels.SatisfiesThm31 d k₀ F Ft` (the hypotheses (1)-(5) of CKMRV Theorem 3.1), together with
their smoothness and evenness in the radius and -- for `d = 24` -- the strip decay
`F, F̃ = o(e^{-2π Im τ})`, the challenge theorem follows.  This is the exact shape of what
`Work.Kernels.satisfiesThm31_of_analysis` produces for `F = Fgen K`, `F̃ = Ftgen K̂`. -/
theorem ckmrv_fourier_interpolation_of_satisfiesThm31
    (F8 Ft8 : UpperHalfPlane → ℝ → ℂ) (h8 : Work.Kernels.SatisfiesThm31 8 1 F8 Ft8)
    (hsF8 : ∀ τ : UpperHalfPlane, ContDiff ℝ ⊤ (F8 τ)) (hsFt8 : ∀ τ : UpperHalfPlane, ContDiff ℝ ⊤ (Ft8 τ))
    (heF8 : ∀ τ : UpperHalfPlane, Function.Even (F8 τ)) (heFt8 : ∀ τ : UpperHalfPlane, Function.Even (Ft8 τ))
    (F24 Ft24 : UpperHalfPlane → ℝ → ℂ) (h24 : Work.Kernels.SatisfiesThm31 24 2 F24 Ft24)
    (hsF24 : ∀ τ : UpperHalfPlane, ContDiff ℝ ⊤ (F24 τ)) (hsFt24 : ∀ τ : UpperHalfPlane, ContDiff ℝ ⊤ (Ft24 τ))
    (heF24 : ∀ τ : UpperHalfPlane, Function.Even (F24 τ)) (heFt24 : ∀ τ : UpperHalfPlane, Function.Even (Ft24 τ))
    (hdecF : Work.FE.TendsToZeroInStrip 24 1
      (fun τ x => if h : 0 < τ.im then F24 ⟨τ, h⟩ ‖x‖ else 0))
    (hdecFt : Work.FE.TendsToZeroInStrip 24 1
      (fun τ x => if h : 0 < τ.im then Ft24 ⟨τ, h⟩ ‖x‖ else 0)) :
    CKMRV 8 1 ∧ CKMRV 24 2 := by
  obtain ⟨S8⟩ := Work.FunctionalEquations.Thm31Adapter (d := 8) (k₀ := 1) (by norm_num)
    F8 Ft8 h8 hsF8 hsFt8 heF8 heFt8
  obtain ⟨S24, -, -, hdecS24, hdecT24⟩ := Work.Interpolation.adapter_decay (d := 24) (k₀ := 2)
    (c := 1) (by norm_num) F24 Ft24 h24 hsF24 hsFt24 heF24 heFt24 hdecF hdecFt
  exact ckmrv_fourier_interpolation_of_functionalEquations S8 S24 hdecS24 hdecT24

/-- **The challenge theorem, from exactly the inputs the construction still owes.**

CAUTION: the hypothesis `Work.FE.HomogeneousRigidity` used here is *false as stated* (it omits the
moderate-growth hypothesis of the paper's uniqueness lemma; see
`Submission/Work/Rigidity/Counterexample.lean` and the ROADMAP).  The corrected route replaces it by
`Work.Rigidity.HomogeneousRigidityP` plus the `InP` hypotheses of the Section 8 pairs; that assembly is
being redone in `Submission/Work/Section8P/`.  This theorem is kept only as a record of the shape of the
assembly: it shows that, given the uniqueness lemma, solutions of the functional equations in dimensions
8 and 24 and the decay `F, F̃ = o(e^{-2π Im τ})` in dimension 24, the challenge theorem follows. -/
theorem ckmrv_fourier_interpolation_of_main_inputs
    (hR8 : Work.FE.HomogeneousRigidity 8 0) (S8 : Work.FE.FunctionalEquationSolution 8)
    (hR24 : Work.FE.HomogeneousRigidity 24 1) (S24 : Work.FE.FunctionalEquationSolution 24)
    (hdec : Work.FE.TendsToZeroInStrip 24 1 S24.F)
    (hdecT : Work.FE.TendsToZeroInStrip 24 1 S24.Ftilde) :
    CKMRV 8 1 ∧ CKMRV 24 2 := by
  obtain ⟨D8⟩ := Work.FE.interpolationBasis_of_functionalEquations_of_rigidity (n := 8) hR8 S8
  obtain ⟨basis24, hExp24⟩ := Work.FE.expansionData_of_functionalEquations (n := 24) S24
  obtain ⟨D24⟩ := Work.FE.interpolationBasis_two_of_rigidity_and_decay (n := 24) hR24 S24
    basis24 hExp24 hdec hdecT
  exact ⟨ckmrv_of_interpolationBasis 8 1 D8, ckmrv_of_interpolationBasis 24 2 D24⟩

/-- **The challenge theorem, from the two interpolation bases** (the same statement as
`ckmrv_of_deep`, with the explicit bases). -/
theorem ckmrv_fourier_interpolation_of_bases
    (D8 : Work.Core.InterpolationBasis 8 1) (D24 : Work.Core.InterpolationBasis 24 2) :
    CKMRV 8 1 ∧ CKMRV 24 2 :=
  ⟨ckmrv_of_interpolationBasis 8 1 D8, ckmrv_of_interpolationBasis 24 2 D24⟩

end Submission
