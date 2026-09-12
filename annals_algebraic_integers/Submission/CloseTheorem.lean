import Submission.FinalAssembly
import Submission.KeystonePerN
import Submission.AdjustContract
import Submission.EarlyIntsContract
import Submission.SqfAssembly
import ChallengeDeps

open AlgebraicIntegers
open ComplexOrder
open Filter
open Polynomial
open MeasureTheory
open scoped Real Topology

set_option autoImplicit false

namespace Submission.CloseTheorem

open Submission.Contracts
open Submission.SerreExample
open Submission.Serre
open Submission.Notions

noncomputable section

/-- Theorem 1.1 of the paper.

The root-mean clause of `EarlyIntsContract` (the quantitative mean bound of
`KeystonePerN.per_n_exists`) replaces the RSphere/Saff–Totik input, and the
squarefree contract is `Submission.SqfAssembly.squarefree_contract`
(Theorem squarefree of Smith's GON.tex).  Contracts 2 and 3 —
`AdjustContract`, `EarlyIntsContract` — are fully proven, as are the
arithmeticity of the Serre measure (`ArithmeticAssembly.serre_arithmetic`),
its moment bounds (`SerreExample.serre_moment_lt_189831`), the keystone
per-`n` Eisenstein assembly (`KeystonePerN.per_n_exists`,
`KeystonePerN.converse_output_of_contracts`), the algebraic bridge
(`AlgebraicBridge.bridge`), the family assembly (`Assembly.family_of_converse_data`)
and the reduction `Reduction.lambda_SSS_le_of_family`.) -/
theorem theorem_1_1_of_contracts :
    lambda_SSS < 1.89831 := by
  have hsqf : SquarefreeContract := Submission.SqfAssembly.squarefree_contract
  have hadj : AdjustContract := Submission.AdjustContract.adjust_contract
  have hearly : EarlyIntsContract := Submission.EarlyAssembly.early_ints_contract
  have hconv0 := Submission.KeystonePerN.converse_output_of_contracts hsqf hadj hearly
  change ∃ R : ℕ → Polynomial ℤ,
      (∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree) ∧
      (∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
      Tendsto (fun n : ℕ => (R n).natDegree) atTop atTop ∧
      Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop
        (𝓝 (∫ x : ℝ, x ∂serreMeasure gSerre aSerre bSerre)) at hconv0
  exact Submission.FinalAssembly.theorem_1_1_of_converse hconv0

end
