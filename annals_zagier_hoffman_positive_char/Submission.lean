/-
Copyright (c) 2026 Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Helpers
import ChallengeDeps
import Submission.ZagierHoffmanProof.Counting
import Submission.ZagierHoffmanProof.StepL193
import Submission.ZagierHoffmanProof.Nonvanishing
import Submission.ZagierHoffmanProof.Degree
import Submission.ZagierHoffmanProof.StepM
import Submission.ZagierHoffmanProof.Prime
import Submission.ZagierHoffmanProof.PrimeAll
import Submission.ZagierHoffmanProof.DegLin
import Submission.ZagierHoffmanProof.AnyQ
import Submission.ZagierHoffmanProof.DegAnyF
import Submission.ZagierHoffmanProof.DegCountAnyF
import Submission.ZagierHoffmanProof.LinIndep
import Submission.ZagierHoffmanProof.CountT0
import Submission.ZagierHoffmanProof.PrimeIndep
import Submission.ZagierHoffmanProof.ZetaShuffle
import Submission.ZagierHoffmanProof.ShuffleGen
import Submission.ZagierHoffmanProof.ShuffleDepth
import Submission.ZagierHoffmanProof.DBound
import Submission.ZagierHoffmanProof.ShuffleSpan
import Submission.ZagierHoffmanProof.CountT0More
import Submission.ZagierHoffmanProof.TrivialRange
import Submission.ZagierHoffmanProof.FrobZ
import Submission.ZagierHoffmanProof.CountRank
import Submission.ZagierHoffmanProof.CountComp
import Submission.ZagierHoffmanProof.ShuffleGenRegression
import Submission.ZagierHoffmanProof.Carlitz
import Submission.ZagierHoffmanProof.CarlitzAT
import Submission.ZagierHoffmanProof.CarlitzRegression
import Submission.ZagierHoffmanProof.CarlitzLog
import Submission.ZagierHoffmanProof.CarlitzLogRegression
import Submission.ZagierHoffmanProof.CarlitzModule
import Submission.ZagierHoffmanProof.CarlitzModuleRegression
import Submission.ZagierHoffmanProof.CarlitzExpLog
import Submission.ZagierHoffmanProof.CarlitzExpLogRegression
import Submission.ZagierHoffmanProof.ATPsi
import Submission.ZagierHoffmanProof.ATPsiRegression
import Submission.ZagierHoffmanProof.ATDrinfeld
import Submission.ZagierHoffmanProof.ATSeries
import Submission.ZagierHoffmanProof.ATSeriesRegression
import Submission.ZagierHoffmanProof.ATFormula
import Submission.ZagierHoffmanProof.ATFormulaRegression
import Submission.ZagierHoffmanProof.Descent
import Submission.ZagierHoffmanProof.DescentRegression
import Submission.ZagierHoffmanProof.DescentGen
import Submission.ZagierHoffmanProof.DescentGenCor
import Submission.ZagierHoffmanProof.DescentGenRegression
import Submission.ZagierHoffmanProof.ATClaim
import Submission.ZagierHoffmanProof.ATForm
import Submission.ZagierHoffmanProof.ATMain
import Submission.ZagierHoffmanProof.AExpansionRegression
import Submission.ZagierHoffmanProof.AFormulaDegreeRegression
import Submission.ZagierHoffmanProof.ATIntegralRegression
import Submission.ZagierHoffmanProof.ATBridge
import Submission.ZagierHoffmanProof.ATBridgeRegression
import Submission.ZagierHoffmanProof.ThakurForm
import Submission.ZagierHoffmanProof.ThakurFormRegression
import Submission.ZagierHoffmanProof.GenFun
import Submission.ZagierHoffmanProof.GenFunRegression
import Submission.ZagierHoffmanProof.BridgeConsequences
import Submission.ZagierHoffmanProof.AFrobenius
import Submission.ZagierHoffmanProof.Entire
import Submission.ZagierHoffmanProof.EntireTwist
import Submission.ZagierHoffmanProof.EntireApp
import Submission.ZagierHoffmanProof.EntireRegression
import Submission.ZagierHoffmanProof.Omega
import Submission.ZagierHoffmanProof.OmegaRegression
import Submission.ZagierHoffmanProof.LSeries
import Submission.ZagierHoffmanProof.LSeriesRegression
import Submission.ZagierHoffmanProof.LSeriesFold
import Submission.ZagierHoffmanProof.LSeriesDepth
import Submission.ZagierHoffmanProof.LSeriesDepthRegression
import Submission.ZagierHoffmanProof.SuperEntire
import Submission.ZagierHoffmanProof.SuperEntireApp
import Submission.ZagierHoffmanProof.SuperEntireRegression
import Submission.ZagierHoffmanProof.KummerField
import Submission.ZagierHoffmanProof.OmegaD
import Submission.ZagierHoffmanProof.PeriodDatum
import Submission.ZagierHoffmanProof.PeriodL
import Submission.ZagierHoffmanProof.PeriodLRegression
import Submission.ZagierHoffmanProof.SuperOmega
import Submission.ZagierHoffmanProof.SuperOmegaRegression
import Submission.ZagierHoffmanProof.SuperPeriod
import Submission.ZagierHoffmanProof.SuperLSeries
import Submission.ZagierHoffmanProof.SuperLSeriesRegression
import Submission.ZagierHoffmanProof.EvalEntire
import Submission.ZagierHoffmanProof.EvalEntireRegression
import Submission.ZagierHoffmanProof.MZProperty
import Submission.ZagierHoffmanProof.MZPropertyRegression
import Submission.ZagierHoffmanProof.Specialisation
import Submission.ZagierHoffmanProof.SpecialisationRegression
import Submission.ZagierHoffmanProof.GenEntire
import Submission.ZagierHoffmanProof.GenEntireRegression
import Submission.ZagierHoffmanProof.GenEvalEntire
import Submission.ZagierHoffmanProof.GenLSeries
import Submission.ZagierHoffmanProof.GenLSeriesRegression
import Submission.ZagierHoffmanProof.GenLSeriesFold
import Submission.ZagierHoffmanProof.GenLSeriesDepth
import Submission.ZagierHoffmanProof.GenSuperLSeries
import Submission.ZagierHoffmanProof.GenMZProperty
import Submission.ZagierHoffmanProof.GenSpecialisation
import Submission.ZagierHoffmanProof.GenOmega
import Submission.ZagierHoffmanProof.GenPeriodDatum
import Submission.ZagierHoffmanProof.FrobPow
import Submission.ZagierHoffmanProof.FrobPowTsum
import Submission.ZagierHoffmanProof.FrobPowRegression
import Submission.ZagierHoffmanProof.ABPDiv
import Submission.ZagierHoffmanProof.ABPGauss
import Submission.ZagierHoffmanProof.ABPClincher
import Submission.ZagierHoffmanProof.ABPFunctionalEq
import Submission.ZagierHoffmanProof.GenChapterRegression
import Submission.ZagierHoffmanProof.AmbientField
import Submission.ZagierHoffmanProof.AmbientRing
import Submission.ZagierHoffmanProof.ABPZero
import Submission.ZagierHoffmanProof.ABPVanishing
import Submission.ZagierHoffmanProof.ABPKey
import Submission.ZagierHoffmanProof.ABPPoly
import Submission.ZagierHoffmanProof.ABPValue
import Submission.ZagierHoffmanProof.ABPFinal
import Submission.ZagierHoffmanProof.AmbRoot
import Submission.ZagierHoffmanProof.ABPSiegel
import Submission.ZagierHoffmanProof.ABPAux
import Submission.ZagierHoffmanProof.ABPFuncEq
import Submission.ZagierHoffmanProof.ABPZeros
import Submission.ZagierHoffmanProof.ABPAssemble
import Submission.ZagierHoffmanProof.AmbRootLevel
import Submission.ZagierHoffmanProof.TmRoot
import Submission.ZagierHoffmanProof.TmMotive
import Submission.ZagierHoffmanProof.TmPhi
import Submission.ZagierHoffmanProof.TmCriterion
import Submission.ZagierHoffmanProof.TmApply
import Submission.ZagierHoffmanProof.ABPKperf
import Submission.ZagierHoffmanProof.AmbField
import Submission.ZagierHoffmanProof.AbpDescent
import Submission.ZagierHoffmanProof.AbpDescentMain
import Submission.ZagierHoffmanProof.AbpDescentRestrict
import Submission.ZagierHoffmanProof.DescentRelation
import Submission.ZagierHoffmanProof.DescentLambda
import Submission.ZagierHoffmanProof.DescentIndependent
import Submission.ZagierHoffmanProof.DescentLevel
import Submission.ZagierHoffmanProof.Step2Complete
import Submission.ZagierHoffmanProof.Rationality
import Submission.ZagierHoffmanProof.KuanLin
import Submission.ZagierHoffmanProof.LinearIndependence
import Submission.ZagierHoffmanProof.AmbPeriod
import Submission.ZagierHoffmanProof.EllFrob
import Submission.ZagierHoffmanProof.AmbPeriodEll
import Submission.ZagierHoffmanProof.LSeriesEval
import Submission.ZagierHoffmanProof.LSeriesEvalSummable
import Submission.ZagierHoffmanProof.Step3Arith
import Submission.ZagierHoffmanProof.OmUnit
import Submission.ZagierHoffmanProof.ACMplDatum
import Submission.ZagierHoffmanProof.AmbKEquiv
import Submission.ZagierHoffmanProof.Step3Val
import Submission.ZagierHoffmanProof.AmbInf
import Submission.ZagierHoffmanProof.AmbZeta
import Submission.ZagierHoffmanProof.AmbPure
import Submission.ZagierHoffmanProof.AmbTransferVal
import Submission.ZagierHoffmanProof.AmbEll
import Submission.ZagierHoffmanProof.ZetaCMPL
import Submission.ZagierHoffmanProof.EvalDepthBound
import Submission.ZagierHoffmanProof.LSeriesEvalDepth
import Submission.ZagierHoffmanProof.ChainEval
import Submission.ZagierHoffmanProof.ChainSwap
import Submission.ZagierHoffmanProof.ATBridge2
import Submission.ZagierHoffmanProof.MZVDatum
import Submission.ZagierHoffmanProof.Step3Splitting
import Submission.ZagierHoffmanProof.Step3General
import Submission.ZagierHoffmanProof.Step3Final
import Submission.ZagierHoffmanProof.Step3Tuple
import Submission.ZagierHoffmanProof.TheoremB
import Submission.ZagierHoffmanProof.ATSecondBlock
import Submission.ZagierHoffmanProof.ATPoly
import Submission.ZagierHoffmanProof.PowerSumSecondBlock
import Submission.ZagierHoffmanProof.ATInterp
import Submission.ZagierHoffmanProof.NestP
import Submission.ZagierHoffmanProof.HDatum
import Submission.ZagierHoffmanProof.BridgeP
import Submission.ZagierHoffmanProof.ChainP
import Submission.ZagierHoffmanProof.BridgeP2
import Submission.ZagierHoffmanProof.TpAux
import Submission.ZagierHoffmanProof.TpCount
import Submission.ZagierHoffmanProof.TpTrans
import Submission.ZagierHoffmanProof.Solve64
import Submission.ZagierHoffmanProof.Endgame2
import Submission.ZagierHoffmanProof.DegTheta
import Submission.ZagierHoffmanProof.IntegralDelta
import Submission.ZagierHoffmanProof.EndgameDeg
import Submission.ZagierHoffmanProof.EndgameRow
import Submission.ZagierHoffmanProof.EndgameBound
import Submission.ZagierHoffmanProof.DegNu
import Submission.ZagierHoffmanProof.CoeffNu
import Submission.ZagierHoffmanProof.XSubOneCoprime
import Submission.ZagierHoffmanProof.LqSupport
import Submission.ZagierHoffmanProof.AntidiagonalSum
import Submission.ZagierHoffmanProof.CoeffTwoTerms
import Submission.ZagierHoffmanProof.EndgameReads
import Submission.ZagierHoffmanProof.CoeffSupport
import Submission.ZagierHoffmanProof.Step3H
import Submission.ZagierHoffmanProof.TupleIndP
import Submission.ZagierHoffmanProof.CoeffW
import Submission.ZagierHoffmanProof.TwRows
import Submission.ZagierHoffmanProof.PiTildeDvd
import Submission.ZagierHoffmanProof.TmFShared
import Submission.ZagierHoffmanProof.Step3HShared
import Submission.ZagierHoffmanProof.Step6H
import Submission.ZagierHoffmanProof.Step6Tuple
import Submission.ZagierHoffmanProof.Step7Endgame
import Submission.ZagierHoffmanProof.Step8TpAssemble
import Submission.ZagierHoffmanProof.DegFrac
import Submission.ZagierHoffmanProof.DegRow
import Submission.ZagierHoffmanProof.RowDen
import Submission.ZagierHoffmanProof.TwistInv
import Submission.ZagierHoffmanProof.TpBasis
import Submission.ZagierHoffmanProof.DenRec
import Submission.ZagierHoffmanProof.EndgameA0
import Submission.ZagierHoffmanProof.EndgameNum
import Submission.ZagierHoffmanProof.EndgameNdeg
import Submission.ZagierHoffmanProof.EndgameFinal
import Submission.ZagierHoffmanProof.EndgameTwRow
import Submission.ZagierHoffmanProof.EndgameKQ
import Submission.ZagierHoffmanProof.EndgameLast1
import Submission.ZagierHoffmanProof.EndgameLast2
import Submission.ZagierHoffmanProof.EndgameLast3
import Submission.ZagierHoffmanProof.EndgameLast4
import Submission.ZagierHoffmanProof.EndgameLast5
import Submission.ZagierHoffmanProof.EndgameLast6
import Submission.ZagierHoffmanProof.EndgameLast7
import Submission.ZagierHoffmanProof.EndgameLast8
import Submission.ZagierHoffmanProof.EndgameLast9
import Submission.ZagierHoffmanProof.EndgameLast10
/-!
# Main Statements from On Zagier-Hoffman's conjectures in positive characteristic

We formalise the statements of the main results from T. N. Dac,
`On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021.

## Implementation Details

Throughout the definitions and statements, we reindex the `i`'s so that they run from `0`
to `r - 1` rather than from `1` to `r`.
-/


namespace Submission

open _root_.ZagierHoffmanPositiveChar
set_option autoImplicit false

namespace ZagierHoffmanPositiveChar

open NNReal Polynomial RatFunc

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]





















/--
Statement of Theorem A (Brown's theorem in positive characteristic):

Let `w ∈ ℕ`, where `ℕ := {1,2,...}`. Then every MZV of weight `w` can be written as a `K`-linear
combination of MZV's in the set `𝒯_w`. In particular, `dim 𝒵_w ≤ d(w)`.
Note that `K` in the paper is `RatFunc F`.
-/
theorem theorem_A (w : ℕ+) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≤ d F w :=
  _root_.ZagierHoffmanPositiveChar.theorem_A_amb F w

/--
Statement of Theorem B:

Let `w ∈ ℕ`, where `ℕ := {1,2,...}`. MZVs of weight `w` in `𝒯0 w` are all linearly independent over
`K`. In particular, `dim 𝒵 w ≥ |𝒯0 w|`. Note that `K` in the paper is `RatFunc F`.
-/
theorem theorem_B (w : ℕ+) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≥ Set.ncard (𝒯0 F w) :=
  _root_.ZagierHoffmanPositiveChar.theorem_B_amb (F := F) w

/--
Statement of Theorem D:

Let `w ∈ ℕ+` with `w ≤ 2q − 2`. Then `𝒯 w` is a `K`-basis for `𝒵 w`. In particular,
`dim_K (𝒵 w) = d(w)`. Note that `K` in the paper is `RatFunc F`.

Note: Theorem A establishes that `𝒯 w` spans `𝒵 w`. So to prove `𝒯 w` is a `K`-basis for `𝒵 w`, we
only need to show that `𝒯 w` are linearly independent in `𝒵 w`.
-/
theorem theorem_D (w : ℕ+) (hw : w ≤ 2 * Nat.card F - 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) = d F w := by
  -- The whole theorem is now assembled: `TpBasis.theorem_D_of_TwRowFalse` reduces it to the
  -- *two-term endgame* `TwRowFalse` at the weights `q < w' ≤ 2q-2` (the remaining mathematics,
  -- Dac §6; see `Submission/PLAN.md`).  At `w' ≤ q` the endgame is not used
  -- (`tupleIndP_of_le`), which is why the hypothesis is stated there and not for all `w' ≤ 2q-2.
  have hrow : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwRowFalse F w' := by
    intro w' hqw' hw'2
    by_cases hdvd : (Nat.card F - 1) ∣ w'
    · -- The one weight left by `TwRowFalse_of_not_dvd`: `(q-1) ∣ w'` with `q < w' ≤ 2q-2` forces
      -- `w' = 2q-2`, and that case is `TwRowFalse_of_eq_two_card` (Dac §6's explicit computation).
      have hq3 : 3 ≤ Nat.card F := by omega
      have hw'eq : w' = 2 * Nat.card F - 2 := by
        obtain ⟨m, hm⟩ := hdvd
        have hm2 : 2 ≤ m := by
          by_contra h
          interval_cases m <;> omega
        have h2 : 2 * (Nat.card F - 1) ≤ w' := by
          rw [hm, mul_comm (Nat.card F - 1) m]
          exact Nat.mul_le_mul_right _ hm2
        have h3 : 2 * (Nat.card F - 1) = 2 * Nat.card F - 2 := by omega
        omega
      rw [hw'eq]
      exact ZagierHoffmanPositiveChar.TwRowFalse_of_eq_two_card (F := F) hq3
    · have hq3 : 3 ≤ Nat.card F := by omega
      exact ZagierHoffmanPositiveChar.TwRowFalse_of_not_dvd (F := F) hq3 hqw' hdvd
  exact ZagierHoffmanPositiveChar.theorem_D_of_TwRowFalse (F := F) (w := (w : ℕ)) w.2 hw hrow

end ZagierHoffmanPositiveChar

end Submission
