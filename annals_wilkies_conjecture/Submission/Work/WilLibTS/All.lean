/-
  `Work.WilLibTS` — a port of the Tarski–Seidenberg (semialgebraic projection) library
  from `openai/math` (`OAI/Analysis/SymmetricDomains/`), Lean v4.34.1 / Mathlib d13f23b7,
  to this workspace's Lean v4.35.0-rc3 / Mathlib 5e0c4e52.

  Modules live under `Submission.Work.WilLibTS.TS.*`; the original module prefix
  `OAI.Analysis.SymmetricDomains.` was renamed to `Submission.Work.WilLibTS.TS.` and the
  top-level namespace `OAI` to `Work.WilLibTS.TS` (the inner `Release061` wrapper dropped,
  declaration names unchanged).

  Headline results:
  * `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite`
    (Tarski–Seidenberg: projection along finitely many real coordinates)
    in `Submission.Work.WilLibTS.TS.PolynomialSignSetProjection2`.
  * the `Work.WilLibTS.TS.SemialgebraicOn` API of `Submission.Work.WilLibTS.TS.Pair`.

  This file just aggregates the ported modules.
-/
import Submission.Work.WilLibTS.TS.Basic
import Submission.Work.WilLibTS.TS.PolynomialIntegralCoordinates
import Submission.Work.WilLibTS.TS.AnalyticImplicitScalar
import Submission.Work.WilLibTS.TS.DifferentiableCauchyTransform
import Submission.Work.WilLibTS.TS.PolynomialRemovableLocal
import Submission.Work.WilLibTS.TS.IntegralPrimitive
import Submission.Work.WilLibTS.TS.FiniteAlgebraGenericSheets
import Submission.Work.WilLibTS.TS.FiniteProperMapOpen
import Submission.Work.WilLibTS.TS.FiberPolynomialNatDegree
import Submission.Work.WilLibTS.TS.ProperEventuallyFiberSubset
import Submission.Work.WilLibTS.TS.FiberCardAmbientSheets
import Submission.Work.WilLibTS.TS.ScalarEquicontinuousHolomorphy
import Submission.Work.WilLibTS.TS.AmbientInverse
import Submission.Work.WilLibTS.TS.ZeroLocusPolynomialSmooth
import Submission.Work.WilLibTS.TS.DiscRelationCompactLocal
import Submission.Work.WilLibTS.TS.DiscCompactness
import Submission.Work.WilLibTS.TS.ContinuityPrinciple
import Submission.Work.WilLibTS.TS.CompactPeakRatio
import Submission.Work.WilLibTS.TS.BoundaryInjective
import Submission.Work.WilLibTS.TS.InterpolateRealUpper
import Submission.Work.WilLibTS.TS.RootEvaluationSurjective
import Submission.Work.WilLibTS.TS.RootMomentCoefficients
import Submission.Work.WilLibTS.TS.SignVariationsPositiveRoots
import Submission.Work.WilLibTS.TS.RootSignPattern
import Submission.Work.WilLibTS.TS.SignatureRootValues
import Submission.Work.WilLibTS.TS.HermiteSignature
import Submission.Work.WilLibTS.TS.TarskiQueryCharpoly
import Submission.Work.WilLibTS.TS.PolynomialEmptyInterior
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite
import Submission.Work.WilLibTS.TS.DecayWeightDeriv
import Submission.Work.WilLibTS.TS.SampleAllChambers
import Submission.Work.WilLibTS.TS.PolynomialSignSetQuery
import Submission.Work.WilLibTS.TS.PolynomialSignSetRoot
import Submission.Work.WilLibTS.TS.PolynomialSignSetSigns
import Submission.Work.WilLibTS.TS.PolynomialSignSetProjection
import Submission.Work.WilLibTS.TS.PolynomialSignSetProjection2
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite2
import Submission.Work.WilLibTS.TS.Pair

-- Additions on top of the port (this area's own API); see `NOTES.md` §3.
import Submission.Work.WilLibTS.TS.SemialgebraicOnAlgebra
import Submission.Work.WilLibTS.TS.ProjectionCorollaries
import Submission.Work.WilLibTS.TS.PolynomialSignSet.polynomialSignSet_iff_finite_sign_description
import Submission.Work.WilLibTS.TS.PolynomialSignSet.forall_finset
import Submission.Work.WilLibTS.TS.PolynomialSignSet.polynomialSignSet_basic
import Submission.Work.WilLibTS.TS.PolynomialSignSet.sign_cell
import Submission.Work.WilLibTS.TS.PolynomialSignSet.prod
import Submission.Work.WilLibTS.TS.PolynomialSignSet.polynomialSignSet_Ioo
import Submission.Work.WilLibTS.TS.PolynomialSignSet.polynomialSignSet_Icc
import Submission.Work.WilLibTS.TS.SemialgebraicOn.finset_sum
import Submission.Work.WilLibTS.TS.SemialgebraicOn.finset_prod
import Submission.Work.WilLibTS.TS.SemialgebraicOn.pi
import Submission.Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_snoc
