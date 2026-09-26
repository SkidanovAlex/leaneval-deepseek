import Mathlib
import Submission.Work.Drive.genericFullDefs
import Submission.TrisecantCurve
import Submission.StripCrosscut

/-!
# Vocabulary for the finite-meridian-fibre lemma

This module fixes the definitions used by `Work.Drive.finiteMeridianFibre_of_tangentChordGP`
and by the helpers it delegates:

* `Work.Drive.TrisecantZeroSet` — the set of *real* off-diagonal collinear triples (the zero set
  of the collinearity map `Φ`, restricted to triples with pairwise distinct knot points);
* `Work.Drive.AnalyticTrisecantLocalCurve` / `AnalyticLocalSmoothCurveTheorem` — the
  analytic (`C^ω`) analogue of `LeanEval.KnotTheory.Quadrisecant.TrisecantLocalCurve` /
  `LocalSmoothCurveTheorem` (`Submission/TrisecantCurve.lean`, with `C¹` regularity): near every
  general-position collinear off-diagonal triple the zero set of `Φ` is an injectively
  parametrised *analytic* curve.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology

/-- **The collinearity-zero locus of real off-diagonal triples.**  The set of real parameter
triples whose three knot points are pairwise distinct and collinear. -/
def TrisecantZeroSet (r : ℝ → Space) : Set RealParamTriple :=
  {q | collinearityMap r q = 0 ∧ q ∈ RealOffDiagonalTriples r}

/-- **The local shape of the collinearity zero set at a general-position triple, analytic
form.**  The analogue of `LeanEval.KnotTheory.Quadrisecant.TrisecantLocalCurve`
(`Submission/TrisecantCurve.lean`) with the regularity of the parametrising curve raised from
`C¹` to `⊤` (= analytic, `C^ω`), and with the additional datum of a *continuous local inverse*
of the parametrisation: a continuous `τ` on the chart neighbourhood `U` with `τ (γ t) = t`.
(`τ` is the coordinate that the implicit function theorem solves in, and it is what makes the
chart a genuine local homeomorphism, so that points of the zero set near `γ 0` have parameters
near `0`.) -/
def AnalyticTrisecantLocalCurve (r : ℝ → Space) (p : RealParamTriple) : Prop :=
  collinearityMap r p = 0 ∧ p ∈ RealOffDiagonalTriples r ∧
    ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∃ lo hi : ℝ, lo < 0 ∧ 0 < hi ∧ ∃ γ : ℝ → RealParamTriple,
        ContDiffOn ℝ ⊤ γ (Set.Ioo lo hi) ∧ Set.InjOn γ (Set.Ioo lo hi) ∧
          γ 0 = p ∧
          (∀ t ∈ Set.Ioo lo hi,
            γ t ∈ U ∧ collinearityMap r (γ t) = 0 ∧ γ t ∈ RealOffDiagonalTriples r) ∧
          (∀ q ∈ U, collinearityMap r q = 0 → q ∈ RealOffDiagonalTriples r →
            ∃ t ∈ Set.Ioo lo hi, γ t = q) ∧
          ∃ τ : RealParamTriple → ℝ, ContinuousOn τ U ∧ ∀ t ∈ Set.Ioo lo hi, τ (γ t) = t

/-- **The analytic local-curve theorem (target of the port of `Submission/LocalCurve.lean`).**
At every general-position collinear off-diagonal triple of a smooth knot, the off-diagonal zero
set of the collinearity map is locally an injectively parametrised analytic curve through the
triple. -/
def AnalyticLocalSmoothCurveTheorem (r : ℝ → Space) : Prop :=
  ∀ (a b m : ℝ), TrisecantGeneralPosition r a b m → collinearityValue r a b m = 0 →
    AnalyticTrisecantLocalCurve r (a, (b, m))

end Work.Drive

end
