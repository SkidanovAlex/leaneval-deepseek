import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.CsrSharp.Main
import Submission.Work.Serre.CsrSharp.Cube.cubeIsoRat
import Submission.Work.Serre.CsrSharp.Cell.perCellSharp
import Submission.Work.Serre.CsrSharp.Sigma.sigmaSharp

namespace Work.Serre

theorem cellStepSharp (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ i : ℕ, i < (n + 2) + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q)
      ((n + 2) + φ)).hom :=
  Work.Serre.CsrSharp.cellStepSharpAux
    (Work.Serre.CsrSharp.Cell.perCellSharp Work.Serre.CsrSharp.Cube.cubeIsoRat)
    Work.Serre.CsrSharp.Sigma.sigmaSharp n Y ι f q hq φ hfib h0

end Work.Serre
