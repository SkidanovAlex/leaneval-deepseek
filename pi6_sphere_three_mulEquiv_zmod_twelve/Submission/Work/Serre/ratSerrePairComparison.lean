import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Serre.Defs
import Submission.Work.Serre.Engine
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.ratPairInputs
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.Serre.cellStepSharp
import Submission.Work.Serre.ratTowerComparison
import Submission.Work.Serre.ratPullbackComparison
import Submission.Work.Serre.ratSerrePairAssembly

namespace Work.Serre

theorem ratSerrePairComparison {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b f : ℕ)
    (hb : 2 ≤ b) (hf : 1 ≤ f) (hE : PathConnectedSpace E) (hB : PathConnectedSpace B)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)) :
    (∀ i : ℕ, i < b + f → Nonempty
      (((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology i) ≅
        ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology i))) ∧
      (CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology (b + f)) →
        CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology (b + f))) :=
  ratSerrePairComparison_of_inputs Work.Serre.cellStepSharp Work.Serre.ratPullbackComparison
    Work.Serre.ratTowerComparison p hp b₀ b f hb hf hE hB hconn hfib0 hfib

end Work.Serre
