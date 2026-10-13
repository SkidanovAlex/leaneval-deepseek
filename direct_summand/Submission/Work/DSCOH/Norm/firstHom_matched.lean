import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.FHMatched.PairAssembly
import Submission.Work.DSCOH.PairingIndex.pairing_index
import Submission.Work.DSCOH.Norm.PairSign.pairingSign

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem firstHom_matched {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [LinearOrder ι] [Fintype ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (TopologicalSpace.Opens X)ᵒᵖ (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) {k : ℕ} (x : Fin (k+2) → ι) :
    (Finset.univ.sum (fun a : Fin (k+2) => Finset.univ.sum (fun b : Fin (k+3) =>
        if b = Fin.castSucc a ∨ b = Work.DSCOH.Norm.pos2A x a then 0
        else Work.DSCOH.Norm.dhTerm P U x a b)))
      + (Finset.univ.sum (fun c : Fin (k+2) => Finset.univ.sum (fun a' : Fin (k+1) =>
          Work.DSCOH.Norm.hdTerm P U x c a'))) = 0 := by
  exact FHMatched.firstHom_matched_of_pairing P U x
    (fun c a' b hb => PairingIndex.pairing_index x c a' b hb)
    (fun c a' b hb => PairSign.pairingSign x c a' b hb)

end Work.DSCOH.Norm
