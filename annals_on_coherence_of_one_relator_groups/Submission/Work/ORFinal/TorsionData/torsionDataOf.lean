import Mathlib
import Submission.Work.ORLinnell.Linnell
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn
import Submission.Work.ORFinal.TorsionData.Defs
import Submission.Work.ORFinal.TorsionData.LaurentDatum

namespace Work.ORFinal.TorsionData

theorem torsionDataOf (K : Type*) [Field K] [CharZero K] (G : Type*) [Group G] (U : Type*) [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex] (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (u : G) (hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure {u})) :
    Nonempty (Work.ORTorsion.TorsionData K G U) := by
  classical
  refine ⟨⟨L.gen, Dsub L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u, hq, ?_⟩⟩
  · intro H h
    exact L.gen_mem H h
  · intro H₁ H₂ h
    exact Dsub_mono L h
  · intro H
    exact L.isDivisionClosed H
  · intro H A hA hclosed
    exact L.minimal H A.toSubring (fun h => hA h) (fun k => A.algebraMap_mem k) hclosed
  · intro H n g hg a ha hsum i
    exact L.independence H n g hg a ha hsum i
  · intro g H x hx
    exact L.conjugation g H x hx
  · intro H
    exact Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn K G U L G'
      (inferInstance : G'.Normal) (inferInstance : G'.FiniteIndex)
      (fun x hx => hdiv G' hG'tf x hx) H
  · intro H φ hφ
    exact laurentBaseOf L G' hG'tf hdiv H φ hφ

end Work.ORFinal.TorsionData
