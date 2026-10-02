import Mathlib
import Submission.Work.ThomBordism.Grassmann.zeroComplementSum
import Submission.Work.ThomBordism.Grassmann.sumPiecesSetup
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.CohHomotopyEquiv
import Submission.Work.Thom.Gysin
import Submission.Work.Thom.Pair
import Submission.Work.ThomBordism.Grassmann.sumPiecesInter

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

theorem subsingleton_zeroComplementSumPieces
    {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ)
    (hA : Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hA₁ : Subsingleton (Work.Thom.Coh ℤ (m - 1)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hA₂ : Subsingleton (Work.Thom.Coh ℤ (m - 2 * b)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hC : Subsingleton (Work.Thom.Coh ℤ m
      ↥(Work.Thom.zeroComplement (Work.Thom.realification C)))) :
    Subsingleton (Work.Thom.Coh ℤ m ↥(Work.ThomBordism.Grassmann.pieceFst A C)) ∧
      Subsingleton (Work.Thom.Coh ℤ m ↥(Work.ThomBordism.Grassmann.pieceSnd A C)) ∧
      Subsingleton (Work.Thom.Coh ℤ (m - 1)
        ↥(Work.ThomBordism.Grassmann.pieceFst A C ∩
          Work.ThomBordism.Grassmann.pieceSnd A C)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Work.ThomBordism.Grassmann.subsingleton_Coh_pieceFst A C m hA
  · exact Work.ThomBordism.Grassmann.subsingleton_Coh_pieceSnd A C m hC
  · by_cases hb : 1 ≤ b
    · exact Work.ThomBordism.Grassmann.subsingleton_Coh_interPieces A C m hb hA₁ hA₂
    · have hb0 : b = 0 := by omega
      subst hb0
      have hempty : Work.ThomBordism.Grassmann.pieceSnd A C = ∅ := by
        ext p
        refine ⟨fun hp => ?_, fun hp => (Set.notMem_empty p hp).elim⟩
        exact absurd (Subsingleton.elim (sndAB a 0 p.1.2) 0) hp
      have hsub : Work.ThomBordism.Grassmann.pieceFst A C ∩
          Work.ThomBordism.Grassmann.pieceSnd A C = ∅ := by
        rw [hempty, Set.inter_empty]
      haveI : IsEmpty ↥(Work.ThomBordism.Grassmann.pieceFst A C ∩
          Work.ThomBordism.Grassmann.pieceSnd A C) := by
        rw [hsub]
        exact ⟨fun x => x.2⟩
      exact Work.Thom.subsingleton_Coh_of_isEmpty ‹IsEmpty _› (m - 1)

end Work.ThomBordism.Grassmann
