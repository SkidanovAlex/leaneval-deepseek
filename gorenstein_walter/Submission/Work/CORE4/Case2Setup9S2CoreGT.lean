import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.COAGT.DihedralInvolutionGen
import Submission.Work.CORE4.COAGT.GeneratorLift
import Submission.Work.CORE4.COAGT.ZpowersSqOdd

namespace Work.CORE4

theorem Case2Setup9S2CoreGT (I : Work.GW2.C4Inputs) :
    ∀ {E : Type} [Group E] [Finite E]
      (Z : Subgroup E) [Z.Normal], Z ≤ Subgroup.center E →
      ∀ (Q Y : Subgroup E), Q ≤ Subgroup.normalizer (Y : Set E) →
      IsPGroup 2 Q → Odd (Nat.card Y) →
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (Q ≃* DihedralGroup n)) →
      IsCyclic (Y.map (QuotientGroup.mk' Z)) →
      (∀ q ∈ Q, ∀ y ∈ Y,
        (q * y * q⁻¹) * y⁻¹ ∈ Z ∨ (q * y * q⁻¹) * y ∈ Z) →
      ∃ s ∈ Q, orderOf s = 2 ∧ ((⁅Q, Y⁆ : Subgroup E) : Set E) = Work.GW2.invSet Y s ∧
        (Y ⊓ Subgroup.centralizer ({s} : Set E) =
          Y ⊓ Subgroup.centralizer ((Q : Subgroup E) : Set E)) ∧
        IsCyclic (⁅Q, Y⁆ : Subgroup E) := by sorry

end Work.CORE4
