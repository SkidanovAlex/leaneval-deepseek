import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs

namespace Work.CORE4Qsub

theorem normal_elementaryAbelian_le_z2 :
    ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
      {P E : Subgroup G} (hEP : E ≤ P) (hEn : (E.subgroupOf P).Normal)
      (hPp : IsPGroup p ↥P) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
      (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcard : Nat.card ↥E = p ^ 2),
      E ≤ Work.CORE4.z2 P := by sorry

end Work.CORE4Qsub
