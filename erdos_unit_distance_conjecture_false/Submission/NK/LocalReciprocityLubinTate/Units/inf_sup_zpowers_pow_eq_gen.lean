import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools

namespace NK.LocalReciprocityLubinTate.Units

theorem inf_sup_zpowers_pow_eq_gen (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : Fˣ) (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (π : F))
    (k n : ℕ) (hk : 1 ≤ k) :
    (Subgroup.zpowers (π ^ k) ⊔ NK.LocalReciprocityLubinTate.higherUnits F 0)
        ⊓ (Subgroup.zpowers π ⊔ NK.LocalReciprocityLubinTate.higherUnits F (n + 1))
      = Subgroup.zpowers (π ^ k) ⊔
          NK.LocalReciprocityLubinTate.higherUnits F (n + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact NK.LocalReciprocityLubinTate.Unramified.inf_sup_zpowers_pow_eq F π hπ m n

end NK.LocalReciprocityLubinTate.Units
