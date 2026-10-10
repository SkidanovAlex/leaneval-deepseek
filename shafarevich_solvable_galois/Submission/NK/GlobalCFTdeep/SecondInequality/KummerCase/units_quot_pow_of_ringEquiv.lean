import Mathlib.Algebra.Field.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.SetTheory.Cardinal.Finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- A ring equivalence of fields induces an isomorphism of the quotients of the
unit groups by the subgroup of `n`-th powers. -/
theorem units_quot_pow_of_ringEquiv {R S : Type*} [Field R] [Field S] (e : R ≃+* S) (n : ℕ) :
    Nat.card (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) =
      Nat.card (Sˣ ⧸ (powMonoidHom n : Sˣ →* Sˣ).range) := by
  let F : Rˣ ≃* Sˣ := Units.mapEquiv e.toMulEquiv
  have h : Subgroup.map (F : Rˣ →* Sˣ) (powMonoidHom n : Rˣ →* Rˣ).range =
      (powMonoidHom n : Sˣ →* Sˣ).range := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, ⟨z, hz⟩, hy⟩
      refine ⟨F z, ?_⟩
      rw [← hy, ← hz]
      simp
    · rintro ⟨z, hz⟩
      refine ⟨F.symm x, ⟨F.symm z, ?_⟩, by simp⟩
      rw [← hz]
      simp
  exact Nat.card_congr (QuotientGroup.congr _ _ F h).toEquiv

end NK.GlobalCFTdeep.SecondInequality.KummerCase
