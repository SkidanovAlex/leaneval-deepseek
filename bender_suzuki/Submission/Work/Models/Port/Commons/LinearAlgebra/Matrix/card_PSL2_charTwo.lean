import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.card_SL2_field
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Matrix

namespace Commons.LinearAlgebra.Matrix

theorem card_PSL2_charTwo {F : Type*} [Field F] [Fintype F] [CharP F 2] :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) =
      Fintype.card F * ((Fintype.card F) ^ 2 - 1) := by
  let G := Matrix.SpecialLinearGroup (Fin 2) F
  -- In characteristic two the centre of SL(2,F) is trivial, so PSL(2,F) ≅ SL(2,F).
  have hcenter : Subgroup.center G = ⊥ := center_SL2_eq_bot_of_charTwo (F := F)
  let e1 : G ⧸ Subgroup.center G ≃* G ⧸ (⊥ : Subgroup G) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  let e2 : G ⧸ (⊥ : Subgroup G) ≃* G := QuotientGroup.quotientBot
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* G := by
    dsimp [Matrix.ProjectiveSpecialLinearGroup]
    exact e1.trans e2
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = Nat.card G :=
    Nat.card_congr e.toEquiv
  rw [hcard]
  exact card_SL2_field (F := F)

end Commons.LinearAlgebra.Matrix