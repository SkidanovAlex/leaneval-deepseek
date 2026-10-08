import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

theorem natCard_ne_one {G : Type*} [Group G] [Finite G] :
    Nat.card {x : G // x ≠ 1} = Nat.card G - 1 := by
  classical
  have hG : Fintype G := Fintype.ofFinite G
  have hne : Fintype {x : G // x ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := G),
    Nat.card_eq_fintype_card (α := {x : G // x ≠ 1}),
    Fintype.card_subtype_compl (fun x : G => x = 1)]
  simp

end Work.ThmF.ChV12
