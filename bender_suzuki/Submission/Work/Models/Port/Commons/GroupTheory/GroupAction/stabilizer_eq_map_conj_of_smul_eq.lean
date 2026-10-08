import Mathlib.GroupTheory.GroupAction.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

theorem stabilizer_eq_map_conj_of_smul_eq {G : Type*} [Group G] {α : Type*} [MulAction G α]
    (g : G) {x y : α} (h : g • x = y) :
    MulAction.stabilizer G y = (MulAction.stabilizer G x).map (MulAut.conj g).toMonoidHom := by
  rw [← h]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g x

end Commons.GroupTheory.GroupAction