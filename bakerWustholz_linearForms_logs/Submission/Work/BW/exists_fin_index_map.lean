import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem exists_fin_index_map {α : Type*} (s : Multiset α) (N : ℕ) (h : s.card = N) :
    ∃ z : Fin N → α, (Finset.univ.val.map z : Multiset α) = s := by
  have hl : s.toList.length = N := by rw [Multiset.length_toList, h]
  refine ⟨fun i => s.toList.get (Fin.cast hl.symm i), ?_⟩
  have hofn : List.ofFn (fun i : Fin N => s.toList.get (Fin.cast hl.symm i)) = s.toList := by
    rw [← List.ofFn_congr hl (List.get s.toList), List.ofFn_get]
  rw [Finset.val_univ_fin, Multiset.map_coe, ← List.ofFn_eq_map, hofn, Multiset.coe_toList]

end Work.BW
