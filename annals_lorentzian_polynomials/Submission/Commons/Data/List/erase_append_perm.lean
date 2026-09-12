import Mathlib

namespace Commons.Data.List

set_option autoImplicit false

/-- Removing one occurrence of `a` from a nodup list and appending it back is a
permutation of the original list. -/
lemma erase_append_perm {α : Type*} [DecidableEq α] (l : List α) (a : α)
    (hm : a ∈ l) (hl : l.Nodup) : (l.erase a ++ [a]).Perm l := by
  -- (l.erase a ++ [a]) ~ a :: l.erase a  (rotate last element to front)
  -- l ~ a :: l.erase a  (erase an occurrence of `a` from `l`)
  exact (List.perm_append_singleton a (l.erase a)).trans (List.perm_cons_erase hm).symm

end Commons.Data.List
