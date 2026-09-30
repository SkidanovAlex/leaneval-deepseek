import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

theorem prod_Iic_succ {n : ℕ} (i : Fin n) {M : Type*} [CommMonoid M] (f : Fin (n+1) → M) :
    (∏ j : Fin (n+1), (if j ≤ i.succ then f j else 1))
      = (∏ j : Fin (n+1), (if j ≤ i.castSucc then f j else 1)) * f i.succ := by
  -- Identify the two index sets as `{j | j ≤ i.succ}` and `{j | j ≤ i.castSucc}`.
  have hset : Finset.univ.filter (fun j : Fin (n+1) => j ≤ i.succ)
      = insert i.succ (Finset.univ.filter (fun j : Fin (n+1) => j ≤ i.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h' | h'
      · exact Or.inl h'
      · right
        have h1 : (j : ℕ) < (i : ℕ) + 1 := by
          rw [Fin.lt_def, Fin.val_succ] at h'
          exact h'
        rw [Fin.le_def, Fin.val_castSucc]
        omega
    · rintro (rfl | h)
      · exact le_rfl
      · exact le_trans h (Fin.castSucc_le_succ i)
  have hnotmem : i.succ ∉ Finset.univ.filter (fun j : Fin (n+1) => j ≤ i.castSucc) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le_of_gt (Fin.castSucc_lt_succ (i := i))
  -- Rewrite both `if ... then f j else 1` products as products over the index sets.
  rw [← Finset.prod_filter (p := fun j : Fin (n+1) => j ≤ i.succ) f,
      ← Finset.prod_filter (p := fun j : Fin (n+1) => j ≤ i.castSucc) f]
  -- The larger index set is the smaller one with `i.succ` adjoined.
  rw [hset, Finset.prod_insert hnotmem, mul_comm]

end Work.BW.Minkowski2
