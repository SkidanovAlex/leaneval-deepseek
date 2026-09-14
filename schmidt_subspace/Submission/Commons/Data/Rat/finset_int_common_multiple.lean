import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Commons.Data.Rat

open scoped BigOperators

/-- For a finite family of rationals, there is a nonzero natural `D` and integer
values `z i` with `(z i : ℚ) = (D : ℚ) * c i` for every `i` in the set. -/
lemma finset_int_common_multiple {ι : Type*} (s : Finset ι) (c : ι → ℚ) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ i ∈ s, ∃ z : ℤ, (z : ℚ) = (D : ℚ) * c i := by
  classical
  refine ⟨∏ j ∈ s, (c j).den, ?_, ?_⟩
  · have hpos : 0 < ∏ j ∈ s, (c j).den := by
      exact Finset.prod_pos (fun j hj => Rat.den_pos (c j))
    exact ne_of_gt hpos
  · intro i hi
    have hnum : c i * ((c i).den : ℚ) = ((c i).num : ℚ) := Rat.mul_den_eq_num (c i)
    have hD : ((∏ j ∈ s, (c j).den : ℕ) : ℚ) =
        ((c i).den : ℚ) * (∏ j ∈ s.erase i, ((c j).den : ℚ)) := by
      rw [Nat.cast_prod]
      exact (Finset.mul_prod_erase s (fun x : ι => ((c x).den : ℚ)) hi).symm
    refine ⟨(c i).num * ((∏ j ∈ s.erase i, (c j).den : ℕ) : ℤ), ?_⟩
    calc
      (((c i).num * ((∏ j ∈ s.erase i, (c j).den : ℕ) : ℤ) : ℤ) : ℚ)
          = ((c i).num : ℚ) * (∏ j ∈ s.erase i, ((c j).den : ℚ)) := by
              simp [Nat.cast_prod]
      _ = (((∏ j ∈ s, (c j).den : ℕ) : ℕ) : ℚ) * c i := by
              symm
              calc
                (((∏ j ∈ s, (c j).den : ℕ) : ℕ) : ℚ) * c i
                    = ((c i).den : ℚ) * (∏ j ∈ s.erase i, ((c j).den : ℚ)) * c i := by
                        rw [hD]
                _ = (∏ j ∈ s.erase i, ((c j).den : ℚ)) * (c i * ((c i).den : ℚ)) := by ring
                _ = (∏ j ∈ s.erase i, ((c j).den : ℚ)) * ((c i).num : ℚ) := by rw [hnum]
                _ = ((c i).num : ℚ) * (∏ j ∈ s.erase i, ((c j).den : ℚ)) := by ring

end Commons.Data.Rat