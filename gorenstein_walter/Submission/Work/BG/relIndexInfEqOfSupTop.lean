import Mathlib

namespace Work.BG

/-- **Relative-index form of the second isomorphism theorem.** If `P` is normal in the finite group `X` and `P ⊔ Y = ⊤`, then `[X : Y] = [P : P ⊓ Y]`, i.e. `Y.index = (Y ⊓ P).relIndex P`. -/
theorem relIndexInfEqOfSupTop {X : Type*} [Group X] [Finite X] (P Y : Subgroup X)
    (hP : P.Normal) (hPY : P ⊔ Y = ⊤) : Y.index = (Y ⊓ P).relIndex P := by
  -- Multiplying the relative index by the index of `P` recovers the index of `P ⊓ Y`.
  have h1 : (Y ⊓ P).relIndex P * P.index = (Y ⊓ P).index :=
    Subgroup.relIndex_mul_index inf_le_right
  -- Since `P ⊔ Y = ⊤`, the relative index of `P` in `Y` is the full index of `P`.
  have hpre : P.relIndex Y = P.index := by
    rw [← Subgroup.relIndex_sup_right Y P,
        show Y ⊔ P = ⊤ by rw [sup_comm]; exact hPY,
        Subgroup.relIndex_top_right]
  -- Hence `[X : P ⊓ Y] = [X : Y] * [X : P]`.
  have h2 : (Y ⊓ P).index = Y.index * P.index := by
    rw [inf_comm, Subgroup.index_inf, hpre, mul_comm]
  have hne : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h2] at h1
  exact (Nat.mul_right_cancel_iff (Nat.pos_iff_ne_zero.mpr hne)).mp h1.symm

end Work.BG
