import Mathlib

namespace Work.L2F.Props

theorem sign_regular_involution {G : Type*} [Group G] [Fintype G] [DecidableEq G] (u : G)
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1) (m : ℕ) (hcard : Fintype.card G = 2 * m) (hm : Odd m) :
    Equiv.Perm.sign (MulAction.toPermHom G G u) = -1 := by
  -- `toPermHom G G u` is the permutation `x ↦ u * x` of `G`.
  -- Since `u` is an involution, so is this permutation.
  have hsq : (MulAction.toPermHom G G u) ^ 2 = 1 := by
    rw [← map_pow, hu, map_one]
  -- Mathlib's formula for the sign of a permutation with `σ ^ 2 = 1`.
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq]
  -- It has no fixed points because `u ≠ 1`.
  have hcard_fix : Fintype.card (Function.fixedPoints (⇑(MulAction.toPermHom G G u))) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    have hx : (⇑(MulAction.toPermHom G G u)) x.1 = x.1 :=
      (Function.mem_fixedPoints.mp x.2)
    have hx' : u * x.1 = x.1 := by simpa [MulAction.toPermHom_apply] using hx
    exact hu1 (mul_right_cancel (hx'.trans (one_mul x.1).symm))
  rw [hcard_fix, hcard, Nat.sub_zero, Nat.mul_div_cancel_left m (by norm_num)]
  -- `m` is odd, so `(-1) ^ m = -1`.
  exact Odd.neg_one_pow hm

end Work.L2F.Props
