import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.PiNat.hall_eq_one_of_isPiNat
import Submission.Work.Hall.HallAPI.hall_isHall_relIndex

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A Hall `π`-subgroup is maximal among `π`-subgroups

If `H ≤ K ≤ G` with `G` finite and both `H` and `K` Hall `π`-subgroups of `G`, then `H = K`.

The point is that the relative index `[K : H] = H.relIndex K` is simultaneously a `π`-number and a
`π'`-number:

* it is a `π'`-number because it divides the index `[G : H]` of the Hall subgroup `H` in `G`
  (`Subgroup.relIndex_dvd_index_of_le`),
* it is a `π`-number because `H.relIndex K * |H| = |K|`, so `H.relIndex K` divides the order of the
  `π`-subgroup `K`.

A nonzero integer which is both a `π`-number and a `π'`-number equals `1`
(`Work.Hall.PiNat.hall_eq_one_of_isPiNat`), and `H.relIndex K = 1` together with `H ≤ K` forces
`H = K`.
-/

namespace Work.Hall.HallAPI

open Work.Hall

/-- Tower law for the relative index and the order: if `H ≤ K` are subgroups of a finite group
then `H.relIndex K * |H| = |K|`.  This is `|K|/|H| * |H| = |K|` written multiplicatively, derived
from the tower law for indices `[G : H] = [K : H] * [G : K]` and `[G : X] * |X| = |G|`. -/
theorem relIndex_mul_card_of_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 : H.relIndex K * K.index = H.index := Subgroup.relIndex_mul_index h
  have h2 : H.index * Nat.card H = Nat.card G := H.index_mul_card
  have h3 : K.index * Nat.card K = Nat.card G := K.index_mul_card
  rw [← h1] at h2
  have key : K.index * (H.relIndex K * Nat.card H) = K.index * Nat.card K := by
    rw [← h2.trans h3.symm]; ac_rfl
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K))) key

/-- Two Hall `π`-subgroups of a finite group that are comparable are equal. -/
theorem hall_isHall_eq_of_le {G : Type*} [Group G] [Finite G] {π : ℕ → Prop} {H K : Subgroup G}
    (hH : Work.Hall.IsHall π H) (hK : Work.Hall.IsHall π K) (h : H ≤ K) : H = K := by
  -- `[K : H]` is a `π`-number, because it divides `|K|`.
  have hpi : Work.Hall.IsPiNat π (H.relIndex K) := by
    intro p hp hpd
    obtain ⟨c, hc⟩ := hpd
    exact hK.1 p hp ⟨c * Nat.card H, by rw [← relIndex_mul_card_of_le h, hc, mul_assoc]⟩
  -- `[K : H] ≠ 0`.
  have hne : H.relIndex K ≠ 0 := by
    intro h0
    have : Nat.card K = 0 := by rw [← relIndex_mul_card_of_le h, h0, zero_mul]
    exact (Nat.card_pos (α := K)).ne' this
  -- It is also a `π'`-number, because it divides `[G : H]`.
  have hone : H.relIndex K = 1 :=
    Work.Hall.PiNat.hall_eq_one_of_isPiNat hpi (hall_isHall_relIndex hH h) hne
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp hone)

end Work.Hall.HallAPI
