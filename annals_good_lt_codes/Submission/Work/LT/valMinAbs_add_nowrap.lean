import Mathlib

namespace Work.LT

/-- Adding two residues whose absolutely-least representatives are both `< n/4` does not wrap
around: the balanced representative is additive.

Proof: `valMinAbs` is characterised (`ZMod.valMinAbs_spec`) by the two conditions
`x = (y : ZMod n)` and `-n < 2 y ≤ n`, so it suffices to check that
`X + Y` (with `X = a.valMinAbs`, `Y = b.valMinAbs`) satisfies them.  The first is
`ZMod.coe_valMinAbs`; for the second, `|X + Y| ≤ |X| + |Y|` and
`2 (|X| + |Y|) < n` because `4 |X| < n` and `4 |Y| < n`. -/
theorem valMinAbs_add_nowrap {n : ℕ} [NeZero n] (a b : ZMod n)
    (ha : 4 * a.valMinAbs.natAbs < n) (hb : 4 * b.valMinAbs.natAbs < n) :
    (a + b).valMinAbs = a.valMinAbs + b.valMinAbs := by
  set X := a.valMinAbs with hX
  set Y := b.valMinAbs with hY
  have hXY : ((X + Y) * 2).natAbs < n := by
    calc ((X + Y) * 2).natAbs = (X + Y).natAbs * 2 := by rw [Int.natAbs_mul]; norm_num
      _ ≤ (X.natAbs + Y.natAbs) * 2 := Nat.mul_le_mul_right 2 (Int.natAbs_add_le X Y)
      _ < n := by omega
  have hz : |(X + Y) * 2| < (n : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hXY
  refine (ZMod.valMinAbs_spec (a + b) (X + Y)).mpr ⟨?_, ?_⟩
  · rw [Int.cast_add, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  · rw [Set.mem_Ioc]
    obtain ⟨h1, h2⟩ := abs_lt.mp hz
    exact ⟨h1, le_of_lt h2⟩

end Work.LT
