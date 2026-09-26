import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs

namespace Work.Rigidity.SigmaEntryBound

/-!
# The nearest-integer remainder of `rnd`

This file proves `Work.Rigidity.SigmaEntryBound.rnd_spec`, the two numerical estimates
satisfied by the "nearest integer" rounding `rnd a c` of `a / c` (for `c ≠ 0`):

* `2 * |a - (rnd a c) * c| ≤ |c|`  — the remainder is at most half the divisor,
* `2 * |rnd a c| * |c| ≤ 2 * |a| + |c|` — the quotient is controlled by `a`.

Both are proved from the elementary Euclidean-division description of `rnd`: for `0 < c`
one has `rnd a c = (2a+c) / (2c)` and for `c < 0` one has `rnd a c = (-(2a+c)) / (-(2c))`,
while the second estimate is a formal consequence of the first via the triangle inequality.
-/

/-- For `0 < c`, writing `q = (2 * a + c) / (2 * c)`, the remainder `a - q * c` is at most
`c / 2` in absolute value. -/
lemma rnd_pos_core (a c : ℤ) (hc : 0 < c) :
    2 * (a - ((2 * a + c) / (2 * c)) * c).natAbs ≤ c.natAbs := by
  have hd : (0 : ℤ) < 2 * c := by omega
  set q : ℤ := (2 * a + c) / (2 * c) with hq
  set s : ℤ := (2 * a + c) % (2 * c) with hs
  have hdecomp0 : 2 * a + c = q * (2 * c) + s := by
    rw [hq, hs]
    exact (Int.ediv_mul_add_emod (2 * a + c) (2 * c)).symm
  have hdecomp : 2 * a + c = (q * c) * 2 + s := by rw [hdecomp0]; ring
  have hnn : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg _ (by omega)
  have hlt : s < 2 * c := by rw [hs]; exact Int.emod_lt_of_pos _ hd
  omega

/-- For `c < 0`, writing `q = (-(2 * a + c)) / (-(2 * c))`, the remainder `a - q * c` is at
most `|c| / 2` in absolute value. -/
lemma rnd_neg_core (a c : ℤ) (hc : c < 0) :
    2 * (a - ((-(2 * a + c)) / (-(2 * c))) * c).natAbs ≤ c.natAbs := by
  have hd : (0 : ℤ) < -(2 * c) := by omega
  set q : ℤ := (-(2 * a + c)) / (-(2 * c)) with hq
  set s : ℤ := (-(2 * a + c)) % (-(2 * c)) with hs
  have hdecomp0 : -(2 * a + c) = q * (-(2 * c)) + s := by
    rw [hq, hs]
    exact (Int.ediv_mul_add_emod (-(2 * a + c)) (-(2 * c))).symm
  have hdecomp : -(2 * a + c) = (q * c) * (-2) + s := by rw [hdecomp0]; ring
  have hnn : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg _ (by omega)
  have hlt : s < -(2 * c) := by rw [hs]; exact Int.emod_lt_of_pos _ hd
  omega

/-- The second estimate of `rnd_spec` follows from the first: since `a = (rnd a c) * c + r`
with `2 * |r| ≤ |c|`, the triangle inequality bounds `|rnd a c| * |c|` by `|a| + |r|`,
and hence `2 * |rnd a c| * |c|` by `2 * |a| + |c|`. -/
lemma rnd_second_bound (a c : ℤ)
    (h1 : 2 * (a - rnd a c * c).natAbs ≤ c.natAbs) :
    2 * (rnd a c).natAbs * c.natAbs ≤ 2 * a.natAbs + c.natAbs := by
  have key : (rnd a c * c).natAbs = (rnd a c).natAbs * c.natAbs := Int.natAbs_mul _ _
  have hle : (rnd a c * c).natAbs ≤ a.natAbs + (a - rnd a c * c).natAbs := by
    have he : rnd a c * c = a - (a - rnd a c * c) := by ring
    conv_lhs => rw [he]
    exact Int.natAbs_sub_le a _
  calc 2 * (rnd a c).natAbs * c.natAbs = 2 * (rnd a c * c).natAbs := by rw [key]; ring
    _ ≤ 2 * (a.natAbs + (a - rnd a c * c).natAbs) := by omega
    _ = 2 * a.natAbs + 2 * (a - rnd a c * c).natAbs := by ring
    _ ≤ 2 * a.natAbs + c.natAbs := by omega

/-- The nearest integer to `a / c` leaves a remainder of at most half the divisor, and the
corresponding quotient is bounded by `(2 |a| + |c|) / (2 |c|)`. -/
theorem rnd_spec (a c : ℤ) (hc : c ≠ 0) :
    2 * (a - rnd a c * c).natAbs ≤ c.natAbs ∧
    2 * (rnd a c).natAbs * c.natAbs ≤ 2 * a.natAbs + c.natAbs := by
  have h1 : 2 * (a - rnd a c * c).natAbs ≤ c.natAbs := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [rnd, if_neg (by omega)]
      exact rnd_neg_core a c h
    · rw [rnd, if_pos h]
      exact rnd_pos_core a c h
  exact ⟨h1, rnd_second_bound a c h1⟩

end Work.Rigidity.SigmaEntryBound
