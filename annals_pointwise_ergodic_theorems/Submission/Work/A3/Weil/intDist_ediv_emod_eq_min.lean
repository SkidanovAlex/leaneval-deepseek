import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# The distance to the nearest integer of a rational `z/q`, via `z % q`

`Submission.VanDerCorput.intDist α = min (Int.fract α) (1 - Int.fract α)` is the distance
from `α` to the nearest integer.  For `α = z / q` with `q ≥ 1` an integer, this distance is
`min r (q - r) / q` where `r = z % q` is the Euclidean remainder of `z` modulo `q`.

The point is that `Int.fract (z/q) = (z % q)/q`: writing `z = (z/q)*q + (z%q)`, the integer
part `z/q` drops out under `Int.fract`, and `0 ≤ (z%q)/q < 1` so `Int.fract` is the identity
there.  This is the arithmetic input that converts the Euclidean remainder produced by the
divisor-counting arguments into the real quantity `intDist` used by the Weyl/van der Corput
estimates.
-/

namespace Work.A3.Weil

theorem intDist_ediv_emod_eq_min {q : ℤ} (hq : 1 ≤ q) (z : ℤ) :
    Submission.VanDerCorput.intDist ((z : ℝ) / (q : ℝ))
      = ((min (z % q) (q - z % q) : ℤ) : ℝ) / (q : ℝ) := by
  rw [Submission.VanDerCorput.intDist]
  have hq0 : q ≠ 0 := by omega
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < q)
  have hqRne : (q : ℝ) ≠ 0 := ne_of_gt hqRpos
  -- `r = z % q`, the Euclidean remainder, lies in `[0, q)`.
  set r : ℤ := z % q with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg z hq0
  have hrlt : r < q := by rw [hr]; exact Int.emod_lt_of_pos z (by omega)
  -- Division algorithm: `z = (z / q) * q + r`.
  have hzR : (z : ℝ) = ((z / q : ℤ) : ℝ) * (q : ℝ) + (r : ℝ) := by
    have h := Int.ediv_mul_add_emod z q
    have h' : ((z / q * q + z % q : ℤ) : ℝ) = (z : ℝ) := by rw [h]
    push_cast at h'
    rw [← hr] at h'
    linarith
  have hsplit : (z : ℝ) / (q : ℝ) = ((z / q : ℤ) : ℝ) + (r : ℝ) / (q : ℝ) := by
    rw [hzR, add_div, mul_div_cancel_right₀ _ hqRne]
  -- The integer part drops out of `Int.fract`, and `r/q ∈ [0,1)`.
  have hfract : Int.fract ((z : ℝ) / (q : ℝ)) = (r : ℝ) / (q : ℝ) := by
    rw [hsplit, Int.fract_intCast_add]
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg (by exact_mod_cast hr0) hqRpos.le,
      by rw [div_lt_one hqRpos]; exact_mod_cast hrlt⟩
  rw [hfract]
  have hone : 1 - (r : ℝ) / (q : ℝ) = ((q - r : ℤ) : ℝ) / (q : ℝ) := by
    rw [Int.cast_sub, sub_div, div_self hqRne]
  rw [hone, min_div_div_right hqRpos.le]
  congr 1
  rw [Int.cast_min, Int.cast_sub]

end Work.A3.Weil
