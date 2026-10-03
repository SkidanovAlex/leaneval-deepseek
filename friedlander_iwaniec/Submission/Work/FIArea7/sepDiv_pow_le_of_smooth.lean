import Mathlib
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sepDiv_pow_le

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

theorem sepDiv_pow_le_of_smooth (r k N : ℕ) (p : Fin k → ℕ) (hk : 0 < k) (hr : 2 ≤ r)
    (hmono : StrictAnti p) (hprime : ∀ i, (p i).Prime)
    (hl : (∏ i, p i) ≤ N) (hz : (p ⟨0, hk⟩) ^ (r * r) ≤ N) :
    (∏ i ∈ dIdx r k, p i) ^ r ≤ N ^ 2 := by
  have h1 := sepDiv_pow_le r k p hk hr hmono hprime
  have hp0 : 1 ≤ p ⟨0, hk⟩ := (hprime _).one_le
  have hle : r * (r - 1) ≤ r * r := Nat.mul_le_mul_left r (Nat.sub_le r 1)
  have hz' : p ⟨0, hk⟩ ^ (r * (r - 1)) ≤ N :=
    le_trans (Nat.pow_le_pow_right hp0 hle) hz
  calc (∏ i ∈ dIdx r k, p i) ^ r
      ≤ (∏ i, p i) * p ⟨0, hk⟩ ^ (r * (r - 1)) := h1
    _ ≤ N * N := Nat.mul_le_mul hl hz'
    _ = N ^ 2 := by ring

end Work.FIArea7
