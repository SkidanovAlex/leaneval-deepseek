import Mathlib

namespace Work.EKLC6Core

/-- Two reals whose quotients by `η > 0` have the same floor differ by less than `η`. -/
theorem abs_sub_lt_of_floor_div_eq {η : ℝ} (hη : 0 < η) {a b : ℝ}
    (h : ⌊a / η⌋ = ⌊b / η⌋) : |a - b| < η := by
  set n : ℤ := ⌊a / η⌋ with hn
  have ha_le : (n : ℝ) * η ≤ a := (le_div_iff₀ hη).mp (Int.floor_le (a / η))
  have ha_lt : a < ((n : ℝ) + 1) * η := (div_lt_iff₀ hη).mp (Int.lt_floor_add_one (a / η))
  have hb_floor : ⌊b / η⌋ = n := h.symm
  have hb_le : (n : ℝ) * η ≤ b :=
    (le_div_iff₀ hη).mp (hb_floor ▸ Int.floor_le (b / η))
  have hb_lt : b < ((n : ℝ) + 1) * η :=
    (div_lt_iff₀ hη).mp (hb_floor ▸ Int.lt_floor_add_one (b / η))
  rw [abs_lt]
  constructor <;> linarith

end Work.EKLC6Core
