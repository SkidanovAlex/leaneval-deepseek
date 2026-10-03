import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

/-- If `a ∣ b`, `‖a‖ = ‖b‖` and `b ≠ 0` then `a ~ b`. -/
theorem associated_of_dvd_of_normNatAbs_eq {a b : GaussianInt} (h : a ∣ b)
    (hna : a.norm.natAbs = b.norm.natAbs) (hb : b ≠ 0) : Associated a b := by
  obtain ⟨c, hc⟩ := h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc
    exact hb hc
  have hna_pos : 0 < a.norm.natAbs := by
    have : a.norm.natAbs ≠ 0 := fun h0 =>
      ha0 (GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp h0))
    omega
  have hnc : c.norm.natAbs = 1 := by
    have h1 : a.norm.natAbs = a.norm.natAbs * c.norm.natAbs := by
      have h' : b.norm.natAbs = a.norm.natAbs * c.norm.natAbs := by
        rw [hc, Zsqrtd.norm_mul, Int.natAbs_mul]
      exact hna.trans h'
    exact Nat.mul_left_cancel hna_pos (by rw [mul_one]; exact h1.symm)
  have hcu : IsUnit c := Zsqrtd.norm_eq_one_iff.mp hnc
  exact ⟨hcu.unit, by rw [hc, hcu.unit_spec]⟩

end Commons.NumberTheory.GaussianInt