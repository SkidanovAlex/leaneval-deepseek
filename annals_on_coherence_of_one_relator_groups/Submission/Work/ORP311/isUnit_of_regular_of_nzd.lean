import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

/-- In a von Neumann regular ring, an element which is neither a left nor a right zero
divisor is a unit. Indeed `x = x * y * x` gives `x * (y * x - 1) = 0` and
`(x * y - 1) * x = 0`, so `y * x = 1` and `x * y = 1`. -/
theorem isUnit_of_regular_of_nzd {R : Type*} [Ring R] (hreg : Work.ORVonNeumann.VonNeumannRegular R) {x : R} (hl : ∀ y, x * y = 0 → y = 0) (hr : ∀ y, y * x = 0 → y = 0) : IsUnit x := by
  obtain ⟨y, hy⟩ := hreg x
  have hyx : y * x = 1 := by
    have h : x * (y * x - 1) = 0 := by
      have h2 : x * (y * x) = x := by rw [← mul_assoc]; exact hy
      rw [mul_sub, mul_one, h2, sub_self]
    exact sub_eq_zero.mp (hl (y * x - 1) h)
  have hxy : x * y = 1 := by
    have h : (x * y - 1) * x = 0 := by
      rw [sub_mul, one_mul, hy, sub_self]
    exact sub_eq_zero.mp (hr (x * y - 1) h)
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

end Work.ORP311
