import Mathlib

namespace Work.ORHughesFree.RatU

theorem conj_mul_identity {R : Type*} [Semiring R] (c c' : R) (h : c' * c = 1) (x y : R) :
    c * (x * y) * c' = (c * x * c') * (c * y * c') := by
  rw [← mul_assoc c x y, mul_assoc (c * x) y c', mul_assoc c y c',
      ← mul_assoc (c * x * c') c (y * c'), mul_assoc (c * x) c' c, h, mul_one]

end Work.ORHughesFree.RatU
