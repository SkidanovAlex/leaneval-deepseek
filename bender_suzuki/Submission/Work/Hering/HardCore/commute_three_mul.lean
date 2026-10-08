import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- For two commuting elements `x y`, the product of two blocks of powers adds the
exponents componentwise. -/
lemma commute_two_mul {G : Type*} [Group G] {x y : G} (h : Commute x y)
    (m n k l : ℕ) :
    (x ^ m * y ^ n) * (x ^ k * y ^ l) = x ^ (m + k) * y ^ (n + l) := by
  rw [pow_add, pow_add]
  simp only [mul_assoc]
  rw [mul_left_cancel_iff]
  rw [← mul_assoc, (h.symm.pow_pow n k).eq, mul_assoc]

/-- Middle four: the middle two factors of a product of four can be swapped when they
commute. -/
lemma commute_swap_middle {G : Type*} [Semigroup G] {A B C D : G}
    (h : Commute B C) :
    (A * B) * (C * D) = (A * C) * (B * D) := by
  rw [mul_assoc, ← mul_assoc B C D, h.eq, mul_assoc, ← mul_assoc]

theorem commute_three_mul {G : Type*} [Group G] {a b c : G}
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (p q r s t u : ℕ) :
    (a ^ p * b ^ q * c ^ r) * (a ^ s * b ^ t * c ^ u) =
      a ^ (p + s) * b ^ (q + t) * c ^ (r + u) := by
  have hY : Commute (b ^ q * c ^ r) (a ^ s) :=
    ((hab.pow_right q).mul_right (hac.pow_right r)).pow_left s |>.symm
  calc (a ^ p * b ^ q * c ^ r) * (a ^ s * b ^ t * c ^ u)
      = (a ^ p * (b ^ q * c ^ r)) * (a ^ s * (b ^ t * c ^ u)) := by
        rw [mul_assoc (a ^ p) (b ^ q) (c ^ r),
            mul_assoc (a ^ s) (b ^ t) (c ^ u)]
      _ = (a ^ p * a ^ s) * ((b ^ q * c ^ r) * (b ^ t * c ^ u)) :=
        commute_swap_middle hY
      _ = a ^ (p + s) * (b ^ (q + t) * c ^ (r + u)) := by
        rw [commute_two_mul hbc q r t u, ← pow_add]
      _ = a ^ (p + s) * b ^ (q + t) * c ^ (r + u) := by
        rw [mul_assoc]

end Work.Hering.HardCore
