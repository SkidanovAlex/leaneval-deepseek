import Mathlib

namespace Work.KronP

theorem twoListCost (Kp Kr Kc Ks A B : ℕ) :
    Kp * 2 + (Kr * 3 * (A + B + 2) + (Kc + (Ks * (A + B + 3) + Kc)))
      ≤ (2 * Kp + 3 * Kr + Ks + 2 * Kc) * (A + B + 3) := by
  nlinarith

end Work.KronP
