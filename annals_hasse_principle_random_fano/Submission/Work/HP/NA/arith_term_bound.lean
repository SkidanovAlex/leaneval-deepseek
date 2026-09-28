import Mathlib

namespace Work.HP.NA

theorem arith_term_bound (p r n e : ℕ) (hp : p.Prime) (hn : 2 ≤ n) (he : e ∈ Finset.Ico 1 (r + 1)) :
    ((p ^ e - p ^ (e - 1) : ℕ) : ℝ) * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ)
      ≤ (p : ℝ) ^ (2 * e + (r - e) * (n + 1)) := by
  have hnat : (p ^ e - p ^ (e - 1)) * (p ^ e * p ^ ((r - e) * (n + 1)))
      ≤ p ^ (2 * e + (r - e) * (n + 1)) := by
    calc (p ^ e - p ^ (e - 1)) * (p ^ e * p ^ ((r - e) * (n + 1)))
        ≤ p ^ e * (p ^ e * p ^ ((r - e) * (n + 1))) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = p ^ (2 * e + (r - e) * (n + 1)) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
  exact_mod_cast hnat

end Work.HP.NA
