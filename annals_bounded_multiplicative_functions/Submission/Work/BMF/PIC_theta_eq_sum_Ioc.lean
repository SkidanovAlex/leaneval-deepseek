import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Nat

namespace Work.BMF

theorem PIC_theta_eq_sum_Ioc (n : ℕ) :
    Chebyshev.theta (2 * (n : ℝ)) - Chebyshev.theta (n : ℝ) =
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) := by
  have hcast : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Chebyshev.theta_eq_sum_primesLE_log (2 * n),
    Chebyshev.theta_eq_sum_primesLE_log n]
  have hset : (2 * n).primesLE =
      n.primesLE ∪ (Finset.Ioc n (2 * n)).filter Nat.Prime := by
    ext p
    rw [Nat.mem_primesLE, Finset.mem_union, Nat.mem_primesLE, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨hp2, hpp⟩
      by_cases h : p ≤ n
      · exact Or.inl ⟨h, hpp⟩
      · exact Or.inr ⟨⟨Nat.lt_of_not_le h, hp2⟩, hpp⟩
    · rintro (⟨h, hpp⟩ | ⟨⟨h1, h2⟩, hpp⟩)
      · exact ⟨le_trans h (by omega), hpp⟩
      · exact ⟨h2, hpp⟩
  have hdisj : Disjoint n.primesLE ((Finset.Ioc n (2 * n)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Nat.mem_primesLE] at hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    omega
  rw [hset, Finset.sum_union hdisj]
  ring

end Work.BMF
