import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

/-- **At primes the `1/log`-weighted twisted von Mangoldt summand equals the twisted prime
summand, term by term.** At a prime `p`, `Λ p = log p`, so the factor `(log p)⁻¹ · Λ p` cancels:
`Σ_{p ∈ [N,M] prime} (log p)⁻¹ Λ(p) χ(p) p^{it} = Σ_{p ∈ [N,M] prime} χ(p) p^{it}`. -/
lemma prime_part_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (N M : ℕ) :
    (∑ n ∈ (Finset.Icc N M).filter Nat.Prime,
        ((Real.log n : ℝ) : ℂ)⁻¹ *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t)))
      = ∑ n ∈ (Finset.Icc N M).filter Nat.Prime, χ n * (n : ℂ) ^ (Complex.I * t) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨_, hnp⟩ := Finset.mem_filter.mp hn
  have hlog : ((Real.log n : ℝ) : ℂ) ≠ 0 := by
    have h1 : (1 : ℝ) < n := by exact_mod_cast hnp.one_lt
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos h1))
  rw [ArithmeticFunction.vonMangoldt_apply_prime hnp, mul_assoc,
    inv_mul_cancel_left₀ hlog]

end Work.BMF.pcsw
