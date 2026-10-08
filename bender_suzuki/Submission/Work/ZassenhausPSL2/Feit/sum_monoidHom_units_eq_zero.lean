import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.sum_monoidHom_units_eq_zero`

A generic character-theoretic fact, used by the Feit-count leaves of the area
`ZassenhausPSL2` (`cfInner_indFun_linear_self_notreal` and its siblings): the sum of a
**non-trivial** homomorphism `ψ : K →* ℂˣ` over a finite group `K` vanishes,

`∑_{k ∈ K} (ψ k : ℂ) = 0`.

These are exactly the one-dimensional (linear) complex characters of `K`; the result is the
`⟨ψ, 1_K⟩ = 0` half of the first orthogonality relation, in the elementary form in which it is
needed (one multiplication by `ψ k₀ ≠ 1` permutes the summation index).

Mathlib has the additive version `AddChar.sum_eq_zero_of_ne_one`, but no `ℂˣ`-valued
(monoid homomorphism) counterpart; this file fills that gap in the workspace's own terms.
-/

namespace Work.ZassenhausPSL2.Feit

/-- The sum of a non-trivial homomorphism `ψ : K →* ℂˣ` over a finite group vanishes:
choose `k₀` with `ψ k₀ ≠ 1`; since `k ↦ k₀ * k` is a bijection of `K`,
`(ψ k₀ : ℂ) * ∑_k (ψ k : ℂ) = ∑_k (ψ (k₀ * k) : ℂ) = ∑_k (ψ k : ℂ)`, so
`((ψ k₀ : ℂ) - 1) * ∑_k (ψ k : ℂ) = 0`, and the second factor is a unit of the field `ℂ`. -/
theorem sum_monoidHom_units_eq_zero {K : Type} [Group K] [Fintype K] (ψ : K →* ℂˣ)
    (h : ψ ≠ 1) : (∑ k : K, (ψ k : ℂ)) = 0 := by
  obtain ⟨k₀, hk₀⟩ : ∃ k, ψ k ≠ 1 := by
    by_contra hc
    push Not at hc
    exact h (MonoidHom.ext fun k => hc k)
  have hstep : (ψ k₀ : ℂ) * (∑ k : K, (ψ k : ℂ)) = ∑ k : K, (ψ k : ℂ) := by
    rw [Finset.mul_sum]
    rw [show (∑ k : K, (ψ k₀ : ℂ) * (ψ k : ℂ)) = ∑ k : K, (ψ (k₀ * k) : ℂ) from
      Finset.sum_congr rfl fun k _ => by rw [← Units.val_mul, map_mul]]
    exact Fintype.sum_equiv (Equiv.mulLeft k₀) (fun k => (ψ (k₀ * k) : ℂ))
      (fun k => (ψ k : ℂ)) (fun x => rfl)
  have hz : ((ψ k₀ : ℂ) - 1) * (∑ k : K, (ψ k : ℂ)) = 0 := by
    rw [sub_mul, one_mul, hstep, sub_self]
  rcases mul_eq_zero.mp hz with h1 | h1
  · exfalso
    rw [sub_eq_zero] at h1
    exact hk₀ (Units.ext h1)
  · exact h1

end Work.ZassenhausPSL2.Feit
