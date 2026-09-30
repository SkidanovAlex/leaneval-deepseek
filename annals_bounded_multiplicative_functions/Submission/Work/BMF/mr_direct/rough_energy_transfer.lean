import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.coprime_primesIn_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-!
# Rough energy transfer

For a coefficient sequence `a` supported on integers having no prime factor in `[P,Q]`,
the weighted energy `Σ_{n ∈ [X₁,X₂]} ‖a n‖² / n²` is bounded by `(1/X₁)` times the
unweighted (first-power) energy over the same range restricted to integers coprime to
the product of the primes in `[P,Q]`.  Both the support hypothesis and the coprimality
condition refer to the same set of primes, so the two sides see the same nonzero terms;
the factor `1/X₁` is the trivial bound `1/n ≤ 1/X₁`.
-/

/-- Rough energy transfer: see the module docstring.  If `a` vanishes on every integer
divisible by a prime in `[P,Q]`, then the `1/n²`-weighted energy over `[X₁,X₂]` is at most
`1/X₁` times the `1/n`-weighted energy over the integers of that range coprime to the
product of the primes in `[P,Q]`. -/
theorem rough_energy_transfer (a : ℕ → ℂ) (X₁ X₂ P Q : ℝ) (hX1 : 1 ≤ X₁)
    (hsupp : ∀ n : ℕ, (∃ p : ℕ, Nat.Prime p ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n) →
      a n = 0) :
    (∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (1 / X₁) * ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
          (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), ‖a n‖ ^ 2 / (n : ℝ) := by
  classical
  set S := Work.BMF.natIcc X₁ X₂ with hS
  set g := ∏ p ∈ Work.BMF.primesIn P Q, p with hg
  have hX1pos : (0 : ℝ) < X₁ := lt_of_lt_of_le one_pos hX1
  -- every `n ∈ [X₁,X₂]` satisfies `X₁ ≤ n`
  have hmem : ∀ n ∈ S, X₁ ≤ (n : ℝ) := by
    intro n hn
    rw [hS] at hn
    simp only [Work.BMF.natIcc, Finset.mem_Icc] at hn
    exact Nat.ceil_le.mp hn.1
  -- `a` vanishes on the non-coprime part of the range
  have hzero : ∀ n ∈ S, ¬ n.Coprime g → a n = 0 := by
    intro n _ hnc
    rw [hg] at hnc
    rw [coprime_primesIn_iff n P Q] at hnc
    push Not at hnc
    obtain ⟨p, hp, hP, hQ, hdvd⟩ := hnc
    exact hsupp n ⟨p, hp, hP, hQ, hdvd⟩
  -- pointwise comparison against `1/X₁` times the unweighted term (zero off the coprime set)
  have hpoint : ∀ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (1 / X₁) * (if n.Coprime g then ‖a n‖ ^ 2 / (n : ℝ) else 0) := by
    intro n hn
    by_cases hc : n.Coprime g
    · rw [ite_eq_left hc]
      have hnX : X₁ ≤ (n : ℝ) := hmem n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hX1pos hnX
      have hb : (0 : ℝ) ≤ ‖a n‖ ^ 2 := by positivity
      have hXn : X₁ * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hXnp : (0 : ℝ) < X₁ * (n : ℝ) := mul_pos hX1pos hnpos
      have h1 : ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ ‖a n‖ ^ 2 / (X₁ * (n : ℝ)) :=
        div_le_div_of_nonneg_left hb hXnp hXn
      have h2 : ‖a n‖ ^ 2 / (X₁ * (n : ℝ)) = (1 / X₁) * (‖a n‖ ^ 2 / (n : ℝ)) := by
        field_simp
      linarith [h1, h2]
    · rw [ite_eq_right hc]
      have hz : a n = 0 := hzero n hn hc
      rw [hz]
      simp
  calc ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ S, (1 / X₁) * (if n.Coprime g then ‖a n‖ ^ 2 / (n : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
    _ = (1 / X₁) * ∑ n ∈ S, (if n.Coprime g then ‖a n‖ ^ 2 / (n : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ = (1 / X₁) * ∑ n ∈ S.filter (fun n => n.Coprime g), ‖a n‖ ^ 2 / (n : ℝ) := by
        rw [Finset.sum_filter]

end Work.BMF.mr_direct
