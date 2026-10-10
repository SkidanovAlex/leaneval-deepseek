import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `haveI := hR` below is used to turn the `Subsingleton R`/`Nontrivial R` hypotheses into
-- instances; the style linter misreads this as a `have`.
set_option linter.style.haveILetI false

namespace Work.MotV5.Nodes.UEPR

open Polynomial

/-- An element of `R` which is integral over a subring `O` all of whose elements have
valuation at most `1` has valuation at most `1`: the valuation ring `{y | v y ≤ 1}` is
integrally closed in `R`, and `O` is contained in it. -/
theorem valuation_le_one_of_isIntegral {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (O : Subring R) (hO : ∀ x : O, v (x : R) ≤ 1) {x : R} (hx : IsIntegral O x) : v x ≤ 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := hR
    have hx0 : x = 0 := Subsingleton.elim x 0
    rw [hx0, v.map_zero]
    exact zero_le_one
  · haveI := hR
    obtain ⟨f, hm, hf⟩ := hx
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      have hc : algebraMap O R c = 0 := by simpa using hf
      have hc1 : c = 1 := by
        have := hm.coeff_natDegree
        simpa using this
      have h1 : (1 : R) = 0 := by
        rw [← map_one (algebraMap O R), ← hc1]
        exact hc
      exact absurd h1 one_ne_zero
    · -- `f` is monic of degree `n = f.natDegree ≥ 1` and `x` is a root
      simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree,
        map_one, one_mul, add_eq_zero_iff_eq_neg] at hf
      apply_fun v at hf
      simp only [Valuation.map_neg, Valuation.map_pow] at hf
      contrapose! hf
      -- if `1 < v x` then the leading term `x ^ n` strictly dominates the sum
      refine ne_of_lt (v.map_sum_lt ?_ ?_)
      · exact pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hf))
      · intro i hi
        simp only [Finset.mem_range, Valuation.map_mul, Valuation.map_pow] at hi ⊢
        exact mul_lt_of_le_one_of_lt (hO (f.coeff i)) (pow_lt_pow_right₀ hf hi)

end Work.MotV5.Nodes.UEPR
