import Mathlib
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.FFResidual.Eisenstein.isDomain_adjoinRoot_of_isEisensteinAt

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier order `R[X] / (X ^ 5 + π X ^ 4 - π)` is a domain

The defining polynomial of `FunctionFieldPlace.AsOrder P` is monic of degree `5`, and it is
*Eisenstein* at the maximal ideal of the discrete valuation ring `R`: its only non-vanishing
coefficients are the leading one `1` and the constant one `-π` (both intermediate coefficients
`X ^ 4`, `X ^ 3`, `X ^ 2`, `X` vanish except for the `X ^ 4`-coefficient `π ∈ 𝔪`), and the
constant coefficient `-π` is a uniformizer, hence in `𝔪` but not in `𝔪 ^ 2`.

The Eisenstein extension of a discrete valuation ring
(`Submission/Work/FFResidual/Eisenstein/isDomain_adjoinRoot_of_isEisensteinAt.lean`, a missing
chapter of Mathlib proved in this workspace) is then a domain.

The auxiliary facts are stated separately, so that the neighbouring files of this chapter
(`isFractionRing_asOrder`, `isDiscreteValuationRing_asOrder`, `modelResidueTrivial_asOrder`, ...)
can reuse them.
-/

namespace Work.FFResidual.CharP

open Polynomial

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The degree of the defining polynomial `X ^ 5 + π X ^ 4 - π` of the Artin–Schreier order is
at most `5`: the leading term is `X ^ 5` and the remaining part `π X ^ 4 - π` has degree `≤ 4`. -/
theorem asOrderPoly_degree_le (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).degree ≤ 5 := by
  refine le_trans (degree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (degree_add_le _ _) (max_le (degree_X_pow_le 5) ?_)
    exact le_trans (degree_C_mul_X_pow_le 4 P.π) (by norm_num)
  · exact le_trans degree_C_le (by norm_num)

/-- The coefficient of `X ^ 5` in `X ^ 5 + π X ^ 4 - π` is `1`. -/
theorem asOrderPoly_coeff_five (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).coeff 5 = 1 := by simp

/-- **The defining polynomial of the Artin–Schreier order is monic.** -/
theorem asOrderPoly_monic (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).Monic :=
  monic_of_degree_le 5 (asOrderPoly_degree_le P) (asOrderPoly_coeff_five P)

/-- **The defining polynomial of the Artin–Schreier order has degree `5`.** -/
theorem asOrderPoly_natDegree (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).natDegree = 5 :=
  le_antisymm (natDegree_le_iff_degree_le.mpr (asOrderPoly_degree_le P))
    (le_natDegree_of_ne_zero (by rw [asOrderPoly_coeff_five P]; exact one_ne_zero))

/-- The constant coefficient of `X ^ 5 + π X ^ 4 - π` is `-π`. -/
theorem asOrderPoly_coeff_zero (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).coeff 0 = -P.π := by simp

/-- The coefficient of `X ^ 4` in `X ^ 5 + π X ^ 4 - π` is `π`. -/
theorem asOrderPoly_coeff_four (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).coeff 4 = P.π := by simp

/-- All the other coefficients of `X ^ 5 + π X ^ 4 - π` vanish. -/
theorem asOrderPoly_coeff_eq_zero (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) {n : ℕ}
    (h0 : n ≠ 0) (h4 : n ≠ 4) (h5 : n ≠ 5) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).coeff n = 0 := by
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C, h0, h4, h5]

/-- **The defining polynomial of the Artin–Schreier order is Eisenstein** at the maximal ideal of
the discrete valuation ring `R`: the leading coefficient `1` is a unit, every other coefficient
below the degree is either `0` or the uniformizer `π` (hence in `𝔪`), and the constant coefficient
`-π` is in `𝔪` but not in `𝔪 ^ 2`. -/
theorem asOrderPoly_isEisensteinAt (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    Polynomial.IsEisensteinAt (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])
      (IsLocalRing.maximalIdeal P.R) := by
  have hπ : P.π ∈ IsLocalRing.maximalIdeal P.R := by
    rw [P.isUniformizer]
    exact Ideal.mem_span_singleton_self P.π
  -- the uniformizer is not in the square of the maximal ideal
  have hπ2 : P.π ∉ IsLocalRing.maximalIdeal P.R ^ 2 := by
    intro h
    rw [P.isUniformizer, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨r, hr⟩ := h
    have h2 : P.π ^ 2 * r = P.π * (P.π * r) := by ring
    rw [h2] at hr
    have h3 : P.π * (1 - P.π * r) = 0 := by rw [mul_sub, mul_one, ← hr, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact P.pi_ne_zero h0
    · refine (fun hu => (IsLocalRing.maximalIdeal.isMaximal P.R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hπ hu)) ?_
      rw [sub_eq_zero] at h0
      exact isUnit_iff_exists_inv.mpr ⟨r, h0.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(asOrderPoly_monic P).leadingCoeff]
    intro h1
    exact (IsLocalRing.maximalIdeal.isMaximal P.R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · intro n hn
    have hn5 : n < 5 := by rw [← asOrderPoly_natDegree P]; exact hn
    interval_cases n
    · rw [asOrderPoly_coeff_zero P]; exact neg_mem hπ
    · rw [asOrderPoly_coeff_eq_zero P (by norm_num) (by norm_num) (by norm_num)]
      exact zero_mem _
    · rw [asOrderPoly_coeff_eq_zero P (by norm_num) (by norm_num) (by norm_num)]
      exact zero_mem _
    · rw [asOrderPoly_coeff_eq_zero P (by norm_num) (by norm_num) (by norm_num)]
      exact zero_mem _
    · rw [asOrderPoly_coeff_four P]; exact hπ
  · rw [asOrderPoly_coeff_zero P]
    intro h
    exact hπ2 (by simpa using neg_mem h)

/-- **The Artin–Schreier order is a domain.**  `R[X]/(X ^ 5 + π X ^ 4 - π)` is a domain, because
the polynomial is Eisenstein at the maximal ideal of the discrete valuation ring `R` (hence
irreducible over the fraction field of `R`). -/
theorem isDomain_asOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    IsDomain (Work.FFResidual.FunctionFieldPlace.AsOrder P) :=
  Work.FFResidual.Eisenstein.isDomain_adjoinRoot_of_isEisensteinAt (asOrderPoly_monic P)
    (by rw [asOrderPoly_natDegree P]; norm_num) (asOrderPoly_isEisensteinAt P)

end Work.FFResidual.CharP
