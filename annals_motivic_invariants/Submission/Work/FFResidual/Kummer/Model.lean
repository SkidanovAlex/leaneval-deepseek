/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Kummer.Order
import Submission.Work.FFResidual.Eisenstein.isDomain_adjoinRoot_of_isEisensteinAt
import Submission.Work.FFResidual.Eisenstein.isDiscreteValuationRing_adjoinRoot_of_isEisensteinAt
import Submission.Work.FFResidual.Kummer.isFractionRing_kummerOrder
import Submission.Work.FFResidual.Kummer.modelPreserves_kummerOrder
import Submission.Work.FFResidual.Kummer.modelResidueTrivial_kummerOrder
import Submission.Work.FFResidual.Kummer.hasGoodReduction_kummerOrder

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The local model of the Kummer place

This file collects the local theory of the place of the function field `𝕜` at the Kummer extension
`𝕜(s)`, `s ^ 5 = π`:

* `KummerOrder P = R[X]/(X ^ 5 - π)` is a discrete valuation ring (the Eisenstein order) with
  fraction field the top field `Top P` (registered as instances `isDomain_kummerOrder`,
  `isDiscreteValuationRing_kummerOrder`, `isFractionRing_kummerOrder`);
* the Kummer automorphism `s ↦ ζ s` preserves the model and acts trivially on its residue field
  (`modelPreserves_kummerOrder`, `modelResidueTrivial_kummerOrder`);
* the constant Tate model has good reduction at the model (`hasGoodReduction_kummerOrder`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

open Polynomial

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The constant coefficient of `X ^ 5 - π` is `-π`. -/
theorem coeff_kummerOrder_poly_zero (P : FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 - C P.π : P.R[X]).coeff 0 = -P.π := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  norm_num

/-- **`X ^ 5 - π` is Eisenstein at the maximal ideal of the place**: the leading coefficient is `1`,
the intermediate coefficients vanish, and the constant coefficient `-π` is a uniformizer. -/
theorem isEisensteinAt_kummerOrder_poly (P : FunctionFieldPlace 𝔽 𝕜) :
    Polynomial.IsEisensteinAt (X ^ 5 - C P.π : P.R[X]) (IsLocalRing.maximalIdeal P.R) := by
  have hπ : P.π ∈ IsLocalRing.maximalIdeal P.R := by
    rw [P.isUniformizer]
    exact Ideal.mem_span_singleton_self P.π
  have hunit : ¬ IsUnit P.π := fun hu =>
    (IsLocalRing.maximalIdeal.isMaximal P.R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hπ hu)
  have hπ2 : P.π ∉ IsLocalRing.maximalIdeal P.R ^ 2 := by
    intro h
    rw [P.isUniformizer, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨r, hr⟩ := h
    have h2 : P.π ^ 2 * r = P.π * (P.π * r) := by ring
    rw [h2] at hr
    have h3 : P.π * (1 - P.π * r) = 0 := by rw [mul_sub, mul_one, ← hr, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact P.pi_ne_zero h0
    · refine hunit ?_
      rw [sub_eq_zero] at h0
      exact isUnit_iff_exists_inv.mpr ⟨r, h0.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.leadingCoeff_X_pow_sub_C (n := 5) (by norm_num)]
    intro h1
    exact (IsLocalRing.maximalIdeal.isMaximal P.R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · intro n hn
    have hn5 : n < 5 := by
      rw [Polynomial.natDegree_X_pow_sub_C (n := 5) (r := P.π)] at hn
      exact hn
    rcases eq_or_ne n 0 with rfl | h0
    · rw [P.coeff_kummerOrder_poly_zero]
      exact neg_mem hπ
    · have h5 : n ≠ 5 := by omega
      have hzero : (X ^ 5 - C P.π : P.R[X]).coeff n = 0 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        simp [h0, h5]
      rw [hzero]
      exact Submodule.zero_mem _
  · rw [P.coeff_kummerOrder_poly_zero]
    intro h
    exact hπ2 (by simpa using neg_mem h)

theorem kummerOrder_natDegree (P : FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 - C P.π : P.R[X]).natDegree = 5 :=
  Polynomial.natDegree_X_pow_sub_C (n := 5) (r := P.π)

/-- The Eisenstein order of the Kummer place is a domain. -/
instance isDomain_kummerOrder (P : FunctionFieldPlace 𝔽 𝕜) : IsDomain P.KummerOrder :=
  Work.FFResidual.Eisenstein.isDomain_adjoinRoot_of_isEisensteinAt
    (Polynomial.monic_X_pow_sub_C _ (by norm_num))
    (by rw [P.kummerOrder_natDegree]; norm_num)
    P.isEisensteinAt_kummerOrder_poly

/-- The Eisenstein order of the Kummer place is a discrete valuation ring. -/
instance isDiscreteValuationRing_kummerOrder (P : FunctionFieldPlace 𝔽 𝕜) :
    IsDiscreteValuationRing P.KummerOrder :=
  Work.FFResidual.Eisenstein.isDiscreteValuationRing_adjoinRoot_of_isEisensteinAt
    (Polynomial.monic_X_pow_sub_C _ (by norm_num))
    (by rw [P.kummerOrder_natDegree]; norm_num)
    P.isEisensteinAt_kummerOrder_poly

/-- The Eisenstein order of the Kummer place has fraction field the top field. -/
instance isFractionRing_kummerOrder (P : FunctionFieldPlace 𝔽 𝕜) :
    IsFractionRing P.KummerOrder P.Top :=
  Work.FFResidual.Kummer.isFractionRing_kummerOrder P

instance decEqResidueKummerOrder (P : FunctionFieldPlace 𝔽 𝕜) :
    DecidableEq (IsLocalRing.ResidueField P.KummerOrder) :=
  Classical.decEq _

end FunctionFieldPlace

end

end Work.FFResidual
