import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.deriv_algebraMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial

namespace Work.Genus.Deriv

/-- **In characteristic zero, the kernel of `d/dt` is the constants.**  Route: `deriv f = 0` says
`num' * denom = num * denom'` in `F[X]`; since `num` and `denom` are coprime (`RatFunc.isCoprime_num_denom`),
`num ∣ num'`, so `num = 0`, or `num` is constant (because `natDegree num' < natDegree num` in
characteristic zero, `Polynomial.natDegree_derivative_lt`); then `num * denom' = 0` gives `denom' = 0`
and hence `denom` constant, and `denom` is monic, so `denom = 1`.  The converse is
`RatFunc.num_algebraMap`/`denom_algebraMap`. -/
theorem deriv_eq_zero_iff {F : Type*} [Field F] [CharZero F] (f : RatFunc F) :
    Work.Genus.deriv f = 0 ↔ ∃ c : F, f = algebraMap F (RatFunc F) c := by
  constructor
  · intro h
    -- The denominator of the quotient-rule expression is non-zero.
    have hden : (algebraMap F[X] (RatFunc F)) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero f.denom_ne_zero
    -- `deriv f = 0` forces the numerator of the quotient-rule expression to vanish.
    have hnum : (algebraMap F[X] (RatFunc F)) f.num.derivative
        * (algebraMap F[X] (RatFunc F)) f.denom
        - (algebraMap F[X] (RatFunc F)) f.num
          * (algebraMap F[X] (RatFunc F)) f.denom.derivative = 0 := by
      have hh := h
      unfold Work.Genus.deriv at hh
      rcases (div_eq_zero_iff.mp hh) with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero 2 hden)
    -- Descend to a polynomial identity: `num' * denom = num * denom'`.
    have hpoly : f.num.derivative * f.denom - f.num * f.denom.derivative = 0 := by
      refine RatFunc.algebraMap_injective F ?_
      rw [map_sub, map_mul, map_mul, map_zero]
      exact hnum
    have hmul : f.num.derivative * f.denom = f.num * f.denom.derivative := sub_eq_zero.mp hpoly
    -- Coprimality of the reduced form: `num ∣ num'`.
    have hnumdvd : f.num ∣ f.num.derivative :=
      (RatFunc.isCoprime_num_denom f).dvd_of_dvd_mul_right
        (by rw [hmul]; exact dvd_mul_right _ _)
    -- In characteristic zero the derivative strictly lowers the degree, so `num' = 0`.
    have hderiveq : f.num.derivative = 0 := by
      by_cases h0 : f.num.natDegree = 0
      · exact Polynomial.derivative_eq_zero.mpr h0
      · by_contra hne
        have hle : f.num.natDegree ≤ f.num.derivative.natDegree :=
          natDegree_le_of_dvd hnumdvd hne
        have hlt := Polynomial.natDegree_derivative_lt (p := f.num) h0
        omega
    rcases eq_or_ne f.num 0 with hnum0 | hnumne
    · -- `f = 0`, the constant `0`.
      refine ⟨0, ?_⟩
      rw [RatFunc.num_eq_zero_iff.mp hnum0]
      simp
    · -- `num ≠ 0`, so `denom' = 0` and `denom` is the monic constant `1`.
      have hden_deriv : f.denom.derivative = 0 := by
        rw [hderiveq, zero_mul] at hmul
        exact (mul_eq_zero.mp hmul.symm).resolve_left hnumne
      have hdeg : f.denom.natDegree = 0 := Polynomial.derivative_eq_zero.mp hden_deriv
      have hden1 : f.denom = 1 := by
        have hc : f.denom.coeff 0 = 1 := by
          rw [← hdeg]
          exact f.monic_denom
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, hc, Polynomial.C_1]
      -- `num` is a constant, and `f = num / 1 = num`.
      obtain ⟨c, hc⟩ : ∃ c : F, f.num = Polynomial.C c :=
        ⟨f.num.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hderiveq⟩
      refine ⟨c, ?_⟩
      conv_lhs => rw [← RatFunc.num_div_denom f]
      rw [hden1, map_one, div_one, hc, Polynomial.C_eq_algebraMap]
      exact (IsScalarTower.algebraMap_apply F F[X] (RatFunc F) c).symm
  · -- Conversely a constant has zero derivative (`deriv_algebraMap`, `derivative_C`).
    rintro ⟨c, rfl⟩
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F) c, ← Polynomial.C_eq_algebraMap,
      Work.Genus.Deriv.deriv_algebraMap, Polynomial.derivative_C, map_zero]

end Work.Genus.Deriv
