import Mathlib
import Submission.CDT.KolchinHeart

/-!
# Kolchin's lemma for algebraic extensions: no new constants

Let `R ⊆ S` be fields of characteristic zero with derivations, compatible
(`DifferentialAlgebra R S`).  If `u ∈ S` is algebraic over `R` and `u′ = a` with `a ∈ R`, then
`u` differs from an element of `R` by a *constant*: there is `b ∈ R` with `(u + b)′ = 0`.

Equivalently (`exists_algebraMap_of_isIntegral_of_deriv_mem`): if moreover every constant of `S`
lies in the image of `R`, then `u` itself is the image of an element of `R`.

This is the "algebraic" step of Kolchin's theorem on the algebraic independence of logarithms:
an element which is algebraic over the base and whose derivative lies in the base cannot
introduce new constants.

The proof is the classical one: let `m = minpoly R u` (monic, `m(u) = 0`).  Differentiating
`m(u) = 0` with the chain rule `Differential.deriv_aeval_eq` gives
`(mapCoeffs m)(u) + m′(u)·a = 0`, i.e. `u` is a root of `mapCoeffs m + C a * m′`, a polynomial of
*smaller* degree, which must therefore vanish; comparing the coefficients of `X^(D-1)`
(`D = natDegree m`, `m` monic) gives `(m_{D-1})′ + a·D = 0`, and then `b = m_{D-1}/D`
satisfies `b′ = -a`.
-/

open scoped Differential

noncomputable section

namespace Submission.CDT

open Polynomial

variable {R S : Type*} [Field R] [Differential R] [CharZero R] [Field S] [Algebra R S]
  [Differential S] [DifferentialAlgebra R S]

/-- If `m` is a monic polynomial over `R` of nonzero degree, then the coefficientwise derivative
`mapCoeffs m` has strictly smaller degree. -/
lemma natDegree_mapCoeffs_lt_of_monic {m : Polynomial R} (hm : m.Monic)
    (hpos : 0 < m.natDegree) : (Differential.mapCoeffs m).natDegree < m.natDegree := by
  by_contra hlt
  rw [not_lt] at hlt
  have heq : (Differential.mapCoeffs m).natDegree = m.natDegree :=
    le_antisymm (natDegree_mapCoeffs_le m) hlt
  have h1 : (Differential.mapCoeffs m).leadingCoeff = 0 := by
    rw [← coeff_natDegree, heq, Differential.coeff_mapCoeffs, coeff_natDegree, hm.leadingCoeff,
      Derivation.map_one_eq_zero]
  have h2 : (Differential.mapCoeffs m) ≠ 0 := by
    rintro h0
    rw [h0] at heq
    simp only [natDegree_zero] at heq
    omega
  exact leadingCoeff_ne_zero.mpr h2 h1

/-- **Kolchin's lemma, algebraic case.**  An element `u` algebraic over the base field `R` whose
derivative lies in `R` differs from an element of `R` by a constant. -/
theorem exists_deriv_add_eq_zero_of_isIntegral {u : S} (hu : IsIntegral R u) {a : R}
    (ha : u′ = algebraMap R S a) :
    ∃ b : R, (u + algebraMap R S b)′ = 0 := by
  set m : Polynomial R := minpoly R u with hm
  have hmonic : m.Monic := minpoly.monic hu
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hu
  have haeval : (Polynomial.aeval u) m = 0 := minpoly.aeval R u
  -- `u` is a root of the polynomial `mapCoeffs m + C a * m′`
  have hd : (Polynomial.aeval u)
      (Differential.mapCoeffs m + Polynomial.C a * m.derivative) = 0 := by
    have h := Differential.deriv_aeval_eq u m
    rw [haeval, map_zero, ha] at h
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, h]
    ring
  -- which has smaller degree, hence vanishes
  have hlt : (Differential.mapCoeffs m + Polynomial.C a * m.derivative).natDegree
      < m.natDegree := by
    have hle : (Differential.mapCoeffs m + Polynomial.C a * m.derivative).natDegree
        ≤ m.natDegree := by
      refine le_trans (natDegree_add_le _ _) (max_le (natDegree_mapCoeffs_le m) ?_)
      exact le_of_lt (lt_of_le_of_lt (natDegree_C_mul_le a m.derivative)
        (natDegree_derivative_lt (ne_of_gt hpos)))
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hc : (Differential.mapCoeffs m + Polynomial.C a * m.derivative).coeff m.natDegree = 0 := by
      rw [coeff_add, Differential.coeff_mapCoeffs, coeff_natDegree, hmonic.leadingCoeff,
        Derivation.map_one_eq_zero,
        coeff_C_mul, coeff_eq_zero_of_natDegree_lt (natDegree_derivative_lt (ne_of_gt hpos)),
        mul_zero, add_zero]
    rw [← heq, coeff_natDegree] at hc
    have hne0 : (Differential.mapCoeffs m + Polynomial.C a * m.derivative) ≠ 0 := by
      rintro h0
      rw [h0] at heq
      simp only [natDegree_zero] at heq
      omega
    exact leadingCoeff_ne_zero.mpr hne0 hc
  have hzero : Differential.mapCoeffs m + Polynomial.C a * m.derivative = 0 := by
    have hdvd : minpoly R u ∣ (Differential.mapCoeffs m + Polynomial.C a * m.derivative) :=
      minpoly.dvd R u hd
    rw [hm] at hdvd
    by_contra hne
    obtain ⟨q, hq⟩ := hdvd
    have hqne : q ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hq
      exact hne hq
    have hnd := natDegree_mul (hmonic.ne_zero) hqne
    rw [hq, hnd] at hlt
    omega
  -- extract the coefficient of `X^(D-1)`, `D = m.natDegree`
  have hsub : m.natDegree - 1 + 1 = m.natDegree :=
    Nat.sub_add_cancel (show 1 ≤ m.natDegree from Nat.succ_le_of_lt hpos)
  have hcast : ((↑(m.natDegree - 1) + 1 : R)) = (m.natDegree : R) := by
    exact_mod_cast hsub
  have hcoeff : (Differential.mapCoeffs m + Polynomial.C a * m.derivative).coeff
      (m.natDegree - 1) = 0 := by
    rw [hzero, coeff_zero]
  simp only [coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul, coeff_derivative, hsub,
    hcast, coeff_natDegree, hmonic.leadingCoeff, one_mul] at hcoeff
  -- `hcoeff : (m_{D-1})′ + a * ↑D = 0`
  have hroot : (m.coeff (m.natDegree - 1))′ = -(a * (m.natDegree : R)) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hcoeff
  have hDne : (m.natDegree : R) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  refine ⟨m.coeff (m.natDegree - 1) / (m.natDegree : R), ?_⟩
  have hb : (m.coeff (m.natDegree - 1) / (m.natDegree : R))′ = -a := by
    have hD' : ((m.natDegree : R))′ = 0 := Derivation.map_natCast _ _
    have h1 : (m.coeff (m.natDegree - 1))′
        = (m.coeff (m.natDegree - 1) / (m.natDegree : R))′ * (m.natDegree : R) := by
      conv_lhs => rw [← div_mul_cancel₀ (m.coeff (m.natDegree - 1)) hDne]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD', mul_zero, zero_add, mul_comm]
    rw [h1] at hroot
    refine mul_right_cancel₀ hDne ?_
    rw [hroot]
    ring
  rw [Derivation.map_add, DifferentialAlgebra.deriv_algebraMap, ha, hb, map_neg, add_neg_cancel]

/-- **Kolchin's lemma, algebraic case, `mem` form.**  If in addition the constants of `S` are the
images of constants of `R`, then `u` itself lies in the image of `R`. -/
theorem exists_algebraMap_of_isIntegral_of_deriv_mem {u : S} (hu : IsIntegral R u) {a : R}
    (ha : u′ = algebraMap R S a) [Differential.ContainConstants R S] :
    ∃ c : R, u = algebraMap R S c := by
  obtain ⟨b, hb⟩ := exists_deriv_add_eq_zero_of_isIntegral hu ha
  obtain ⟨c, hc⟩ :=
    Differential.ContainConstants.mem_range_of_deriv_eq_zero (A := R) hb
  exact ⟨c - b, by rw [map_sub, hc, add_sub_cancel_right]⟩

end Submission.CDT
