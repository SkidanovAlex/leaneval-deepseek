import Mathlib
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis

/-!
# The discriminant of `ℚ(√a)` divides `4a`

Let `K` be a number field generated over `ℚ` by an element `x` with `x ^ 2 = a`, where `a` is a
rational integer.  Then `K` is either `ℚ` itself or the quadratic field `ℚ(√a)`, and in either
case its discriminant divides `4 * a`: for `K = ℚ` the discriminant is `1`, while for a quadratic
field the powers `1, x` form a `ℤ`-basis of a full sublattice of the ring of integers, whose
discriminant is `4 * a`.

The proof uses the power basis `pb` attached to `x` (which exists because `x` is integral and
generates `K`).  Its elements are `x ^ i`, hence integral, so the discriminant of `K` divides the
discriminant of the power basis.  That discriminant is computed by the two classical formulae

* `Algebra.discr K pb.basis = (-1) ^ (n * (n - 1) / 2) * norm K (f' (x))` where `f` is the
  minimal polynomial of `x` and `n = [K : ℚ]` (`Algebra.discr_powerBasis_eq_norm`),
* `norm K x = (-1) ^ n * f.coeff 0` (`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`).

With `[K : ℚ] = 2` and `f = X ^ 2 - a` these give `discr K = 4 * a`; with `[K : ℚ] = 1` the
discriminant is `1`.
-/

namespace Work.QuadraticFields

open Polynomial

theorem discr_dvd_of_sq_eq {K : Type*} [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = algebraMap ℚ K (a : ℚ)) (hgen : Algebra.adjoin ℚ ({x} : Set K) = ⊤) :
    NumberField.discr K ∣ 4 * a := by
  -- `x` is integral over `ℚ` and over `ℤ`
  have hIntQ : IsIntegral ℚ x :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hx]; exact isIntegral_algebraMap)
  have hIntZ : IsIntegral ℤ x :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [hx]
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := a))
  -- the power basis attached to `x`
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop' hIntQ hgen
  have hgen_pb : pb.gen = x := PowerBasis.ofAdjoinEqTop'_gen hIntQ hgen
  have hdim : pb.dim = (minpoly ℚ x).natDegree := PowerBasis.ofAdjoinEqTop'_dim hIntQ hgen
  have hfin : Module.finrank ℚ K = pb.dim := PowerBasis.finrank pb
  -- its elements are powers of `x`, hence integral
  have hbint : ∀ i : Fin pb.dim, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [PowerBasis.basis_eq_pow, hgen_pb]
    exact hIntZ.pow _
  obtain ⟨m, hm⟩ :=
    Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis pb.basis hbint
  -- `minpoly ℚ x` divides `X ^ 2 - C a`
  have hmonic : (X ^ 2 - C (a : ℚ) : ℚ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have haeval : aeval x (X ^ 2 - C (a : ℚ) : ℚ[X]) = 0 := by simp [hx]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C (a : ℚ) : ℚ[X]) := minpoly.dvd_iff.mpr haeval
  have hdim_le : pb.dim ≤ 2 := by
    rw [hdim]
    calc (minpoly ℚ x).natDegree ≤ (X ^ 2 - C (a : ℚ) : ℚ[X]).natDegree :=
          natDegree_le_of_dvd hdvd hmonic.ne_zero
      _ = 2 := natDegree_X_pow_sub_C
  have hdim_pos : 0 < pb.dim := pb.dim_pos
  have hcases : pb.dim = 1 ∨ pb.dim = 2 := by omega
  rcases hcases with h1 | h2
  · -- ## `[K : ℚ] = 1`: the power basis has a single element `1`, of discriminant `1`
    have hdisc : Algebra.discr ℚ pb.basis = 1 := by
      rw [Algebra.discr_def, Algebra.traceMatrix_of_basis pb.basis,
        Algebra.traceForm_toMatrix_powerBasis pb,
        Matrix.det_eq_elem_of_card_eq_one (by simp [h1]) ⟨0, hdim_pos⟩]
      simp only [Matrix.of_apply]
      rw [add_zero, pow_zero, show (1 : K) = algebraMap ℚ K (1 : ℚ) by simp,
        Algebra.trace_algebraMap, hfin, h1]
      norm_num
    have hdiv : NumberField.discr K ∣ 1 := by
      refine ⟨m, ?_⟩
      have hq : (1 : ℚ) = (NumberField.discr K : ℚ) * (m : ℚ) := by rw [← hdisc]; exact hm
      exact_mod_cast hq
    exact hdiv.trans (one_dvd (4 * a))
  · -- ## `[K : ℚ] = 2`: the power basis is `1, x` and its discriminant is `4 * a`
    have hfr : Module.finrank ℚ K = 2 := by rw [hfin, h2]
    have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) := by
      have hle : (X ^ 2 - C (a : ℚ) : ℚ[X]).natDegree ≤ (minpoly ℚ x).natDegree := by
        rw [← hdim, h2, natDegree_X_pow_sub_C]
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hIntQ) hmonic hdvd
        hle).symm
    have hdisc : Algebra.discr ℚ pb.basis = 4 * (a : ℚ) := by
      rw [Algebra.discr_powerBasis_eq_norm ℚ pb, hfr, hgen_pb, hmin]
      rw [show derivative (X ^ 2 - C (a : ℚ) : ℚ[X]) = C (2 : ℚ) * X by
        rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C]
        simp]
      rw [show (aeval x) (C (2 : ℚ) * X : ℚ[X]) = algebraMap ℚ K 2 * x by simp]
      rw [map_mul (Algebra.norm ℚ), Algebra.norm_algebraMap, ← hgen_pb,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, h2, hgen_pb, hmin]
      rw [hfr, show ((X ^ 2 - C (a : ℚ) : ℚ[X]).coeff 0) = -(a : ℚ) by simp]
      norm_num
    refine ⟨m, ?_⟩
    have hq : (4 : ℚ) * (a : ℚ) = (NumberField.discr K : ℚ) * (m : ℚ) := by
      rw [← hdisc]; exact hm
    exact_mod_cast hq

end Work.QuadraticFields
