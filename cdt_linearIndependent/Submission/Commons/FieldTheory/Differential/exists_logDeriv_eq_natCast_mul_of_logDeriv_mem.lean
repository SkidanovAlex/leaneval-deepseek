import Mathlib.FieldTheory.Differential.Basic
import Submission.Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic

/-!
# A multiple of a base-field logarithmic derivative

Let `L/K` be a finite extension of fields carrying compatible derivations.  If `x ∈ L` is nonzero
and its logarithmic derivative `x′/x` is the image of an element `a ∈ K` of the base field, then
some positive integer multiple `m·a` is the logarithmic derivative of a nonzero element of `K`.

The proof uses the minimal polynomial `p = minpoly K x` of `x` over `K`, of degree `d ≥ 1`.  From
`p(x) = 0` and `x′ = a·x` the identity
`p^{(D)} + a·X·p′ = d·a·p`   (`p^{(D)}` the coefficient-wise derivative of `p`)
follows by a degree argument, and comparing constant coefficients gives
`(p.coeff 0)′ = d·a·(p.coeff 0)`.  Since `p.coeff 0 ≠ 0` (otherwise `X ∣ p`, whence `x = 0`),
the element `u := p.coeff 0 ∈ K` satisfies `logDeriv u = d·a`.
-/

open Polynomial

namespace Commons.FieldTheory.Differential

/-- If `x ≠ 0` in a finite extension `L/K` of differential fields has logarithmic derivative in
the image of the base field, `logDeriv x = a`, then some positive multiple of `a` is the
logarithmic derivative of a nonzero element of the base field. -/
theorem exists_logDeriv_eq_natCast_mul_of_logDeriv_mem {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Differential K] [Differential L]
    [DifferentialAlgebra K L] {x : L} (hx : x ≠ 0) {a : K}
    (ha : Differential.logDeriv x = algebraMap K L a) :
    ∃ m : ℕ, 0 < m ∧ ∃ u : K, u ≠ 0 ∧ Differential.logDeriv u = (m : K) * a := by
  have hxint : IsIntegral K x := (IsAlgebraic.of_finite K x).isIntegral
  let p : K[X] := minpoly K x
  have hp_monic : p.Monic := by simpa [p] using minpoly.monic hxint
  have hp_aeval : aeval x p = 0 := minpoly.aeval K x
  have hd_pos : 0 < p.natDegree := by
    simpa [p] using minpoly.natDegree_pos (A := K) (B := L) hxint
  -- `x′ = a · x`
  have hx' : Differential.deriv x = algebraMap K L a * x := by
    have h := ha
    rw [Differential.logDeriv, div_eq_iff hx] at h
    exact h
  -- The auxiliary polynomial `q := p^{(D)} + a·X·p′ - d·a·p` has degree `< d`.
  let q : K[X] :=
    Differential.mapCoeffs p + a • (X * derivative p) - ((p.natDegree : K) * a) • p
  have hqaeval : aeval x q = 0 := by
    have h1 := Differential.deriv_aeval_eq (A := K) (R := L) x p
    rw [hp_aeval, map_zero] at h1
    have hsm : aeval x (a • (X * derivative p)) =
        algebraMap K L a * (x * aeval x (derivative p)) := by
      rw [map_smul, Algebra.smul_def, map_mul, aeval_X]
    have hsm2 : aeval x (((p.natDegree : K) * a) • p) = 0 := by
      rw [map_smul, hp_aeval, smul_zero]
    have hkey : algebraMap K L a * (x * aeval x (derivative p)) =
        Differential.deriv x * aeval x (derivative p) := by
      rw [← mul_assoc, ← hx']
    simp only [q, map_add, map_sub, hsm, hsm2, sub_zero]
    rw [hkey, mul_comm (Differential.deriv x) (aeval x (derivative p)), h1.symm]
  have hqdeg : q.natDegree ≤ p.natDegree - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hmap : (Differential.mapCoeffs p).coeff N = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt
          (Commons.FieldTheory.Differential.natDegree_mapCoeffs_le_of_monic p hp_monic) hN)
    have hNd : p.natDegree ≤ N := by omega
    have key : q.coeff N = a * (X * derivative p).coeff N - ((p.natDegree : K) * a) * p.coeff N := by
      simp only [q, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_smul,
        smul_eq_mul, hmap, zero_add]
    rcases lt_or_eq_of_le hNd with hlt | heq
    · have hpN : p.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      have hXn : (X * derivative p).coeff N = 0 := by
        obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hpN, zero_mul]
      rw [key, hpN, hXn]; ring
    · have hpN : p.coeff N = 1 := by rw [← heq]; exact hp_monic.coeff_natDegree
      have hXn : (X * derivative p).coeff N = (N : K) := by
        obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hpN, one_mul]
        push_cast
        ring
      rw [key, hpN, hXn, mul_one, ← heq]
      ring
  have hq0 : q = 0 :=
    eq_zero_of_dvd_of_natDegree_lt (p := p)
      (by simpa [p] using minpoly.dvd K x hqaeval)
      (lt_of_le_of_lt hqdeg (Nat.sub_one_lt (ne_of_gt hd_pos)))
  -- Compare constant coefficients.
  have hc : Differential.deriv (p.coeff 0) = ((p.natDegree : K) * a) * (p.coeff 0) := by
    have h0 := congrArg (fun r : K[X] => r.coeff 0) hq0
    have hX0 : (X * derivative p).coeff 0 = 0 :=
      Polynomial.X_dvd_iff.mp (dvd_mul_right X (derivative p))
    simp only [q, Polynomial.coeff_sub, Polynomial.coeff_add, Differential.coeff_mapCoeffs,
      Polynomial.coeff_smul, smul_eq_mul, hX0, mul_zero, Polynomial.coeff_zero] at h0
    rw [add_zero, sub_eq_zero] at h0
    exact h0
  -- The constant coefficient is nonzero because `x ≠ 0`.
  have hc0ne : p.coeff 0 ≠ 0 := by
    intro hc0
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hc0
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr
      exact hp_monic.ne_zero hr
    have haeval_r : aeval x r = 0 := by
      have h : aeval x (X * r) = 0 := by rw [← hr]; exact hp_aeval
      rw [aeval_mul, aeval_X] at h
      exact (mul_eq_zero.mp h).resolve_left hx
    have hdvd : p ∣ r := by simpa [p] using minpoly.dvd K x haeval_r
    have hle := Polynomial.natDegree_le_of_dvd hdvd hr0
    have hdeg : p.natDegree = 1 + r.natDegree := by
      rw [hr, Polynomial.natDegree_mul Polynomial.X_ne_zero hr0, Polynomial.natDegree_X]
    omega
  refine ⟨p.natDegree, hd_pos, p.coeff 0, hc0ne, ?_⟩
  rw [Differential.logDeriv, hc, mul_div_cancel_right₀ _ hc0ne]

end Commons.FieldTheory.Differential