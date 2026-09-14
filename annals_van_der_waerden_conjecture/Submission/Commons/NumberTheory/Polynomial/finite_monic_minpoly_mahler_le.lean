import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.Polynomial.finite_monic_poly_coeff_le
import Submission.Commons.NumberTheory.Polynomial.ncard_intpoly_mahler_le

namespace Commons.NumberTheory.Polynomial

/-- **Finiteness of algebraic integers of bounded degree and Mahler measure.**

The set of complex numbers `z` whose minimal polynomial over `ℤ` is monic of degree `m`
and has Mahler measure at most `S` is finite.  Indeed, such a `z` is an algebraic integer of
degree `m`, its minimal polynomial is an integer polynomial of degree `m` all of whose
coefficients are bounded by `2 ^ m * max S 1` (Mignotte's coefficient bound), and there are
only finitely many such polynomials, each having finitely many complex roots. -/
theorem finite_monic_minpoly_mahler_le (m : ℕ) (S : ℝ) :
    ({z : ℂ | (minpoly ℤ z).Monic ∧ (minpoly ℤ z).natDegree = m ∧
        Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} : Set ℂ).Finite := by
  classical
  set Z : Set ℂ := {z : ℂ | (minpoly ℤ z).Monic ∧ (minpoly ℤ z).natDegree = m ∧
      Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) ≤ S} with hZ
  change Z.Finite
  -- The coefficient bound for the minimal polynomials of points of `Z`.
  set B : ℝ := (2 : ℝ) ^ m * max S 1 with hBdef
  -- The finite set of admissible integer polynomials.
  set T : Set (Polynomial ℤ) :=
    {g | g.Monic ∧ g.natDegree = m ∧ ∀ i ≤ m, |((g.coeff i : ℤ) : ℝ)| ≤ B} with hT
  have hTfin : T.Finite := by
    rw [hT]
    exact finite_monic_poly_coeff_le (n := m) (fun _ : ℕ => B)
  -- Every `z ∈ Z` has `minpoly ℤ z ∈ T`, and `z` is a root of that polynomial.
  have hsub : Z ⊆ ⋃ g ∈ T, g.rootSet ℂ := by
    intro z hz
    rw [hZ] at hz
    simp only [Set.mem_ofPred_eq] at hz
    obtain ⟨hmon, hdeg, hM⟩ := hz
    have hmemT : minpoly ℤ z ∈ T := by
      rw [hT]
      refine ⟨hmon, hdeg, fun i _ => ?_⟩
      have h1 := coeff_abs_le_two_pow_natDegree_mul_mapMahlerMeasure (minpoly ℤ z) i
      rw [hdeg] at h1
      calc |(((minpoly ℤ z).coeff i : ℤ) : ℝ)|
          ≤ (2 : ℝ) ^ m * Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ) := h1
        _ ≤ (2 : ℝ) ^ m * max S 1 :=
            mul_le_mul_of_nonneg_left (hM.trans (le_max_left S 1)) (by positivity)
        _ = B := hBdef.symm
    exact Set.mem_biUnion hmemT
      (Polynomial.mem_rootSet.mpr ⟨hmon.ne_zero, minpoly.aeval ℤ z⟩)
  exact (hTfin.biUnion (fun g _ => g.rootSet_finite ℂ)).subset hsub

end Commons.NumberTheory.Polynomial