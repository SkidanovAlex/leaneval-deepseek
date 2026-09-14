import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

namespace Commons.Polynomial

/-- For a monic polynomial, the discriminant is natural with respect to ring homomorphisms. -/
theorem discr_map_of_monic {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {f : R[X]} (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  rcases eq_or_ne f.natDegree 0 with h0 | h0
  · rw [eq_one_of_monic_natDegree_zero hf h0, Polynomial.map_one]
    have hR : Polynomial.discr (1 : R[X]) = 1 := by
      rw [show (1 : R[X]) = Polynomial.C (1 : R) from (Polynomial.C_1 (R := R)).symm]
      exact Polynomial.discr_C 1
    have hS : Polynomial.discr (1 : S[X]) = 1 := by
      rw [show (1 : S[X]) = Polynomial.C (1 : S) from (Polynomial.C_1 (R := S)).symm]
      exact Polynomial.discr_C 1
    rw [hR, hS]; simp
  · have hn : 0 < f.natDegree := Nat.pos_of_ne_zero h0
    have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
    have hfm : (f.map φ).Monic := hf.map φ
    have hd1 : 0 < f.degree := (natDegree_pos_iff_degree_pos).mp hn
    have hd2 : 0 < (f.map φ).degree := (natDegree_pos_iff_degree_pos).mp (by rw [hdeg]; exact hn)
    have hr1 := resultant_deriv (f := f) hd1
    have hr2 := resultant_deriv (f := f.map φ) hd2
    have hr1' : f.resultant f.derivative f.natDegree (f.natDegree - 1)
        = (-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
      rw [hr1, hf.leadingCoeff]; simp
    have hr2' : (f.map φ).resultant (f.map φ).derivative (f.map φ).natDegree
          ((f.map φ).natDegree - 1)
        = (-1 : S) ^ ((f.map φ).natDegree * ((f.map φ).natDegree - 1) / 2) *
            (f.map φ).discr := by
      rw [hr2, hfm.leadingCoeff]; simp
    have hmain : (-1 : S) ^ ((f.map φ).natDegree * ((f.map φ).natDegree - 1) / 2) *
          (f.map φ).discr
        = (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.discr := by
      rw [← hr2', hdeg, derivative_map,
        resultant_map_map f f.derivative f.natDegree (f.natDegree - 1) φ, hr1']
      simp
    have hkk : (f.map φ).natDegree * ((f.map φ).natDegree - 1) / 2
        = f.natDegree * (f.natDegree - 1) / 2 := by rw [hdeg]
    rw [hkk] at hmain
    exact (isUnit_one.neg).pow _ |>.mul_left_cancel hmain

theorem discr_map_int (g : Polynomial ℤ) (hg : g.Monic) :
    Polynomial.discr (g.map (algebraMap ℤ ℚ)) = ((Polynomial.discr g : ℤ) : ℚ) := by
  simpa using discr_map_of_monic (algebraMap ℤ ℚ) hg

end Commons.Polynomial