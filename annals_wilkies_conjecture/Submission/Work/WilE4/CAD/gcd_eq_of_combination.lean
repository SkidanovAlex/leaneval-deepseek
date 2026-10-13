import Mathlib

namespace Work.WilE4.CAD

open Polynomial

/-- If `W = u * A + v * B` satisfies the Bezout degree bounds `natDegree u ≤ q - ν - 1`,
`natDegree v ≤ p - ν - 1` (where `p = natDegree A`, `q = natDegree B`, `ν = natDegree (gcd A B)`)
has all coefficients strictly above `ν` vanishing and coefficient `1` at `ν`, then it equals
`gcd A B`. -/
theorem gcd_eq_of_combination {A B u v W : Polynomial ℝ} {p q ν : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAn : A.natDegree = p) (hBn : B.natDegree = q)
    (hgν : (gcd A B).natDegree = ν) (hνp : ν < p) (hνq : ν < q)
    (hu : u.natDegree ≤ q - ν - 1) (hv : v.natDegree ≤ p - ν - 1)
    (hW : W = u * A + v * B)
    (hhigh : ∀ k, ν < k → k ≤ p + q - ν - 1 → W.coeff k = 0)
    (hlow : W.coeff ν = 1) :
    W = gcd A B := by
  -- `gcd A B` divides `W = u * A + v * B`.
  have hGA : gcd A B ∣ A := gcd_dvd_left A B
  have hGB : gcd A B ∣ B := gcd_dvd_right A B
  have hGW : gcd A B ∣ W := by
    rw [hW]
    exact dvd_add (dvd_mul_of_dvd_right hGA u) (dvd_mul_of_dvd_right hGB v)
  -- `gcd A B ≠ 0`, hence monic (the gcd over a field is normalized).
  have hGne : gcd A B ≠ 0 := by
    intro h
    have hA0 : A = 0 := by
      have hd := gcd_dvd_left A B
      rw [h] at hd
      exact zero_dvd_iff.mp hd
    exact hA hA0
  have hGmonic : (gcd A B).Monic := by
    rw [← normalize_gcd A B]
    exact monic_normalize hGne
  have hGcoeff : (gcd A B).coeff ν = 1 := by
    have h := hGmonic.leadingCoeff
    rw [Polynomial.leadingCoeff, hgν] at h
    exact h
  have hWne : W ≠ 0 := by
    intro h; rw [h] at hlow; simp at hlow
  -- Degree bound `W.natDegree ≤ p + q - ν - 1` from the degree bounds on `u` and `v`.
  have hdegW : W.natDegree ≤ p + q - ν - 1 := by
    rw [hW]
    calc (u * A + v * B).natDegree ≤ max (u * A).natDegree (v * B).natDegree :=
            natDegree_add_le _ _
      _ ≤ p + q - ν - 1 := by
            apply max_le
            · calc (u * A).natDegree ≤ u.natDegree + A.natDegree := natDegree_mul_le
                _ ≤ (q - ν - 1) + p := by
                    exact add_le_add hu (le_of_eq hAn)
                _ ≤ p + q - ν - 1 := by omega
            · calc (v * B).natDegree ≤ v.natDegree + B.natDegree := natDegree_mul_le
                _ ≤ (p - ν - 1) + q := by
                    exact add_le_add hv (le_of_eq hBn)
                _ ≤ p + q - ν - 1 := by omega
  -- All coefficients of `W` above `ν` vanish, so `W.natDegree ≤ ν`.
  have hdegWν : W.natDegree ≤ ν := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hN2 : N ≤ p + q - ν - 1
    · exact hhigh N hN hN2
    · rw [not_le] at hN2
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegW hN2)
  have hνleW : ν ≤ W.natDegree := le_natDegree_of_ne_zero (by rw [hlow]; norm_num)
  have hWdeg : W.natDegree = ν := le_antisymm hdegWν hνleW
  -- `W = (gcd A B) * R` with `R` of degree `0`, i.e. a nonzero constant.
  obtain ⟨R, hR⟩ := hGW
  have hRne : R ≠ 0 := by
    intro h; rw [h, mul_zero] at hR; exact hWne hR
  have hRdeg : R.natDegree = 0 := by
    have h := natDegree_mul hGne hRne
    rw [← hR, hWdeg, hgν] at h
    omega
  have hRconst : R = C (R.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
  have hcoeff : W.coeff ν = (gcd A B).coeff ν * R.coeff 0 := by
    rw [hR, hRconst]
    rw [coeff_mul_C]
    simp
  have hcR : R.coeff 0 = 1 := by
    rw [hlow, hGcoeff, one_mul] at hcoeff
    exact hcoeff.symm
  rw [hR, hRconst, hcR]
  simp

end Work.WilE4.CAD
