import Mathlib

/-!
# The vanishing kernel of `u ↦ u * A + v * B` for bounded-degree `u, v`

Let `A, B ∈ ℝ[X]` be nonzero of degrees `p` and `q`, with `gcd A B` of degree `ν < min p q`.
Suppose `u` has degree `≤ q - ν - 1` and `v` has degree `≤ p - ν - 1`, and the combination
`u * A + v * B` has vanishing coefficients in degrees `ν, ν+1, …, p + q - ν - 1`. Then the
combination has degree `≤ p + q - ν - 1`, so all its coefficients in degrees `≥ ν` vanish; since
`gcd A B` divides it, it must be zero.  Writing `A = G * (A/G)`, `B = G * (B/G)` with
`G = gcd A B` (so that the cofactors are coprime), the identity `u * A = -v * B` forces
`(A/G) ∣ v` and `(B/G) ∣ u`; the degree bounds `deg v ≤ p - ν - 1 < p - ν = deg (A/G)` and
`deg u ≤ q - ν - 1 < q - ν = deg (B/G)` then give `u = v = 0`.

This is the linear-algebra kernel computation behind the Sylvester/Bezout bound on `p + q`
in the CAD ("type localisation") development.
-/

namespace Work.WilE4.CAD

open Polynomial

theorem gcd_core_kernel {A B u v : Polynomial ℝ} {p q ν : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAn : A.natDegree = p) (hBn : B.natDegree = q)
    (hgν : (gcd A B).natDegree = ν) (hνp : ν < p) (hνq : ν < q)
    (hu : u.natDegree ≤ q - ν - 1) (hv : v.natDegree ≤ p - ν - 1)
    (hlow : (u * A + v * B).coeff ν = 0)
    (hhigh : ∀ k, ν < k → k ≤ p + q - ν - 1 → (u * A + v * B).coeff k = 0) :
    u = 0 ∧ v = 0 := by
  -- `gcd A B` is nonzero, since it divides the nonzero polynomial `A`.
  have hGne : gcd A B ≠ 0 := fun h => hA (zero_dvd_iff.mp (h ▸ gcd_dvd_left A B))
  -- Degree bound: the combination has degree at most `p + q - ν - 1`.
  have hWdeg : (u * A + v * B).natDegree ≤ p + q - ν - 1 := by
    have h1 : (u * A).natDegree ≤ p + q - ν - 1 := by
      calc (u * A).natDegree ≤ u.natDegree + A.natDegree := natDegree_mul_le
        _ ≤ (q - ν - 1) + p := add_le_add hu (le_of_eq hAn)
        _ = p + q - ν - 1 := by omega
    have h2 : (v * B).natDegree ≤ p + q - ν - 1 := by
      calc (v * B).natDegree ≤ v.natDegree + B.natDegree := natDegree_mul_le
        _ ≤ (p - ν - 1) + q := add_le_add hv (le_of_eq hBn)
        _ = p + q - ν - 1 := by omega
    calc (u * A + v * B).natDegree ≤ max (u * A).natDegree (v * B).natDegree :=
          natDegree_add_le _ _
      _ ≤ p + q - ν - 1 := max_le h1 h2
  -- Hence every coefficient in degree `≥ ν` vanishes.
  have hcoeff : ∀ k, ν ≤ k → (u * A + v * B).coeff k = 0 := by
    intro k hk
    rcases eq_or_lt_of_le hk with h | h
    · rw [← h]; exact hlow
    · by_cases hle : k ≤ p + q - ν - 1
      · exact hhigh k h hle
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hWdeg (Nat.lt_of_not_le hle))
  -- Therefore the combination is zero: `gcd A B` divides it and its degree is `< ν`.
  have hsum : u * A + v * B = 0 := by
    by_contra hne
    have hlt : (u * A + v * B).natDegree < ν := by
      by_contra hlt
      have hle : ν ≤ (u * A + v * B).natDegree := Nat.le_of_not_lt hlt
      have hc := hcoeff _ hle
      rw [coeff_natDegree] at hc
      exact hne ((leadingCoeff_eq_zero).mp hc)
    have hdvd : gcd A B ∣ u * A + v * B :=
      dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left A B) u)
              (dvd_mul_of_dvd_right (gcd_dvd_right A B) v)
    have hle2 := natDegree_le_of_dvd hdvd hne
    rw [hgν] at hle2
    omega
  -- Now `u * A = -v * B`.  Split off the gcd and use coprimality of the cofactors.
  have hA1 : gcd A B * (A / gcd A B) = A :=
    EuclideanDomain.mul_div_cancel' hGne (gcd_dvd_left A B)
  have hB1 : gcd A B * (B / gcd A B) = B :=
    EuclideanDomain.mul_div_cancel' hGne (gcd_dvd_right A B)
  have hnormG : normalize (gcd A B) = gcd A B := normalize_gcd A B
  have hgcd_eq : gcd (A / gcd A B) (B / gcd A B) = 1 := by
    have hc := gcd_mul_left (gcd A B) (A / gcd A B) (B / gcd A B)
    rw [hA1, hB1, hnormG] at hc
    exact mul_left_cancel₀ hGne (by rw [mul_one]; exact hc.symm)
  have hcop : IsCoprime (A / gcd A B) (B / gcd A B) :=
    (gcd_isUnit_iff _ _).mp (by rw [hgcd_eq]; exact isUnit_one)
  have hA1ne : A / gcd A B ≠ 0 := fun h => hA (by rw [← hA1, h, mul_zero])
  have hB1ne : B / gcd A B ≠ 0 := fun h => hB (by rw [← hB1, h, mul_zero])
  have hvB : v * B = -(u * A) := eq_neg_of_add_eq_zero_right hsum
  have huA : u * A = -(v * B) := eq_neg_of_add_eq_zero_left hsum
  have hdivA : A ∣ v * B := by rw [hvB]; exact dvd_neg.mpr (dvd_mul_of_dvd_right (dvd_refl A) u)
  have hdivB : B ∣ u * A := by rw [huA]; exact dvd_neg.mpr (dvd_mul_of_dvd_right (dvd_refl B) v)
  have hAB1 : A / gcd A B ∣ v * (B / gcd A B) := by
    have hm : gcd A B * (A / gcd A B) ∣ gcd A B * (v * (B / gcd A B)) := by
      rw [hA1]
      rw [show gcd A B * (v * (B / gcd A B)) = v * B from by
            rw [show gcd A B * (v * (B / gcd A B))
                  = v * (gcd A B * (B / gcd A B)) from by ring, hB1]]
      exact hdivA
    exact (mul_dvd_mul_iff_left hGne).mp hm
  have hA1dvdv : A / gcd A B ∣ v := hcop.dvd_of_dvd_mul_right hAB1
  have hA1deg : (A / gcd A B).natDegree = p - ν := by
    have hthis : (gcd A B).natDegree + (A / gcd A B).natDegree = A.natDegree := by
      rw [← natDegree_mul hGne hA1ne, hA1]
    rw [hgν, hAn] at hthis
    omega
  have hv0 : v = 0 := by
    by_contra hvne
    have hle2 := natDegree_le_of_dvd hA1dvdv hvne
    rw [hA1deg] at hle2
    omega
  have hBA1 : B / gcd A B ∣ u * (A / gcd A B) := by
    have hm : gcd A B * (B / gcd A B) ∣ gcd A B * (u * (A / gcd A B)) := by
      rw [hB1]
      rw [show gcd A B * (u * (A / gcd A B)) = u * A from by
            rw [show gcd A B * (u * (A / gcd A B))
                  = u * (gcd A B * (A / gcd A B)) from by ring, hA1]]
      exact hdivB
    exact (mul_dvd_mul_iff_left hGne).mp hm
  have hB1dvdu : B / gcd A B ∣ u := hcop.symm.dvd_of_dvd_mul_right hBA1
  have hB1deg : (B / gcd A B).natDegree = q - ν := by
    have hthis : (gcd A B).natDegree + (B / gcd A B).natDegree = B.natDegree := by
      rw [← natDegree_mul hGne hB1ne, hB1]
    rw [hgν, hBn] at hthis
    omega
  have hu0 : u = 0 := by
    by_contra hune
    have hle2 := natDegree_le_of_dvd hB1dvdu hune
    rw [hB1deg] at hle2
    omega
  exact ⟨hu0, hv0⟩

end Work.WilE4.CAD
