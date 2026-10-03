import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs

namespace Work.FIArea2.R6

open Finset

/-- **The index divides every lattice determinant.**

Let `L = {w : c ∣ A w₁ - B w₂}` be the lattice cut out by the congruences, of index
`wcI c A B = c / gcd(c,A,B)` in `ℤ²`.  Then for any two lattice vectors `u, w ∈ L` the
determinant `wcDet u w = u₁ w₂ - u₂ w₁` is divisible by that index.

PROOF: From `c ∣ A u₁ - B u₂` and `c ∣ A w₁ - B w₂` one gets, for `D = wcDet u w`,
the two identities

  `A · D = w₂ (A u₁ - B u₂) - u₂ (A w₁ - B w₂)`,   `B · D = w₁ (A u₁ - B u₂) - u₁ (A w₁ - B w₂)`,

so `c ∣ A D` and `c ∣ B D`; Bézout on `(A,B)` gives `c ∣ gcd(A,B) · D`; together with the
trivial `c ∣ c · D` and Bézout on `(c, gcd(A,B))` this yields `c ∣ gcd(c,A,B) · D`.  Dividing by
`gcd(c,A,B) = c / wcI c A B` (which is positive since `c ≥ 1`) gives `wcI c A B ∣ D`. -/
theorem wcI_dvd_wcDet (c A B : ℕ) (hc : 1 ≤ c) (u w : ℤ × ℤ)
    (hu : wcInL c A B u) (hw : wcInL c A B w) :
    ((wcI c A B : ℕ) : ℤ) ∣ wcDet u w := by
  have hu' : (c : ℤ) ∣ (A : ℤ) * u.1 - (B : ℤ) * u.2 := hu
  have hw' : (c : ℤ) ∣ (A : ℤ) * w.1 - (B : ℤ) * w.2 := hw
  -- `c ∣ A · D`
  have hA : (c : ℤ) ∣ (A : ℤ) * wcDet u w := by
    have h : (A : ℤ) * wcDet u w
        = w.2 * ((A : ℤ) * u.1 - (B : ℤ) * u.2) - u.2 * ((A : ℤ) * w.1 - (B : ℤ) * w.2) := by
      simp only [wcDet]; ring
    rw [h]
    exact dvd_sub (hu'.mul_left w.2) (hw'.mul_left u.2)
  -- `c ∣ B · D`
  have hB : (c : ℤ) ∣ (B : ℤ) * wcDet u w := by
    have h : (B : ℤ) * wcDet u w
        = w.1 * ((A : ℤ) * u.1 - (B : ℤ) * u.2) - u.1 * ((A : ℤ) * w.1 - (B : ℤ) * w.2) := by
      simp only [wcDet]; ring
    rw [h]
    exact dvd_sub (hu'.mul_left w.1) (hw'.mul_left u.1)
  -- Bézout on `(A,B)`: `c ∣ gcd(A,B) · D`
  have hd : (c : ℤ) ∣ ((Nat.gcd A B : ℕ) : ℤ) * wcDet u w := by
    have key : ((Nat.gcd A B : ℕ) : ℤ) * wcDet u w
        = (Nat.gcdA A B : ℤ) * ((A : ℤ) * wcDet u w)
          + (Nat.gcdB A B : ℤ) * ((B : ℤ) * wcDet u w) := by
      rw [Nat.gcd_eq_gcd_ab]; ring
    rw [key]
    exact dvd_add (hA.mul_left _) (hB.mul_left _)
  -- Bézout on `(c, gcd(A,B))`: `c ∣ gcd(c, gcd(A,B)) · D`
  have hg : (c : ℤ) ∣ ((Nat.gcd c (Nat.gcd A B) : ℕ) : ℤ) * wcDet u w := by
    have key : ((Nat.gcd c (Nat.gcd A B) : ℕ) : ℤ) * wcDet u w
        = (Nat.gcdA c (Nat.gcd A B) : ℤ) * ((c : ℤ) * wcDet u w)
          + (Nat.gcdB c (Nat.gcd A B) : ℤ) * (((Nat.gcd A B : ℕ) : ℤ) * wcDet u w) := by
      rw [Nat.gcd_eq_gcd_ab]; ring
    rw [key]
    exact dvd_add ((dvd_mul_right (c : ℤ) (wcDet u w)).mul_left _) (hd.mul_left _)
  -- identify `gcd(c, gcd(A,B))` with `wcG c A B = gcd(gcd c A) B`
  have hgeq : Nat.gcd c (Nat.gcd A B) = wcG c A B := by
    simp only [wcG]; exact (Nat.gcd_assoc c A B).symm
  rw [hgeq] at hg
  have hgpos : 0 < wcG c A B := by
    rw [← hgeq]
    exact Nat.gcd_pos_of_pos_left (Nat.gcd A B) (by omega)
  have hgdvd : wcG c A B ∣ c := by
    rw [← hgeq]; exact Nat.gcd_dvd_left c (Nat.gcd A B)
  -- `c = gcd · wcI c A B`; cancel the positive factor `gcd`
  have hcast : (c : ℤ) = (wcG c A B : ℤ) * ((wcI c A B : ℕ) : ℤ) := by
    have h := Nat.mul_div_cancel' hgdvd
    have h2 : ((wcG c A B * (c / wcG c A B) : ℕ) : ℤ) = (c : ℤ) := by exact_mod_cast h
    rw [Nat.cast_mul] at h2
    exact h2.symm
  rw [hcast] at hg
  have hgne : (wcG c A B : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hgpos)
  exact (mul_dvd_mul_iff_left hgne).mp hg

end Work.FIArea2.R6
