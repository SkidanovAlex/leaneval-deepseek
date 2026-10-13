import Mathlib
import Submission.Work.DSCOH.ShiftToolkit

namespace Work.DSCOH

/-- A polynomial lying in the shifted piece `shift d (k * n)` is homogeneous of degree
`k * n - d`; consequently the coordinate sum of any monomial occurring in it is `k * n - d`. -/
theorem sum_coord_sub {A : Type*} [CommRing A] {n d k : ℕ} {m : Poly A n}
    (hm : m ∈ shift (A := A) (n := n) d (k * n)) {v : Fin n →₀ ℕ} (hv : v ∈ m.support) :
    ∑ i, ((v i : ℤ) - (k : ℤ)) = -(d : ℤ) := by
  have hle : d ≤ k * n := by
    by_contra h
    rw [shift_of_not_le h] at hm
    have : m = 0 := by simpa using hm
    rw [this, MvPolynomial.support_zero] at hv
    exact Finset.notMem_empty v hv
  have hm' : m ∈ homSub A n (k * n - d) := by
    rwa [shift_of_le hle] at hm
  rw [homSub, MvPolynomial.mem_homogeneousSubmodule] at hm'
  have hcoeff : m.coeff v ≠ 0 := MvPolynomial.mem_support_iff.mp hv
  have hweight : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) v = k * n - d := hm' hcoeff
  have hvdeg : v.degree = k * n - d := by
    rw [Finsupp.degree_eq_weight_one]; exact hweight
  have hvsum : (∑ i, v i) = k * n - d := by
    rw [← Finsupp.degree_eq_sum]; exact hvdeg
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumz : (∑ x, ((v x : ℕ) : ℤ)) = (k : ℤ) * n - (d : ℤ) := by
    rw [← Nat.cast_sum, hvsum, Nat.cast_sub hle]; push_cast; ring
  rw [hsumz]
  ring

end Work.DSCOH
