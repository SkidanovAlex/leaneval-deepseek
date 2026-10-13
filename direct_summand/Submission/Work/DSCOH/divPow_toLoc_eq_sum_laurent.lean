import Mathlib
import Submission.Work.DSCOH.ShiftToolkit

namespace Work.DSCOH

theorem divPow_toLoc_eq_sum_laurent {A : Type*} [CommRing A] {n : ℕ} (k : ℕ) (m : Poly A n) :
    divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k
        (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) m) =
      ∑ v ∈ m.support,
        (m.coeff v) • laurent (A := A) (n := n) (fun i => (v i : ℤ) - (k : ℤ)) := by
  -- Expand `m` in its monomial basis.
  have h_expand : m =
      ∑ v ∈ m.support, (m.coeff v) • xpow (A := A) (n := n) (fun i => v i) := by
    conv_lhs => rw [MvPolynomial.as_sum (p := m)]
    apply Finset.sum_congr rfl
    intro v _
    rw [MvPolynomial.smul_eq_C_mul, ← mvpoly_monomial_eq_xpow (A := A) (n := n) v,
      MvPolynomial.C_mul_monomial, mul_one]
  conv_lhs => rw [h_expand]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, map_smul,
    ← laurent_sub_one_eq (A := A) (n := n) (α := fun i => v i) (k := k)]

end Work.DSCOH
