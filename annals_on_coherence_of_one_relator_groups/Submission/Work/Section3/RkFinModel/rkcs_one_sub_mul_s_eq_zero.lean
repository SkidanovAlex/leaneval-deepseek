import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory

universe u

namespace Work.Section3.RkFinModel

open Work.ORHughesFree.Epic

/-- The row vector `w` is a right-null vector of the matrix `A` (`∀ i, ∑ j, A i j * w j = 0`).
Then the pairing `x ↦ ∑ j, x j * w j` kills the row space of `A`: for every `v` in the domain
of `rowMulLin A`, `∑ j, (rowMulLin A v) j * w j = 0`.

This is the computational core of `rkcs_one_sub_mul_s_eq_zero`: it is the statement that the
linear functional `x ↦ ∑ j, x j * w j` vanishes on `LinearMap.range (rowMulLin A)`. -/
private lemma sum_rowMulLin_mul_eq_zero {S : Type u} [Ring S] {a n : ℕ}
    (A : Matrix (Fin a) (Fin n) S) (w : Fin n → S)
    (hw : ∀ i : Fin a, ∑ j, A i j * w j = 0) (v : Fin a → S) :
    ∑ j, rowMulLin A v j * w j = 0 := by
  simp only [rowMulLin, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hw i, mul_zero]

/-- If `(1 - e) • u` lies in the row space of `A` and `w` is a right-null vector of `A`, then
`(1 - e) * (u ⬝ w) = 0`. Concretely: writing `(1 - e) • u = rowMulLin A v`, the scalar
`(1 - e) * s = ∑ j, ((1 - e) • u) j * w j` is a linear combination `∑ i, v i * (∑ j, A i j * w j)`
of the numbers `∑ j, A i j * w j`, all of which vanish. -/
theorem rkcs_one_sub_mul_s_eq_zero {S : Type u} [Ring S] {a n : ℕ}
    (A : Matrix (Fin a) (Fin n) S) (u w : Fin n → S) {e s : S}
    (hw : ∀ i : Fin a, ∑ j, A i j * w j = 0) (huw : ∑ j, u j * w j = s)
    (hPu : (1 - e) • u ∈ LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)) :
    (1 - e) * s = 0 := by
  obtain ⟨v, hv⟩ := hPu
  -- `(1 - e) * u j` is the `j`-th component of `rowMulLin A v`.
  have hv' : ∀ j, (1 - e) * u j = rowMulLin A v j := fun j => by
    rw [congr_fun hv j, Pi.smul_apply, smul_eq_mul]
  -- Push `(1 - e)` and `s` inside the sum defining `s`.
  rw [← huw, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [← mul_assoc, hv' j])]
  -- The resulting sum is killed by `w` on the row space of `A`.
  exact sum_rowMulLin_mul_eq_zero A w hw v

end Work.Section3.RkFinModel
