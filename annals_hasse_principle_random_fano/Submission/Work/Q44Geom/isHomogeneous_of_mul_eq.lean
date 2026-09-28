import Mathlib
import Submission.Work.Q44Geom.ReducDefs
import Submission.Work.Q44Geom.MaxDeg
import Submission.Work.Q44Geom.exists_minDeg_add_of_mul_eq
import Submission.Work.Q44Geom.homogeneousComponent_mul_of_maxDeg

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom

/-- Over a domain, if a product `A * B` of nonzero polynomials is homogeneous of degree `n`,
then both factors are homogeneous with degrees adding up to `n`.
Intended proof: let `i`, `j` be the *minimal* degrees (via `Work.Q44Geom.IsMinDeg` and
`Work.Q44Geom.homogeneousComponent_mul_of_minDeg` from `Q44Geom/ReducDefs`) and `a`, `b` the
*maximal* degrees of `A`, `B`.  The degree-`(i+j)` component of `A*B` is `A_i * B_j ≠ 0`, and the
degree-`(a+b)` component is `A_a * B_b ≠ 0`; since `A*B` is homogeneous of degree `n`,
`MvPolynomial.homogeneousComponent m P = if m = n then P else 0`, forcing `i+j = a+b = n`, whence
`i = a` and `j = b` (as `i ≤ a`, `j ≤ b`).  Then `A.IsHomogeneous i` and `B.IsHomogeneous j`
because every monomial in the support has degree squeezed between the min and the max. -/
theorem isHomogeneous_of_mul_eq {n : ℕ} {P A B : MvPolynomial (Fin 5) ℚ}
    (hP : P.IsHomogeneous n) (hAB : P = A * B) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ i j : ℕ, i + j = n ∧ A.IsHomogeneous i ∧ B.IsHomogeneous j := by
  -- `A * B` is homogeneous of degree `n`
  have hPh : (A * B).IsHomogeneous n := hAB ▸ hP
  -- minimal degrees of `A` and `B`, whose sum is `n` (proved in parallel, as
  -- `Work.Q44Geom.exists_minDeg_add_of_mul_eq`)
  obtain ⟨i, j, hi, hj, hij⟩ := exists_minDeg_add_of_mul_eq hP hAB hA hB
  -- maximal degrees of `A` and `B`, whose sum is `n` as well
  obtain ⟨a, ha⟩ := exists_isMaxDeg A hA
  obtain ⟨b, hb⟩ := exists_isMaxDeg B hB
  have hmax : MvPolynomial.homogeneousComponent (a + b) (A * B)
      = MvPolynomial.homogeneousComponent a A * MvPolynomial.homogeneousComponent b B :=
    homogeneousComponent_mul_of_maxDeg ha hb
  have hnzmax : MvPolynomial.homogeneousComponent (a + b) (A * B) ≠ 0 := by
    rw [hmax]
    exact mul_ne_zero ha.coeff_ne_zero hb.coeff_ne_zero
  have hifmax := MvPolynomial.homogeneousComponent_of_mem (m := a + b) hPh
  have hab : a + b = n := by
    by_contra hne
    rw [if_neg hne] at hifmax
    exact hnzmax hifmax
  -- hence the minimal and maximal degrees coincide
  have hia : i ≤ a := hi.le_maxDeg ha
  have hjb : j ≤ b := hj.le_maxDeg hb
  have hieq : i = a := by omega
  have hjeq : j = b := by omega
  refine ⟨i, j, hij, ?_, ?_⟩
  · exact hi.isHomogeneous_of_forall_le (fun t ht => by rw [hieq]; exact ha.2 t ht)
  · exact hj.isHomogeneous_of_forall_le (fun t ht => by rw [hjeq]; exact hb.2 t ht)

end Work.Q44Geom
