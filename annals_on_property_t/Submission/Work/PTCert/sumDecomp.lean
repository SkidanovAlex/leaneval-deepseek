import Mathlib
import Submission.Work.PTCert.labelData

namespace Work.PTCert

/-! Guidance from the project lead (the requester): this is the algebraic reshuffling at the start of
the proof of `LabelIdentity` (`Submission/Work/PTCert/labelIdentity.lean`): the sum over the index
type `TIdx` of `tCoef • of (tElt)` is the explicit element
`(1/SCv) • K - targetSum q Dq + residualSum res (SCv·Dq)`.  Read
`Submission/Work/PTCert/labelData.lean` for `TIdx`, `tElt`, `tCoef` (and note the `1/2` in the
residual coefficient).

Intended route: `Fintype.sum_sum_type` (twice) splits the sum over
`TIdx = (Σ r : Fin 18, Fin (ngE r.1)) ⊕ Fin 6561 ⊕ (Fin ncls × Bool)` into the three parts.
The key part: `Fintype.sum_sigma` turns `Σ_{t : Σ r : Fin 18, Fin (ngE r.1)}` into
`Σ_{r : Fin 18} Σ_{g : Fin (ngE r.1)}`, then `Fin.sum_univ_eq_sum_range` (twice) turns it into
`Σ r ∈ Finset.range 18, Σ g ∈ Finset.range (ngE r)`, and `Finset.smul_sum`/`smul_sum` +
`mul_smul` pull `(1/SCv)` out.  The target part is `Fin.sum_univ_eq_sum_range` together with the
definition of `targetSum` (the coefficient `-((q p : ℝ)/(Dq : ℝ))` matches `-` of the term of
`targetSum`).  The residual part: `Fintype.sum_prod_type` + the two `Bool` cases, `Finset.sum_add_distrib`,
`smul_add`, `div_eq_mul_inv`, and `(lprod 5 (canonW c))⁻¹` — the postfix `⁻¹` binds tighter than
application, so this is `of ((lprod 5 (canonW c))⁻¹)`, exactly `tElt` on `(c, true)`.
Finish with `sub_eq_add_neg`, `add_assoc` as needed. -/

open Submission.PTCert Submission.PTCert.G
open Work.PTCert.LabelData
open scoped BigOperators

theorem sumDecomp (pv q res : ℕ → ℤ) (Dq SCv : ℤ) :
    (∑ t : TIdx, tCoef pv q res SCv Dq t • MonoidAlgebra.of ℝ G5 (tElt t))
      = (1 / (SCv : ℝ)) • (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
            ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) • MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g)))
        - targetSum q Dq + residualSum res ((SCv : ℝ) * (Dq : ℝ)) := by
  -- split the index type: keys ⊕ (targets ⊕ residual signs)
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  -- ### the key part
  have hK :
      (∑ a : (Σ r : Fin 18, Fin (ngE r.1)),
          tCoef pv q res SCv Dq (Sum.inl a) • MonoidAlgebra.of ℝ G5 (tElt (Sum.inl a)))
        = (1 / (SCv : ℝ)) • (∑ r ∈ Finset.range 18, ∑ g ∈ Finset.range (ngE r),
              ((multE (keyOf r g) : ℝ) * (pv (keyOf r g) : ℝ)) •
                MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord r g))) := by
    rw [Fintype.sum_sigma]
    simp only [tCoef, tElt]
    rw [Fin.sum_univ_eq_sum_range (fun n => ∑ g : Fin (ngE n),
          (1 / (SCv : ℝ) * ((multE (keyOf n g.1) : ℝ) * (pv (keyOf n g.1) : ℝ))) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord n g.1))) 18]
    have hinner : ∀ n : ℕ, (∑ g : Fin (ngE n),
          (1 / (SCv : ℝ) * ((multE (keyOf n g.1) : ℝ) * (pv (keyOf n g.1) : ℝ))) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord n g.1)))
        = ∑ g ∈ Finset.range (ngE n),
            (1 / (SCv : ℝ) * ((multE (keyOf n g) : ℝ) * (pv (keyOf n g) : ℝ))) •
            MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord n g)) := by
      intro n
      exact Fin.sum_univ_eq_sum_range (fun g =>
        (1 / (SCv : ℝ) * ((multE (keyOf n g) : ℝ) * (pv (keyOf n g) : ℝ))) •
          MonoidAlgebra.of ℝ G5 (lprod 5 (keyWord n g))) (ngE n)
    simp only [hinner]
    simp only [mul_smul, ← Finset.smul_sum]
  -- ### the target part
  have hT :
      (∑ p : Fin 6561,
          tCoef pv q res SCv Dq (Sum.inr (Sum.inl p)) •
            MonoidAlgebra.of ℝ G5 (tElt (Sum.inr (Sum.inl p))))
        = - targetSum q Dq := by
    simp only [tCoef, tElt]
    rw [Fin.sum_univ_eq_sum_range (fun p => (-((q p : ℝ) / (Dq : ℝ))) •
      MonoidAlgebra.of ℝ G5 (lprod 5 [invL (p / 81), p % 81, 0, 0])) 6561]
    simp only [targetSum, neg_smul, Finset.sum_neg_distrib]
  -- ### the residual part
  have hR :
      (∑ c : Fin ncls × Bool,
          tCoef pv q res SCv Dq (Sum.inr (Sum.inr c)) •
            MonoidAlgebra.of ℝ G5 (tElt (Sum.inr (Sum.inr c))))
        = residualSum res ((SCv : ℝ) * (Dq : ℝ)) := by
    rw [Fintype.sum_prod_type]
    simp only [tCoef, tElt]
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    rw [Fin.sum_univ_eq_sum_range (fun c =>
      ((res c : ℝ) / ((SCv : ℝ) * (Dq : ℝ)) / 2) •
          MonoidAlgebra.of ℝ G5 ((lprod 5 (canonW c))⁻¹) +
        ((res c : ℝ) / ((SCv : ℝ) * (Dq : ℝ)) / 2) •
          MonoidAlgebra.of ℝ G5 (lprod 5 (canonW c))) ncls]
    rw [residualSum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_add, add_comm]
  rw [hK, hT, hR, sub_eq_add_neg, add_assoc]

end Work.PTCert
