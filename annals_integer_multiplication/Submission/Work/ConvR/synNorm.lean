import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.normsAux

/-!
# Norm bound for the synthetic DFT (convolution over `ℝ = ℂ[y]/(y^r+1)`)

Paper Proposition 3.4 / Lemma 2.5 use that the synthetic multidimensional DFT `G` (resp. `G*`)
does not increase the sup norm: it is a normalised sum of `yMul`-images, and multiplication by
`y^e` acts on `ℂ[y]/(y^r+1)` by a signed permutation of the coefficients.

Main statements:

* `synDFT_coeff_norm_le` : every coefficient `(synDFT r ts sgn u) j c` is bounded by `‖u‖`;
* `synNorm` : `‖synDFT r ts sgn u‖ ≤ ‖u‖` for a nonempty transform (this is the conjunct of the
  `Work.ConvR.norms` package).
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Each coefficient of the synthetic DFT is bounded by the sup norm of the input: it is
`1/M` times a sum of `M` terms, each of which is a coefficient of a `yMul`-image of an input
entry, hence bounded by `‖u‖`. -/
theorem synDFT_coeff_norm_le (r : ℕ) (ts : List ℕ) (sgn : ℤ)
    (u : Fin ts.prod → Fin r → ℂ) (j : Fin ts.prod) (c : Fin r) :
    ‖HvdH.synDFT r ts sgn u j c‖ ≤ ‖u‖ := by
  rw [synDFT_apply]
  have hTpos : (0 : ℝ) < ts.prod := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le (j : ℕ)) j.isLt : 0 < ts.prod)
  calc ‖1 / ↑ts.prod * ∑ k : Fin ts.prod,
        HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts ↑j) (HvdH.digits ts ↑k))
          (u k) c‖
      = (1 / (ts.prod : ℝ)) * ‖∑ k : Fin ts.prod,
          HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts ↑j) (HvdH.digits ts ↑k))
            (u k) c‖ := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    _ ≤ (1 / (ts.prod : ℝ)) * ∑ k : Fin ts.prod,
          ‖HvdH.yMul r (sgn * HvdH.synExp r ts (HvdH.digits ts ↑j) (HvdH.digits ts ↑k))
            (u k) c‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (1 / (ts.prod : ℝ)) * ∑ _k : Fin ts.prod, ‖u‖ := by
        gcongr with k
        exact le_trans (le_trans (norm_le_pi_norm _ c)
          (yMul_norm_le r _ (u k))) (norm_le_pi_norm u k)
    _ = ‖u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- The synthetic DFT does not increase the sup norm (for a nonempty transform). -/
theorem synNorm (r : ℕ) (ts : List ℕ) (sgn : ℤ) (u : Fin ts.prod → Fin r → ℂ)
    (h : 0 < ts.prod) : ‖HvdH.synDFT r ts sgn u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 (fun j => ?_)
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
    (fun c => synDFT_coeff_norm_le r ts sgn u j c)

end Work.ConvR
