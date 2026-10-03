import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.exists_powerSeriesToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_rowSupport
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_colSupport
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.NaturalExtension.sum_Icc_sub_sum_Icc
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_of_rowSupport_lt
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_of_colSupport_gt

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The `v`-th summand of the coefficient of degree `S - R` in `p * q`, twisted by `τ^R`:
`(τ^R p_v) · (τ^{R+v} q_{S-R-v})`.  This is the common summand of the Toeplitz product and of the
coefficient expansion of the genuine product, compare `toeplitzSeries_mul`. -/
noncomputable def defectSummand {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (p q : Work.ORHughesFree.SkewLaurentSeries U) (R S : ℤ) (v : ℤ) : U :=
  (Multiplicative.ofAdd R • p.1 v) * (Multiplicative.ofAdd (R + v) • q.1 (S - R - v))

/-- The "low part" of the multiplicativity defect of the Toeplitz series matrix: the intermediate
degrees running from `lo p` up to `-r-1`, i.e. the contributions visible to the genuine coefficient
of `p * q` (which sums over all intermediate degrees) but not to the finite matrix product. -/
noncomputable def toeplitzDefectLow {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) : Matrix (Fin N) (Fin N) U :=
  fun r s => ∑ v ∈ Finset.Icc (Work.ORHughesFree.SkewLaurentSeries.lo p) (-(r : ℤ) - 1),
    defectSummand p q (r : ℤ) (s : ℤ) v

/-- The "high part" of the multiplicativity defect: the intermediate degrees running from `N-r`
to `s - r - lo q`, i.e. the contributions visible to the finite matrix product but not to the
genuine coefficient of `p * q`. -/
noncomputable def toeplitzDefectHigh {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) : Matrix (Fin N) (Fin N) U :=
  fun r s => ∑ v ∈ Finset.Icc ((N : ℤ) - (r : ℤ))
      ((s : ℤ) - (r : ℤ) - Work.ORHughesFree.SkewLaurentSeries.lo q),
    defectSummand p q (r : ℤ) (s : ℤ) v

/-- The matrix product `toeplitzSeries N p * toeplitzSeries N q`, entrywise as a sum over the
intermediate degrees `v ∈ [-r, N-1-r]`. -/
theorem toeplitzSeries_mul_apply {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) (r s : Fin N) :
    (toeplitzSeries N p * toeplitzSeries N q) r s
      = ∑ v ∈ Finset.Icc (-(r : ℤ)) ((N : ℤ) - 1 - (r : ℤ)),
          defectSummand p q (r : ℤ) (s : ℤ) v := by
  rw [Matrix.mul_apply]
  rw [show (∑ u : Fin N, toeplitzSeries N p r u * toeplitzSeries N q u s)
      = ∑ u : Fin N, defectSummand p q (r : ℤ) (s : ℤ) ((u : ℤ) - (r : ℤ)) from
    Finset.sum_congr rfl fun u _ => by
      rw [toeplitzSeries_apply, toeplitzSeries_apply, defectSummand]
      rw [show (r : ℤ) + ((u : ℤ) - (r : ℤ)) = (u : ℤ) by ring,
          show (s : ℤ) - (r : ℤ) - ((u : ℤ) - (r : ℤ)) = (s : ℤ) - (u : ℤ) by ring]]
  exact sum_fin_sub_shift_skew N (r : ℤ) (defectSummand p q (r : ℤ) (s : ℤ))

/-- The Toeplitz series matrix `toeplitzSeries N (p * q)`, entrywise as a sum over the
intermediate degrees `v ∈ [lo p, s - r - lo q]`. -/
theorem toeplitzSeries_prod_apply {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) (r s : Fin N) :
    toeplitzSeries N (p * q) r s
      = ∑ v ∈ Finset.Icc (Work.ORHughesFree.SkewLaurentSeries.lo p)
          ((s : ℤ) - (r : ℤ) - Work.ORHughesFree.SkewLaurentSeries.lo q),
          defectSummand p q (r : ℤ) (s : ℤ) v := by
  rw [toeplitzSeries_apply,
      Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds p q
        (Work.ORHughesFree.SkewLaurentSeries.lo p)
        (Work.ORHughesFree.SkewLaurentSeries.lo q)
        (fun n hn => Work.ORHughesFree.SkewLaurentSeries.lt_lo (f := p) hn)
        (fun n hn => Work.ORHughesFree.SkewLaurentSeries.lt_lo (f := q) hn)
        ((s : ℤ) - (r : ℤ))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [defectSummand, smul_mul', ← mul_smul, ← ofAdd_add]

/-- The defect `toeplitzSeries N (p * q) - toeplitzSeries N p * toeplitzSeries N q` splits as the
sum of its low part and its high part. -/
theorem toeplitzSeries_sub_mul_eq_low_add_high {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) :
    toeplitzSeries N (p * q) - toeplitzSeries N p * toeplitzSeries N q
      = toeplitzDefectLow N p q + toeplitzDefectHigh N p q := by
  ext r s
  rw [Matrix.sub_apply, Matrix.add_apply,
    toeplitzSeries_prod_apply, toeplitzSeries_mul_apply,
    toeplitzDefectLow, toeplitzDefectHigh]
  have hsplit := sum_Icc_sub_sum_Icc (defectSummand p q (r : ℤ) (s : ℤ))
      (Work.ORHughesFree.SkewLaurentSeries.lo p)
      ((s : ℤ) - (r : ℤ) - Work.ORHughesFree.SkewLaurentSeries.lo q)
      (-(r : ℤ)) ((N : ℤ) - 1 - (r : ℤ))
      (by omega) (fun v hv => by
        rw [defectSummand]
        rcases hv with hv | hv
        · rw [Work.ORHughesFree.SkewLaurentSeries.lt_lo (f := p) hv, smul_zero, zero_mul]
        · have hlt : (s : ℤ) - (r : ℤ) - v < Work.ORHughesFree.SkewLaurentSeries.lo q := by omega
          rw [Work.ORHughesFree.SkewLaurentSeries.lt_lo (f := q) hlt, smul_zero, mul_zero])
  rw [show ((N : ℤ) - 1 - (r : ℤ)) + 1 = (N : ℤ) - (r : ℤ) by ring] at hsplit
  exact hsplit

/-- **Multiplicativity defect of the Toeplitz series matrix.**  The `N × N` Toeplitz matrix
`toeplitzSeries N p` of `p` has `(r,s)` entry `τ^r (p_{s-r})`.  The product of the Toeplitz matrices
of `p` and `q` sums the contributions over the window `r + j ∈ [0, N-1]` only, so the difference
`toeplitzSeries N (p * q) - toeplitzSeries N p * toeplitzSeries N q` is supported in the rows
`r < -lo p` and the columns `s > N - 1 + lo q`, i.e. in at most
`max 0 (-lo p) + max 0 (-lo q)` rows/columns in total; this bounds its rank by that constant,
independently of `N`.  (Route: `toeplitzSeries_mul`/`sum_fin_sub_shift_skew` style manipulation to
write the defect as a sum of the low part (sum over `j ∈ [lo p, -r-1]`) and the high part (sum over
`j ∈ [N-r, s-r-lo q]`), then `rk_add_le`, `rk_le_card_of_rowSupport`, `rk_le_card_of_colSupport`.) -/
theorem rk_toeplitzSeries_sub_mul_le {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : Work.ORHughesFree.SylvesterRank U) (p q : Work.ORHughesFree.SkewLaurentSeries U)
    (N : ℕ) :
    rk.rk N N (Work.ORHughesFree.NaturalExtension.toeplitzSeries N (p * q)
        - Work.ORHughesFree.NaturalExtension.toeplitzSeries N p
          * Work.ORHughesFree.NaturalExtension.toeplitzSeries N q)
      ≤ ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo p)) : ℤ) : ℝ)
        + ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo q)) : ℤ) : ℝ) := by
  classical
  rw [toeplitzSeries_sub_mul_eq_low_add_high]
  have hlow : rk.rk N N (toeplitzDefectLow N p q)
      ≤ ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo p)) : ℤ) : ℝ) :=
    rk_le_of_rowSupport_lt rk (-(Work.ORHughesFree.SkewLaurentSeries.lo p)) _
      (fun i j hij => by
        rw [toeplitzDefectLow,
          Finset.Icc_eq_empty
            (by omega : ¬ (Work.ORHughesFree.SkewLaurentSeries.lo p ≤ -(i : ℤ) - 1))]
        simp)
  have hhigh : rk.rk N N (toeplitzDefectHigh N p q)
      ≤ ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo q)) : ℤ) : ℝ) := by
    have h := rk_le_of_colSupport_gt rk
      ((N : ℤ) - 1 + Work.ORHughesFree.SkewLaurentSeries.lo q) (toeplitzDefectHigh N p q)
      (fun i j hij => by
        rw [toeplitzDefectHigh,
          Finset.Icc_eq_empty
            (by omega : ¬ ((N : ℤ) - (i : ℤ)
              ≤ (j : ℤ) - (i : ℤ) - Work.ORHughesFree.SkewLaurentSeries.lo q))]
        simp)
    rw [show (N : ℤ) - 1 - ((N : ℤ) - 1 + Work.ORHughesFree.SkewLaurentSeries.lo q)
        = -(Work.ORHughesFree.SkewLaurentSeries.lo q) by ring] at h
    exact h
  exact le_trans (RankAPI.rk_add_le rk _ _) (add_le_add hlow hhigh)

end Work.ORHughesFree.NaturalExtension
