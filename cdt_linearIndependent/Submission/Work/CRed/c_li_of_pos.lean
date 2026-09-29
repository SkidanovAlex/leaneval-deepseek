import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Helpers
import Submission.Work.CRed.li_neg_family
import Submission.Work.CRed.log_neg_int
import Submission.Work.CRed.gap_pos
import Submission.Work.CRed.gap_neg

/-! Guidance from the project lead (the requester):

# Area CRed — reduce `cdt_theoremC_li` to positive m, n (`CPos`)

Statement: assuming `CPos`, the exact statement of `cdt_theoremC_li` in Submission.lean.
Proof: m, n ∈ ℤ∖{−1,0}, 10⁶|m−n| < |n|.
- Mixed signs are impossible (m ≥ 1, n ≤ −2 gives |m−n| ≥ |n|+1 > |n|/10⁶, and symmetrically).
- Both ≥ 1: `CPos` applies directly (strict ⇒ non-strict).
- Both ≤ −2: put m' = −m−1 ≥ 1, n' = −n−1 ≥ 1. Then |m'−n'| = |m−n|, |n'| = |n|−1, and
  10⁶|m−n| < |n| = n'+1 gives 10⁶|m'−n'| ≤ n' (integers). And 1 + 1/m = m'/(m'+1) =
  (1 + 1/m')⁻¹, so log(1+1/m) = −log(1+1/m'), same for n. The families ![1, x, y, xy] and
  ![1, −x, −y, xy] span the same ℚ-space; linear independence transfers (e.g. via
  `Submission.Helpers.linearIndependent_cons4_iff` component form: a relation p + q(−x) + r(−y) +
  s(xy) = 0 is the relation p + (−q)x + (−r)y + s(xy) = 0).
- m ≠ n transfers to m' ≠ n'.
Small lemma; do it directly.
-/

namespace Work.CRed

open Submission.CDTPlan

/-- The sign dichotomy for the hypothesis `m ∉ {-1, 0}` of Theorem C: such an integer is either
positive (`≥ 1`) or at most `-2`.  This is the case split that drives the reduction. -/
private lemma pos_or_le_neg_two {m : ℤ} (hm : m ≠ -1) (hm0 : m ≠ 0) :
    1 ≤ m ∨ m ≤ -2 := by omega

theorem c_li_of_pos (hC : CPos) (m n : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) (hn : n ≠ -1)
    (hn0 : n ≠ 0) (hgap : 10 ^ 6 * |m - n| < |n|) (hne : m ≠ n) :
    LinearIndependent ℚ ![1, Real.log (1 + 1 / (m : ℝ)),
      Real.log (1 + 1 / (n : ℝ)),
      Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))] := by
  rcases pos_or_le_neg_two hm hm0 with hm1 | hm2 <;>
    rcases pos_or_le_neg_two hn hn0 with hn1 | hn2
  · -- Both `m, n ≥ 1`: apply `CPos` to the natural numbers `m.toNat, n.toNat`.
    have hmZ : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    have hnZ : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have hcastm : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by rw [← Int.cast_natCast, hmZ]
    have hcastn : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by rw [← Int.cast_natCast, hnZ]
    have hM1 : 1 ≤ m.toNat := by omega
    have hN1 : 1 ≤ n.toNat := by omega
    have hMN : m.toNat ≠ n.toNat := by intro h; apply hne; omega
    have hg := gap_pos m n hm1 hn1 hgap
    have hspec := hC m.toNat n.toNat hM1 hN1 hMN hg
    simpa [hcastm, hcastn] using hspec
  · -- Mixed signs are impossible: `m ≥ 1`, `n ≤ -2` contradicts the gap hypothesis.
    exfalso
    have h1 : |m - n| = m - n := abs_of_pos (by omega)
    have h2 : |n| = -n := abs_of_neg (by omega)
    omega
  · -- Mixed signs are impossible: `m ≤ -2`, `n ≥ 1` contradicts the gap hypothesis.
    exfalso
    have h1 : |m - n| = n - m := by rw [abs_of_neg (by omega)]; ring
    have h2 : |n| = n := abs_of_pos (by omega)
    omega
  · -- Both `m, n ≤ -2`: apply `CPos` to `m' = -m-1`, `n' = -n-1` and transfer across the
    -- sign flip `log(1+1/m) = -log(1+1/m')`.
    have hM1 : 1 ≤ (-m - 1).toNat := by omega
    have hN1 : 1 ≤ (-n - 1).toNat := by omega
    have hMN : (-m - 1).toNat ≠ (-n - 1).toNat := by intro h; apply hne; omega
    have hg := gap_neg m n hm2 hn2 hgap
    have hspec := hC ((-m - 1).toNat) ((-n - 1).toNat) hM1 hN1 hMN hg
    have hlogM : Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ)) =
        -Real.log (1 + 1 / (m : ℝ)) := log_neg_int m hm2
    have hlogN : Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ)) =
        -Real.log (1 + 1 / (n : ℝ)) := log_neg_int n hn2
    have hlogM' : Real.log (1 + 1 / (m : ℝ)) =
        -Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ)) := by rw [hlogM]; ring
    have hlogN' : Real.log (1 + 1 / (n : ℝ)) =
        -Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ)) := by rw [hlogN]; ring
    have hvec : ![1, Real.log (1 + 1 / (m : ℝ)), Real.log (1 + 1 / (n : ℝ)),
          Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))]
        = ![1, -Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ)),
             -Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ)),
             Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ)) *
               Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ))] := by
      funext i
      fin_cases i
      · simp
      · show Real.log (1 + 1 / (m : ℝ)) =
          -Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ))
        exact hlogM'
      · show Real.log (1 + 1 / (n : ℝ)) =
          -Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ))
        exact hlogN'
      · show Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ)) =
          Real.log (1 + 1 / ((((-m - 1).toNat : ℕ)) : ℝ)) *
            Real.log (1 + 1 / ((((-n - 1).toNat : ℕ)) : ℝ))
        rw [hlogM', hlogN']; ring
    rw [hvec]
    exact li_neg_family _ _ hspec

end Work.CRed
