import Mathlib
import Submission.Work.Peluse.Basic
import Submission.Commons.Analysis.Polynomial.abs_eval_sub_eval_le

namespace Work.Peluse.Ulower

open Finset

/-- Evaluating the realification `P.map (Int.castRingHom ℝ)` of an integer polynomial at a natural
number recovers the integer value, cast to `ℝ`. -/
lemma eval_map_intCast_eq (P : Polynomial ℤ) (y : ℕ) :
    (P.map (Int.castRingHom ℝ)).eval (y : ℝ) = ((P.eval (y : ℤ) : ℤ) : ℝ) := by
  exact Polynomial.eval_map_apply (p := P) (f := Int.castRingHom ℝ) (x := (y : ℤ))

/-- **The Lipschitz bound for a polynomial on `[0,N]`.**  For `P : ℤ[X]` of degree `≥ 1` there is a
constant `C > 0` with

`|P y − P y'| ≤ C · N^{deg P − 1} · |y − y'|`  for all `1 ≤ N`, `y, y' ≤ N`.

(Dividing `P y − P y'` by `y − y'` and bounding by the coefficients of `P` gives the mean-value
bound.)  This is the "slow variation of a polynomial over a short window" estimate used in the
progression-length bookkeeping of Peluse's §9. -/
theorem ss_aux_poly_diff (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N y y' : ℕ), 1 ≤ N → y ≤ N → y' ≤ N →
      |((P.eval (y : ℤ) : ℤ) : ℝ) - ((P.eval (y' : ℤ) : ℤ) : ℝ)|
        ≤ C * (N : ℝ) ^ (P.natDegree - 1) * |(y : ℝ) - (y' : ℝ)| := by
  refine ⟨max 1 ((∑ i ∈ Finset.range (P.natDegree + 1),
      |(P.map (Int.castRingHom ℝ)).coeff i|) * (P.natDegree : ℝ)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro N y y' hN hy hy'
    have hdeg : (P.map (Int.castRingHom ℝ)).natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
    have hb := Commons.Analysis.Polynomial.abs_eval_sub_eval_le
      (P.map (Int.castRingHom ℝ)) P.natDegree hP hdeg
      (X := (N : ℝ)) (x := (y : ℝ)) (y := (y' : ℝ))
      (Nat.cast_nonneg y) (Nat.cast_nonneg y')
      (by exact_mod_cast hy) (by exact_mod_cast hy') (by exact_mod_cast hN)
    rw [eval_map_intCast_eq P y, eval_map_intCast_eq P y'] at hb
    exact hb.trans (by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      · exact le_max_right _ _
      · exact pow_nonneg (Nat.cast_nonneg N) _
      · exact abs_nonneg _)

end Work.Peluse.Ulower
