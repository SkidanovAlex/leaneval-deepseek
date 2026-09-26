import Mathlib
import Submission.Work.SG.SellingStep

/-! ## The Selling step on the superbase commutes with right multiplication

`Work.SG.selling_step_sb`: for a unimodular basis matrix `W` and distinct superbase indices
`i j`, the superbase of `W * sellStepMat i j` is the Selling step `sellStep (sb W) i j` applied
to the superbase of `W`.

The proof is linear algebra, through the two "coordinate descriptions" of the superbase:

* `mulVec_coordVec : W.mulVec (coordVec m) = sb W m`, i.e. the superbase of `W` is `W` applied to
  the coordinate vectors attached to the four superbase indices;
* `sb_mul_apply : sb (W * M) m = W.mulVec (sb M m)`, which is the previous identity combined
  with `(W*M).mulVec v = W.mulVec (M.mulVec v)`;
* the columns of `sellStepMat i j` are the vectors `sellStep coordVec i j b.succ`, so
  `W.mulVec` turns them into `sellStep (sb W) i j b.succ` because `W.mulVec` is additive and
  `sellStep` is built from additions and negations (`mulVec_sellStep`).

The two indices `1,2,3` of the superbase are columns and are handled directly; the special index
`0` is the *negative* of the sum of the other three, and both sides are handled by
`sum_zero_apply_zero`, using that the superbase of any matrix (and the Selling step of a
zero-summing family) sums to zero. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- `W` is additive: applying it to the Selling step of a family of vectors is the Selling step
of the family of images.  (`sellStep` only uses addition and negation.) -/
private theorem mulVec_sellStep (W : IMat) (u : Fin 4 → IVec) (i j m : Fin 4) :
    W.mulVec (sellStep u i j m) = sellStep (fun m => W.mulVec (u m)) i j m := by
  simp only [sellStep_apply]
  by_cases hi : m = i
  · rw [ite_eq_left hi, ite_eq_left hi, Matrix.mulVec_neg]
  · rw [ite_eq_right hi, ite_eq_right hi]
    by_cases hj : m = j
    · rw [ite_eq_left hj, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj, Matrix.mulVec_add]

/-- The `m`-th superbase vector of a product is the first factor applied to the `m`-th superbase
vector of the second: `sb (W * M) m = W.mulVec (sb M m)`. -/
private theorem sb_mul_apply (W M : IMat) (m : Fin 4) : sb (W * M) m = W.mulVec (sb M m) := by
  rw [← mulVec_coordVec (W * M) m, ← mulVec_coordVec M m]
  rw [← Matrix.mulVec_mulVec]

/-- The columns of `sellStepMat i j` are the Selling step applied to the coordinate vectors. -/
private theorem sb_sellStepMat_succ (i j : Fin 4) (k : Fin 3) :
    sb (sellStepMat i j) k.succ = sellStep coordVec i j k.succ := by
  funext a
  simp [sb_succ]

/-- In a family of vectors summing to zero, the `0`-th vector is the negative of the sum of the
remaining three. -/
private theorem sum_zero_apply_zero {v : Fin 4 → IVec} (h : ∑ m, v m = 0) :
    v 0 = -(v 1 + v 2 + v 3) := by
  rw [Fin.sum_univ_four] at h
  have h' : v 0 + (v 1 + v 2 + v 3) = 0 := by rw [← h]; abel
  exact eq_neg_of_add_eq_zero_left h'

/-- The Selling step preserves the sum of a family of four vectors. -/
private theorem sellStep_sum (v : Fin 4 → IVec) (i j : Fin 4) (hij : i ≠ j) :
    ∑ m, sellStep v i j m = ∑ m, v m := by
  rw [Fin.sum_univ_four (f := fun m => sellStep v i j m), Fin.sum_univ_four (f := v)]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp [sellStep]; abel)

/-- The Selling step on the superbase of `W` is realised by right multiplication with
`sellStepMat i j`. -/
theorem selling_step_sb (W : IMat) (i j : Fin 4) (hij : i ≠ j) :
    sb (W * sellStepMat i j) = sellStep (sb W) i j := by
  -- Indices `1,2,3` (the columns) are immediate; index `0` needs the zero-sum identities.
  have hne : ∀ m : Fin 4, m ≠ 0 →
      sb (W * sellStepMat i j) m = sellStep (sb W) i j m := by
    intro m hm
    rcases Fin.eq_zero_or_eq_succ m with h0 | ⟨k, hk⟩
    · exact absurd h0 hm
    · rw [hk, sb_mul_apply, sb_sellStepMat_succ]
      simpa [mulVec_coordVec] using mulVec_sellStep W coordVec i j k.succ
  funext m
  rcases Fin.eq_zero_or_eq_succ m with h0 | ⟨k, hk⟩
  · rw [h0]
    have h1 : sb (W * sellStepMat i j) 0
        = -(sb (W * sellStepMat i j) 1 + sb (W * sellStepMat i j) 2
            + sb (W * sellStepMat i j) 3) := sum_zero_apply_zero (sb_sum_zero _)
    have h2 : sellStep (sb W) i j 0
        = -(sellStep (sb W) i j 1 + sellStep (sb W) i j 2 + sellStep (sb W) i j 3) := by
      have hsum : (∑ m, sellStep (sb W) i j m) = 0 := by
        rw [sellStep_sum (sb W) i j hij, sb_sum_zero]
      simpa using sum_zero_apply_zero (v := fun m : Fin 4 => sellStep (sb W) i j m) hsum
    rw [h1, h2, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide)]
  · rw [hk]; exact hne k.succ (Fin.succ_ne_zero k)

end Work.SG
