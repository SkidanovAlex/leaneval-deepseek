import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.LgRound

namespace Work.CNum

open Work.ANum

/-!
# `Work.CNum.SerStepErr` — the error propagation step of the `serUp` invariant

`SerStepErr` is the "error" component of the invariant `SerInv` maintained by the recursion
`serAuxB`: if the mantissa `(px, py)` approximates `c ^ (k+1) = (spt x y) ^ (k+1)` to within
`m2r pe`, and `σ` dominates the radius `srad x y e = ‖c‖ + e/SC` (with `m2r σ < 1`), then the
rounded product `(snx x y px py, sny x y px py)` approximates `c ^ (k+2)` to within
`m2r (snpe σ pe) = m2r (mulU σ pe + 2)`.

The proof splits the error into the propagation of the old error, `‖c‖ · m2r pe ≤ m2r σ · m2r pe`,
and the rounding error of the complex product, which is at most `2/SC = m2r 2`.
-/

/-- Mantissa ceiling division: `⌈a/SC⌉ · SC - a ∈ [0, SC)`. -/
lemma ceilDiv_mul_sub_mem (a : ℤ) :
    0 ≤ (-Int.ediv (-a) SC) * SC - a ∧ (-Int.ediv (-a) SC) * SC - a < SC := by
  have hem : Int.ediv (-a) SC * SC + (-a) % SC = -a := Int.ediv_mul_add_emod (-a) SC
  have hnn : 0 ≤ (-a) % SC := Int.emod_nonneg (-a) SC_ne_zero
  have hlt : (-a) % SC < SC := Int.emod_lt_of_pos (-a) SC_pos
  constructor <;> linarith

/-- The norm of a real number cast to `ℂ`. -/
lemma norm_ofRealC (r : ℝ) : ‖((r:ℝ):ℂ)‖ = |r| := by
  have h : ‖((r:ℝ):ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc ‖((r:ℝ):ℂ)‖ = Real.sqrt (‖((r:ℝ):ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- Rounding the product of the mantissa points `(x,y)` and `(px,py)` to the mantissa pair
`(snx, sny)` is correct to within `2/SC = m2r 2`. -/
lemma spt_round (x y px py : ℤ) :
    ‖spt x y * spt px py - spt (snx x y px py) (sny x y px py)‖ ≤ m2r 2 := by
  set A : ℤ := px * x - py * y with hA
  set B : ℤ := px * y + py * x with hB
  set U : ℤ := A - snx x y px py * SC with hU
  set V : ℤ := B - sny x y px py * SC with hV
  have hnA : snx x y px py = -Int.ediv (-A) SC := by simp only [snx, hA]
  have hnB : sny x y px py = -Int.ediv (-B) SC := by simp only [sny, hB]
  have hU0 : 0 ≤ snx x y px py * SC - A := by
    rw [hnA]; exact (ceilDiv_mul_sub_mem A).1
  have hU1 : snx x y px py * SC - A < SC := by
    rw [hnA]; exact (ceilDiv_mul_sub_mem A).2
  have hV0 : 0 ≤ sny x y px py * SC - B := by
    rw [hnB]; exact (ceilDiv_mul_sub_mem B).1
  have hV1 : sny x y px py * SC - B < SC := by
    rw [hnB]; exact (ceilDiv_mul_sub_mem B).2
  have hUle : |(U : ℝ)| ≤ (SC : ℝ) := by
    have h1 : U = -(snx x y px py * SC - A) := by rw [hU]; ring
    have h2 : (0:ℝ) ≤ ((snx x y px py * SC - A : ℤ) : ℝ) := by exact_mod_cast hU0
    have h3 : ((snx x y px py * SC - A : ℤ) : ℝ) ≤ (SC:ℝ) := by
      exact_mod_cast (le_of_lt hU1)
    rw [h1, Int.cast_neg, abs_neg, abs_of_nonneg h2]
    exact h3
  have hVle : |(V : ℝ)| ≤ (SC : ℝ) := by
    have h1 : V = -(sny x y px py * SC - B) := by rw [hV]; ring
    have h2 : (0:ℝ) ≤ ((sny x y px py * SC - B : ℤ) : ℝ) := by exact_mod_cast hV0
    have h3 : ((sny x y px py * SC - B : ℤ) : ℝ) ≤ (SC:ℝ) := by
      exact_mod_cast (le_of_lt hV1)
    rw [h1, Int.cast_neg, abs_neg, abs_of_nonneg h2]
    exact h3
  have heq : spt x y * spt px py - spt (snx x y px py) (sny x y px py)
      = ((U : ℂ) + (V : ℂ) * Complex.I) / ((((SC:ℝ) * (SC:ℝ) : ℝ)) : ℂ) := by
    simp only [spt, snx, sny, hU, hV, hA, hB]
    field_simp
    push_cast
    ring_nf
    rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  rw [heq, norm_div]
  have hw : ‖(((((SC:ℝ) * (SC:ℝ) : ℝ)) : ℂ))‖ = (SC:ℝ) * SC := by
    rw [norm_ofRealC, abs_of_nonneg (le_of_lt (mul_pos SC_posR SC_posR))]
  rw [hw]
  have hz : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ |(U:ℝ)| + |(V:ℝ)| := by
    have := Complex.norm_le_abs_re_add_abs_im ((U : ℂ) + (V : ℂ) * Complex.I)
    simpa using this
  have hz2 : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ (SC:ℝ) + SC :=
    le_trans hz (by linarith [hUle, hVle])
  have hden : (0:ℝ) < (SC:ℝ) * SC := mul_pos SC_posR SC_posR
  refine le_trans (div_le_div_of_nonneg_right hz2 hden.le) ?_
  rw [show (SC:ℝ) + SC = 2 * (SC:ℝ) by ring]
  have hgoal : (2 * (SC:ℝ)) / ((SC:ℝ) * SC) = m2r 2 := by
    rw [m2r,
      div_eq_div_iff (mul_ne_zero (ne_of_gt SC_posR) (ne_of_gt SC_posR)) (ne_of_gt SC_posR)]
    ring
  rw [hgoal]

theorem SerStepErr {x y e σ : ℤ} {k : ℕ} {px py pe : ℤ} (he : 0 ≤ e) (hσlt : Work.ANum.m2r σ < 1) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) (hpe : 0 ≤ pe) (hp5 : ‖Work.CNum.spt x y ^ (k + 1) - Work.CNum.spt px py‖ ≤ Work.ANum.m2r pe) : ‖Work.CNum.spt x y ^ (k + 2) - Work.CNum.spt (Work.CNum.snx x y px py) (Work.CNum.sny x y px py)‖ ≤ Work.ANum.m2r (Work.CNum.snpe σ pe) := by
  have he0 : (0:ℝ) ≤ m2r e := m2r_nonneg_NrmSpec he
  have hpe0 : (0:ℝ) ≤ m2r pe := m2r_nonneg_NrmSpec hpe
  have hc : ‖spt x y‖ ≤ m2r σ := by
    have h1 : ‖spt x y‖ ≤ srad x y e := by
      have h2 : srad x y e = ‖spt x y‖ + m2r e := rfl
      rw [h2]; linarith
    linarith
  have hpow : ‖spt x y ^ (k + 2) - spt x y * spt px py‖ ≤ m2r σ * m2r pe := by
    have h2 : spt x y ^ (k + 2) - spt x y * spt px py
        = (spt x y ^ (k + 1) - spt px py) * spt x y := by
      rw [show k + 2 = k + 1 + 1 from by ring, pow_succ]
      ring
    rw [h2, norm_mul]
    calc ‖spt x y ^ (k + 1) - spt px py‖ * ‖spt x y‖ ≤ m2r pe * m2r σ :=
          mul_le_mul hp5 hc (norm_nonneg _) hpe0
      _ = m2r σ * m2r pe := by ring
  have hmul : ‖spt x y * spt px py - spt (snx x y px py) (sny x y px py)‖ ≤ m2r 2 :=
    spt_round x y px py
  have hmain : ‖spt x y ^ (k + 2) - spt (snx x y px py) (sny x y px py)‖
      ≤ m2r σ * m2r pe + m2r 2 := by
    have h3 : spt x y ^ (k + 2) - spt (snx x y px py) (sny x y px py)
        = (spt x y ^ (k + 2) - spt x y * spt px py)
          + (spt x y * spt px py - spt (snx x y px py) (sny x y px py)) := by ring
    rw [h3]
    exact le_trans (norm_add_le _ _) (add_le_add hpow hmul)
  refine le_trans hmain ?_
  rw [snpe, m2r_add]
  linarith [m2r_mulU_ge σ pe]

end Work.CNum
