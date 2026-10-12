import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.LatticeCoulomb

open scoped BigOperators

/-!
# `Work.BoseRowsL.LatticeCoulomb.taylorRemainderNorm`

The second order Taylor remainder of `x ↦ ‖x‖⁻²` at `b`, in the operator-norm shape used
by the cell comparison of the lattice Coulomb kernel: for `‖b‖ ≥ 1` and `|wᵢ| ≤ 1/2`,

  `|‖b+w‖⁻² − ‖b‖⁻² + 2⟪b,w⟫/‖b‖⁴| ≤ 100‖w‖²/‖b‖⁴`.

With `A = ‖b‖²`, `q = ‖w‖²`, `p = ⟪b,w⟫`, `B = ‖b+w‖² = A + 2p + q` the left side is exactly
`|4p² + 2pq − qA| / (A²B)`, and `4p² + 2pq − qA = (2p+q)² − qB`.  Hence it suffices to prove the
purely algebraic bound `(2p+q)² ≤ 101 q B` under `A ≥ 1`, `0 ≤ q ≤ 3/4`, `p² ≤ Aq` — the three
consequences of the hypotheses (the last one being Cauchy–Schwarz).  The worst admissible
configuration is the aligned one `A = 1`, `q = 3/4`, `p = -√(Aq)` (there `|4p²+2pq−qA|/(qB) ≈ 70.6`),
so the constant `100` has ≈ 40% slack.
-/

/-- Case `0 ≤ 2p + q` of the scalar core. -/
private lemma taylor_aux_I {A q p : ℝ} (hA : 1 ≤ A) (hq0 : 0 ≤ q) (hq4 : q ≤ 3 / 4)
    (hp : p ^ 2 ≤ A * q) (hu : 0 ≤ 2 * p + q) :
    (2 * p + q) ^ 2 ≤ 101 * q * (A + 2 * p + q) := by
  have hA0 : 0 ≤ A := by linarith
  have hqA : 4 * q ≤ 3 * A := by nlinarith
  have hAM : 0 ≤ A + q := by linarith
  have h4p : (2 * |p|) ^ 2 ≤ (A + q) ^ 2 := by
    have e : (2 * |p|) ^ 2 = 4 * p ^ 2 := by rw [mul_pow, sq_abs]; ring
    nlinarith [sq_nonneg (A - q), hp]
  have h2p : 2 * |p| ≤ A + q := by
    have h := sq_le_sq.mp h4p
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (abs_nonneg p),
      abs_of_nonneg hAM] at h
    exact h
  have hpq : 4 * p * q ≤ 2 * A * q + 2 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h2p (by linarith : (0 : ℝ) ≤ 2 * q)
    have h' : 4 * p * q ≤ 4 * |p| * q := by
      have := mul_le_mul_of_nonneg_right (le_abs_self p) hq0
      linarith
    nlinarith [h, h']
  nlinarith [hu, hq0, hp, hpq, hqA, hA]

/-- Case `2p + q < 0` of the scalar core.  Here `t := -2p > q` and `t² = 4p² ≤ 4Aq`; the remaining
ingredient is the squaring estimate `99t ≤ 97A + 100q`, which follows from
`39204 A q ≤ (97A + 100q)²` and `4q ≤ 3A`. -/
private lemma taylor_aux_II {A q p : ℝ} (hA : 1 ≤ A) (hq0 : 0 ≤ q) (hq4 : q ≤ 3 / 4)
    (hp : p ^ 2 ≤ A * q) (hu : 2 * p + q < 0) :
    (2 * p + q) ^ 2 ≤ 101 * q * (A + 2 * p + q) := by
  have hA0 : 0 ≤ A := by linarith
  have hqA : 4 * q ≤ 3 * A := by nlinarith
  have ht0 : 0 ≤ -2 * p := by linarith
  have ht2 : (-2 * p) ^ 2 ≤ 4 * A * q := by nlinarith [hp]
  have hquad : 0 ≤ 9409 * A ^ 2 - 19804 * A * q + 10000 * q ^ 2 := by
    have h1 : 0 ≤ (q - 3 / 4 * A) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 4 * A * (946 * A - 1201 * q) := by
      apply mul_nonneg (by linarith) (by nlinarith [hqA])
    nlinarith [h1, h2]
  have h99 : 99 * (-2 * p) ≤ 97 * A + 100 * q := by
    have hsq : (99 * (-2 * p)) ^ 2 ≤ (97 * A + 100 * q) ^ 2 := by
      have h1 : (99 * (-2 * p)) ^ 2 = 9801 * 4 * p ^ 2 := by ring
      have h2 : 9801 * 4 * p ^ 2 ≤ 9801 * 4 * A * q := by nlinarith [hp]
      have h3 : 9801 * 4 * A * q ≤ (97 * A + 100 * q) ^ 2 := by nlinarith [hquad]
      linarith
    have h := sq_le_sq.mp hsq
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 99 * (-2 * p)),
      abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 97 * A + 100 * q)] at h
    exact h
  nlinarith [h99, ht2, hu, hq0]

/-- The scalar core: for `A ≥ 1`, `0 ≤ q ≤ 3/4` and `p² ≤ A q`,
`(2p + q)² ≤ 101 q (A + 2p + q)`. -/
private lemma taylor_key_ineq {A q p : ℝ} (hA : 1 ≤ A) (hq0 : 0 ≤ q) (hq4 : q ≤ 3 / 4)
    (hp : p ^ 2 ≤ A * q) :
    (2 * p + q) ^ 2 ≤ 101 * q * (A + 2 * p + q) := by
  rcases le_or_gt 0 (2 * p + q) with hu | hu
  · exact taylor_aux_I hA hq0 hq4 hp hu
  · exact taylor_aux_II hA hq0 hq4 hp hu

theorem taylorRemainderNorm {b w : E3} (hb : 1 ≤ ‖b‖) (hw : ∀ i : Fin 3, |w.ofLp i| ≤ 1 / 2) :
    |1 / ‖b + w‖ ^ 2 - 1 / ‖b‖ ^ 2 + 2 * inner ℝ b w / ‖b‖ ^ 4| ≤ 100 * ‖w‖ ^ 2 / ‖b‖ ^ 4 := by
  set A : ℝ := ‖b‖ ^ 2 with hAdef
  set q : ℝ := ‖w‖ ^ 2 with hqdef
  set p : ℝ := inner ℝ b w with hpdef
  set B : ℝ := ‖b + w‖ ^ 2 with hBdef
  have hA1 : 1 ≤ A := by rw [hAdef]; nlinarith [hb, norm_nonneg b]
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq4 : q ≤ 3 / 4 := by
    rw [hqdef, EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖w.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs]
          have hi : |w.ofLp i| ≤ 1 / 2 := hw i
          have hnn : 0 ≤ |w.ofLp i| := abs_nonneg _
          have hprod : |w.ofLp i| * |w.ofLp i| ≤ (1 / 2 : ℝ) * (1 / 2) :=
            mul_le_mul hi hi hnn (by norm_num)
          simpa [sq] using hprod
      _ = 3 / 4 := by rw [Fin.sum_univ_three]; norm_num
  have hp : p ^ 2 ≤ A * q := by
    rw [hpdef, hAdef, hqdef]
    have h := real_inner_mul_inner_self_le b w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    simpa [sq] using h
  have hB : B = A + 2 * p + q := by
    rw [hBdef, hAdef, hqdef, hpdef, norm_add_sq_real]
  have hBpos : 0 < B := by
    rw [hBdef]
    refine sq_pos_of_ne_zero ?_
    intro h
    have h1 : b + w = 0 := norm_eq_zero.mp h
    have h2 : b = -w := eq_neg_iff_add_eq_zero.mpr h1
    have h3 : ‖b‖ = ‖w‖ := by rw [h2, norm_neg]
    have h4 : 1 ≤ ‖b‖ ^ 2 := by nlinarith [hb, norm_nonneg b]
    have h5 : q = ‖b‖ ^ 2 := by rw [hqdef, h3]
    linarith [hq4, h4, h5]
  have hkey : (2 * p + q) ^ 2 ≤ 101 * q * B := by
    rw [hB]; exact taylor_key_ineq hA1 hq0 hq4 hp
  have hN : |4 * p ^ 2 + 2 * p * q - q * A| ≤ 100 * q * B := by
    have hqB : 0 ≤ q * B := mul_nonneg hq0 (le_of_lt hBpos)
    have h1 : (2 * p + q) ^ 2 - q * B ≤ 100 * q * B := by nlinarith [hkey]
    have h2 : -(100 * q * B) ≤ (2 * p + q) ^ 2 - q * B := by
      nlinarith [sq_nonneg (2 * p + q), hqB]
    have he : 4 * p ^ 2 + 2 * p * q - q * A = (2 * p + q) ^ 2 - q * B := by
      rw [hB]; ring
    rw [he]
    exact abs_le.mpr ⟨h2, h1⟩
  have hId : (1 / B - 1 / A + 2 * p / A ^ 2) * A ^ 2
      = (4 * p ^ 2 + 2 * p * q - q * A) / B := by
    have hA0' : A ≠ 0 := ne_of_gt hA0
    have hB0' : A + 2 * p + q ≠ 0 := by rw [← hB]; exact ne_of_gt hBpos
    rw [hB]
    field_simp
    ring
  have hfinal : |1 / B - 1 / A + 2 * p / A ^ 2| * A ^ 2 ≤ 100 * q := by
    have h1 : |1 / B - 1 / A + 2 * p / A ^ 2| * A ^ 2
        = |(4 * p ^ 2 + 2 * p * q - q * A) / B| := by
      calc |1 / B - 1 / A + 2 * p / A ^ 2| * A ^ 2
          = |1 / B - 1 / A + 2 * p / A ^ 2| * |A ^ 2| := by
            rw [abs_of_nonneg (sq_nonneg A)]
        _ = |(1 / B - 1 / A + 2 * p / A ^ 2) * A ^ 2| := by rw [abs_mul]
        _ = |(4 * p ^ 2 + 2 * p * q - q * A) / B| := by rw [hId]
    rw [h1, abs_div, abs_of_pos hBpos]
    rw [div_le_iff₀ hBpos]
    exact hN
  have hgoal : |1 / B - 1 / A + 2 * p / A ^ 2| ≤ 100 * q / A ^ 2 := by
    rw [le_div_iff₀ (pow_pos hA0 2)]
    exact hfinal
  have hAeq : ‖b‖ ^ 4 = A ^ 2 := by rw [hAdef]; ring
  rw [hAeq]
  exact hgoal

end Work.BoseRowsL.LatticeCoulomb
