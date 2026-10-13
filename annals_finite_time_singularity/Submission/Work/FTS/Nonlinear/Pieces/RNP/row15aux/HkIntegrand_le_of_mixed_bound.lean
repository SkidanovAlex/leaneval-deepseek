import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

/-- `(s^{q/2})² = s^q` for `s ≥ 0`. -/
private lemma rpow_half_sq {s q : ℝ} (hs : 0 ≤ s) : (s ^ (q / 2)) ^ 2 = s ^ q := by
  rw [← Real.rpow_natCast (s ^ (q / 2)) 2, ← Real.rpow_mul hs]
  ring

/-- `(s^{-q/2})² = s^{-q}` for `s ≥ 0`. -/
private lemma rpow_neg_half_sq {s q : ℝ} (hs : 0 ≤ s) : (s ^ (-(q / 2))) ^ 2 = s ^ (-q) := by
  rw [← Real.rpow_natCast (s ^ (-(q / 2))) 2, ← Real.rpow_mul hs]
  ring

/-- `(a / s^{q/2})² = a²·s^{-q}` for `s ≥ 0`. -/
private lemma sq_div_rpow_half {a s q : ℝ} (hs : 0 ≤ s) :
    (a / s ^ (q / 2)) ^ 2 = a ^ 2 * s ^ (-q) := by
  rw [div_pow, rpow_half_sq hs, div_eq_mul_inv, ← Real.rpow_neg hs]

/-- `(a·s^{-q/2})² = a²·s^{-q}` for `s ≥ 0`. -/
private lemma sq_mul_rpow_neg_half {a s q : ℝ} (hs : 0 ≤ s) :
    (a * s ^ (-(q / 2))) ^ 2 = a ^ 2 * s ^ (-q) := by
  rw [mul_pow, rpow_neg_half_sq hs]

theorem HkIntegrand_le_of_mixed_bound {α K Cs : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hK : 0 < K) (hCs : 0 ≤ Cs) {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (h : ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
      |Work.Spaces.mixed j i f z θ * Work.Spaces.w z|
        ≤ K * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ
            * Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog z)
    (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 f z θ
      ≤ (K * α ^ 3 * (Cs + 1)) ^ 2 * (Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog z) ^ 2
          * Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gwt α θ := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hGam0 : 0 ≤ Gam α θ := (Gam_bounds α θ hα hθ).1
  have hrlog0 : 0 ≤ rlog z := rlog_nonneg hz0
  set B : ℝ := K * α ^ 3 * (Cs + 1) * Gam α θ * rlog z with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hK)
      (pow_nonneg (le_of_lt hα) 3)) (by linarith)) hGam0) hrlog0
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have hsinη : 0 ≤ Real.sin (2 * θ) ^ (-eta) := Real.rpow_nonneg hs _
  have hsinγ : 0 ≤ Real.sin (2 * θ) ^ (-gam α) := Real.rpow_nonneg hs _
  -- per-term bounds
  have hDzterm : ∀ i ∈ Finset.range 5,
      (DzIter i f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        ≤ B ^ 2 * Real.sin (2 * θ) ^ (-eta) := by
    intro i hi
    have hi4 : 0 + i ≤ 4 := by
      have := Finset.mem_range.mp hi; omega
    have ha : |mixed i 0 f z θ * w z| ≤ B := by
      rw [hB]; exact h θ hθ 0 i hi4
    have ha2 : (DzIter i f z θ * w z) ^ 2 ≤ B ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hB0] using ha)
    calc (DzIter i f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        = (DzIter i f z θ * w z) ^ 2 * Real.sin (2 * θ) ^ (-eta) := by
          rw [← mul_div_assoc, sq_div_rpow_half hs]
      _ ≤ B ^ 2 * Real.sin (2 * θ) ^ (-eta) := mul_le_mul_of_nonneg_right ha2 hsinη
  have hMxterm : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ B ^ 2 * Real.sin (2 * θ) ^ (-gam α) := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [ite_eq_left hc]
      have ha : |mixed j i f z θ * w z| ≤ B := by
        rw [hB]; exact h θ hθ i j hc.2
      have ha2 : (mixed j i f z θ * w z) ^ 2 ≤ B ^ 2 :=
        sq_le_sq.mpr (by simpa [abs_of_nonneg hB0] using ha)
      calc (mixed j i f z θ * Wt α z θ) ^ 2
          = (mixed j i f z θ * w z) ^ 2 * Real.sin (2 * θ) ^ (-gam α) := by
            rw [Wt, wTheta, ← mul_assoc, sq_mul_rpow_neg_half hs]
        _ ≤ B ^ 2 * Real.sin (2 * θ) ^ (-gam α) :=
            mul_le_mul_of_nonneg_right ha2 hsinγ
    · rw [ite_eq_right hc]
      exact mul_nonneg hB2 hsinγ
  -- sum bounds
  have hsum1 : (∑ i ∈ Finset.range 5,
        (DzIter i f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2)
      ≤ 5 * (B ^ 2 * Real.sin (2 * θ) ^ (-eta)) := by
    calc (∑ i ∈ Finset.range 5,
          (DzIter i f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range 5, (B ^ 2 * Real.sin (2 * θ) ^ (-eta)) :=
          Finset.sum_le_sum (fun i hi => hDzterm i hi)
      _ = 5 * (B ^ 2 * Real.sin (2 * θ) ^ (-eta)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
      ≤ 25 * (B ^ 2 * Real.sin (2 * θ) ^ (-gam α)) := by
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (B ^ 2 * Real.sin (2 * θ) ^ (-gam α)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact Finset.sum_le_sum (fun j hj => hMxterm i hi j hj)
      _ = 25 * (B ^ 2 * Real.sin (2 * θ) ^ (-gam α)) := by
          rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
  calc HkIntegrand α 4 f z θ
      = (∑ i ∈ Finset.range 5,
            (DzIter i f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2)
        + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0) := rfl
    _ ≤ 5 * (B ^ 2 * Real.sin (2 * θ) ^ (-eta))
          + 25 * (B ^ 2 * Real.sin (2 * θ) ^ (-gam α)) := add_le_add hsum1 hsum2
    _ ≤ B ^ 2 * (5 * Real.sin (2 * θ) ^ (-eta) + 30 * Real.sin (2 * θ) ^ (-gam α)) := by
        have hY : 0 ≤ B ^ 2 * Real.sin (2 * θ) ^ (-gam α) := mul_nonneg hB2 hsinγ
        have hR : B ^ 2 * (5 * Real.sin (2 * θ) ^ (-eta) + 30 * Real.sin (2 * θ) ^ (-gam α))
            = 5 * (B ^ 2 * Real.sin (2 * θ) ^ (-eta))
              + 30 * (B ^ 2 * Real.sin (2 * θ) ^ (-gam α)) := by ring
        rw [hR]; linarith
    _ = (K * α ^ 3 * (Cs + 1)) ^ 2 * (rlog z) ^ 2 * Gwt α θ := by
        rw [hB, Gwt]; ring

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
