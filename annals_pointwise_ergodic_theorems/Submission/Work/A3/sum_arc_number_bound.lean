import Mathlib

set_option linter.unusedVariables false

namespace Work.A3

/--
The number of arcs at scale `q ≤ M` weighted by `q + 3`, with the weight `q ^ (-(2 s δ))`, has
uniformly bounded partial sums as soon as `s δ > 1` (so that the exponent `2 s δ` exceeds `2`).
This is the elementary summability used to count arcs in the circle-method bookkeeping.
-/
theorem sum_arc_number_bound {δ : ℝ} (hδ : 0 < δ) {s : ℕ} (hsδ : 1 < (s : ℝ) * δ) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ M : ℕ,
      ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) * (q : ℝ) ^ (-(2 * (s : ℝ) * δ)) ≤ K' := by
  set a : ℝ := 2 * (s : ℝ) * δ with ha
  have ha2 : 2 < a := by
    rw [ha]
    have h : (2 : ℝ) * ((s : ℝ) * δ) = 2 * (s : ℝ) * δ := by ring
    linarith [hsδ]
  have hb1 : 1 < a - 1 := by linarith
  have hmaj : Summable (fun q : ℕ => 4 * (q : ℝ) ^ (-(a - 1))) := by
    refine (Real.summable_nat_rpow_inv.mpr hb1).congr (fun q => ?_) |>.mul_left 4
    exact (Real.rpow_neg (Nat.cast_nonneg q) (a - 1)).symm
  refine ⟨(∑' q : ℕ, 4 * (q : ℝ) ^ (-(a - 1))) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ ∑' q : ℕ, 4 * (q : ℝ) ^ (-(a - 1)) :=
      tsum_nonneg fun q => mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    linarith
  · intro M
    have hpt : ∀ q ∈ Finset.Icc 1 M,
        ((q : ℝ) + 3) * (q : ℝ) ^ (-a) ≤ 4 * (q : ℝ) ^ (-(a - 1)) := by
      intro q hq
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        exact_mod_cast this
      have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
      have h1 : (q : ℝ) + 3 ≤ 4 * (q : ℝ) := by linarith
      have h2 : (0 : ℝ) ≤ (q : ℝ) ^ (-a) := Real.rpow_nonneg hqpos.le _
      have key : (q : ℝ) ^ (-(a - 1)) = (q : ℝ) * (q : ℝ) ^ (-a) := by
        rw [show -(a - 1) = 1 + (-a) by ring, Real.rpow_add hqpos, Real.rpow_one]
      calc ((q : ℝ) + 3) * (q : ℝ) ^ (-a)
          ≤ (4 * (q : ℝ)) * (q : ℝ) ^ (-a) := mul_le_mul_of_nonneg_right h1 h2
        _ = 4 * ((q : ℝ) * (q : ℝ) ^ (-a)) := by ring
        _ = 4 * (q : ℝ) ^ (-(a - 1)) := by rw [key]
    calc ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) + 3) * (q : ℝ) ^ (-a)
        ≤ ∑ q ∈ Finset.Icc 1 M, 4 * (q : ℝ) ^ (-(a - 1)) := Finset.sum_le_sum hpt
      _ ≤ ∑' q : ℕ, 4 * (q : ℝ) ^ (-(a - 1)) :=
          hmaj.sum_le_tsum _ fun q _ =>
            mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      _ ≤ (∑' q : ℕ, 4 * (q : ℝ) ^ (-(a - 1))) + 1 := by linarith

end Work.A3
