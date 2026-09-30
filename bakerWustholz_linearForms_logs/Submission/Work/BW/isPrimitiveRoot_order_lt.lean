import Mathlib
import Submission.Work.BW.totient_mul_logb_add_one_ge
import Submission.Work.BW.logb_order_bound_numeric
import Submission.Work.BW.div_logb2_add_one_mono

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

namespace Work.BW

/-- The order of a root of unity in a number field is bounded polynomially in the degree:
a primitive `k`-th root of unity `β` in `K` satisfies `k < 120 π d log(6d)`, `d = [K : ℚ]`.

From `φ(k) = [ℚ(ζ_k):ℚ] ≤ d` (`Polynomial.cyclotomic_eq_minpoly`, `natDegree_cyclotomic`) and the
elementary bound `k ≤ φ(k) · (log₂ k + 1)`. -/
theorem isPrimitiveRoot_order_lt {K : Type*} [Field K] [NumberField K] (β : K) (k : ℕ)
    (hk : 0 < k) (hβ : IsPrimitiveRoot β k) :
    (k : ℝ) < 120 * Real.pi * (Module.finrank ℚ K : ℝ) *
      Real.log (6 * (Module.finrank ℚ K : ℝ)) := by
  -- `d = [K : ℚ]`
  set d : ℕ := Module.finrank ℚ K with hd
  -- Step 1: `φ(k) = [ℚ(β):ℚ] ≤ d`.
  have htot' : Nat.totient k ≤ Module.finrank ℚ K := by
    have hmin : minpoly ℚ β = cyclotomic k ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hβ hk).symm
    have hdeg : (minpoly ℚ β).natDegree = Nat.totient k := by
      rw [hmin, Polynomial.natDegree_cyclotomic]
    have hle : (minpoly ℚ β).natDegree ≤ Module.finrank ℚ K := minpoly.natDegree_le β
    exact hdeg ▸ hle
  have htot : (Nat.totient k : ℕ) ≤ d := by simpa [← hd] using htot'
  have htotR : (Nat.totient k : ℝ) ≤ (d : ℝ) := by exact_mod_cast htot
  -- Step 2: `k ≤ φ(k) · (log₂ k + 1) ≤ d · (log₂ k + 1)`.
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ Real.logb 2 (k : ℝ) := Real.logb_nonneg (by norm_num) hk1
  have hkpos : 0 < Real.logb 2 (k : ℝ) + 1 := by linarith
  have hmain : (k : ℝ) ≤ (d : ℝ) * (Real.logb 2 (k : ℝ) + 1) :=
    le_trans (totient_mul_logb_add_one_ge k hk)
      (mul_le_mul_of_nonneg_right htotR (by linarith))
  -- `d ≥ 1`.
  have hd0 : 0 < d := by rw [hd]; exact Module.finrank_pos (R := ℚ) (M := K)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  -- `L := 120 π d log(6d)` is `≥ exp 1`.
  set L : ℝ := 120 * Real.pi * (d : ℝ) * Real.log (6 * (d : ℝ)) with hLdef
  have h6d : (0 : ℝ) < 6 * (d : ℝ) := by linarith
  have hlog6d : (1 : ℝ) ≤ Real.log (6 * (d : ℝ)) := by
    rw [Real.le_log_iff_exp_le h6d]
    linarith [Real.exp_one_lt_three]
  have hbig : (360 : ℝ) ≤ L := by
    rw [hLdef]
    have hπ : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hπ3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    have hA : (3 : ℝ) ≤ Real.pi * (d : ℝ) := by
      have hh := mul_le_mul hπ3 hd1 (by norm_num : (0 : ℝ) ≤ 1) hπ
      linarith [hh]
    have hB : (3 : ℝ) ≤ Real.pi * (d : ℝ) * Real.log (6 * (d : ℝ)) := by
      have hh := mul_le_mul hA hlog6d (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ Real.pi * (d : ℝ))
      linarith [hh]
    nlinarith [hB]
  have hexp1L : Real.exp 1 ≤ L := by linarith [Real.exp_one_lt_three, hbig]
  have h1L : (1 : ℝ) ≤ L := le_trans (Real.one_le_exp (by norm_num)) hexp1L
  have hL0 : (0 : ℝ) ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) h1L
  have hLpos : 0 < Real.logb 2 L + 1 := by linarith
  -- Step 3: `x ↦ x/(log₂ x + 1)` is monotone on `[exp 1, ∞)`, so `k ≥ L` is impossible.
  have hdiv_k : (k : ℝ) / (Real.logb 2 (k : ℝ) + 1) ≤ (d : ℝ) := by
    rw [div_le_iff₀ hkpos]; exact hmain
  have hthis : Real.logb 2 L + 1 < 120 * Real.pi * Real.log (6 * (d : ℝ)) := by
    rw [hLdef]; exact logb_order_bound_numeric (d : ℝ) hd1
  have hd_lt : (d : ℝ) < L / (Real.logb 2 L + 1) := by
    have hmul : (d : ℝ) * (Real.logb 2 L + 1)
        < (d : ℝ) * (120 * Real.pi * Real.log (6 * (d : ℝ))) :=
      mul_lt_mul_of_pos_left hthis (by linarith)
    have hR : (d : ℝ) * (120 * Real.pi * Real.log (6 * (d : ℝ))) = L := by
      rw [hLdef]; ring
    rw [hR] at hmul
    rw [lt_div_iff₀ hLpos]
    exact hmul
  by_contra hcon
  have hcon' : L ≤ (k : ℝ) := le_of_not_gt hcon
  have hmono := div_logb2_add_one_mono hexp1L hcon'
  linarith

end Work.BW
