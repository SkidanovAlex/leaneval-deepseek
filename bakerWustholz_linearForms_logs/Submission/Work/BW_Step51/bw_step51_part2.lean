import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW_Step51

/-- Auxiliary arithmetic: a clean rewrite for `32^(r+1)`. -/
private lemma bw51_pow32 (r : ℕ) : ((32 : ℝ) ^ (r + 1)) = (2 : ℝ) ^ (5 * r + 5) := by
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_mul, show 5 * (r + 1) = 5 * r + 5 by ring]

/-- Auxiliary arithmetic: a clean rewrite for `64^(r+2)`. -/
private lemma bw51_pow64 (r : ℕ) : ((64 : ℝ) ^ (r + 2)) = 4 * (2 : ℝ) ^ (6 * r + 10) := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul,
    show 6 * (r + 2) = (6 * r + 10) + 2 by ring, pow_add]
  norm_num
  ring

/-- Auxiliary arithmetic: folding `2^(6r+10)` back into the products appearing in `pD`. -/
private lemma bw51_pow2 (r : ℕ) :
    (2 : ℝ) ^ (6 * r + 10) = (2 : ℝ) ^ r * (2 : ℝ) ^ (5 * r + 5) * 32 := by
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, ← pow_add, ← pow_add,
    show r + (5 * r + 5) + 5 = 6 * r + 10 by ring]

theorem bw_step51_part2 (n d r v : ℕ) (c H : ℝ) (σ : Fin r → ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hσ : ∀ j, 0 < σ j)
    (hp : (Work.BW.ph H v : ℝ) ≤ (n + 1) * H * max (2 ^ v / c) 1) :
    9 * 2 ^ r * (Work.BW.pS r d (Work.BW.ph H v) : ℝ) * Work.BW.pD r d σ
      ≤ Work.BW.kappa' n d r v c * H * ∏ j, σ j := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h32 := bw51_pow32 r
  have h64 := bw51_pow64 r
  have hrr : (↑r : ℝ) ^ (r + 1) = ↑r * ↑r ^ r := by rw [pow_succ']
  have hdd : (↑d : ℝ) ^ (r + 2) = ↑d * ↑d ^ (r + 1) := by rw [pow_succ']
  have h2 := bw51_pow2 r
  rw [Work.BW.kappa', Work.BW.pD, Work.BW.pS]
  push_cast
  have hlog : 0 < Real.log (2 * ↑r * ↑d) := by
    apply Real.log_pos
    nlinarith [hr', hd']
  have hprod : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσ j)
  have hrp : (0 : ℝ) < (r : ℝ) ^ (r + 1) := by positivity
  have hdp : (0 : ℝ) < (d : ℝ) ^ (r + 2) := by positivity
  have h2p : (0 : ℝ) < (2 : ℝ) ^ (6 * r + 10) := by positivity
  have hA : 0 < (2 : ℝ) ^ (6 * r + 10) *
      (9 * ↑r ^ (r + 1) * ↑d ^ (r + 2) * Real.log (2 * ↑r * ↑d) * ∏ j, σ j) := by
    positivity
  have eL : 9 * 2 ^ r * (16 * ↑r * ↑d * ↑(Work.BW.ph H v)) *
        (2 * ↑r ^ r * (32 * ↑d) ^ (r + 1) * Real.log (2 * ↑r * ↑d) * ∏ j, σ j)
      = (2 : ℝ) ^ (6 * r + 10) *
          (9 * ↑r ^ (r + 1) * ↑d ^ (r + 2) * Real.log (2 * ↑r * ↑d) * ∏ j, σ j) *
          ↑(Work.BW.ph H v) := by
    simp only [mul_pow]
    rw [h32, hrr, hdd, h2]
    ring
  have eR : (9 / 4) * (↑n + 1) * ↑r ^ (r + 1) * (64 * ↑d) ^ (r + 2) *
        Real.log (2 * ↑r * ↑d) * max (2 ^ v / c) 1 * H * ∏ j, σ j
      = (2 : ℝ) ^ (6 * r + 10) *
          (9 * ↑r ^ (r + 1) * ↑d ^ (r + 2) * Real.log (2 * ↑r * ↑d) * ∏ j, σ j) *
          ((↑n + 1) * H * max (2 ^ v / c) 1) := by
    simp only [mul_pow]
    rw [h64, h2]
    ring
  rw [eL, eR]
  exact mul_le_mul_of_nonneg_left hp hA.le

end Work.BW_Step51
