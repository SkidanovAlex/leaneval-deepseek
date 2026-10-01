import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

/-!
# `cellLayer` as a threshold indicator in terms of `Nat.clog`

`cellLayer R m k = 1{R ≤ 2^k and m ≤ 2^k}` is the same as `1{clog 2 (max R m) ≤ k}`,
since `clog 2 (max R m)` is the least `k` with `max R m ≤ 2^k`.
-/

namespace Work.LinnikAreas.JMAux

lemma CellLayerEqClogIcc (R m k : ℕ) :
    Work.LinnikAreas.cellLayer R m k
      = (if Nat.clog 2 (max R m) ≤ k then (1:ℝ) else 0) := by
  rw [Work.LinnikAreas.cellLayer]
  have h2 : (1:ℕ) < 2 := by norm_num
  have hpow : ((2:ℝ)^k) = ((2^k : ℕ) : ℝ) := by push_cast; ring
  have hiff : ((R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k) ↔ Nat.clog 2 (max R m) ≤ k := by
    rw [hpow, Nat.clog_le_iff_le_pow h2]
    constructor
    · intro ⟨hR, hm⟩
      exact max_le (by exact_mod_cast hR) (by exact_mod_cast hm)
    · intro h
      exact ⟨by exact_mod_cast le_trans (le_max_left _ _) h,
             by exact_mod_cast le_trans (le_max_right _ _) h⟩
  by_cases h : Nat.clog 2 (max R m) ≤ k
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

end Work.LinnikAreas.JMAux
