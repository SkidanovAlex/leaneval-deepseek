import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.tendsto_wOf_atTop

/-!
# `W(w(B)) · (log B)^m · κ ≤ B^{1/(n+1-d)}` eventually in `B`

Since `d ≤ n`, the exponent `e = 1/((n : ℝ) + 1 - d)` is strictly positive.
We split the left-hand side into three factors and bound each by `B^{e/3}`:

* `bigW (wOf B) ≤ B^{e/3}` eventually — this is `bigW_le_pow`;
* `(log B)^m ≤ B^{e/3}` eventually — `log^m = o (B^{e/3})`
  (`isLittleO_log_rpow_rpow_atTop`), and a `log` is eventually positive;
* `κ ≤ B^{e/3}` eventually — `B ↦ B^{e/3}` tends to `∞` (`tendsto_rpow_atTop`).

Multiplying the three bounds and using `B^a * B^b = B^{a+b}` gives the claim.
-/

namespace Work.HP.HP2

theorem PF_eventually (d n : ℕ) (hdn : d ≤ n) (m : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ B in Filter.atTop,
      1 ≤ Real.log B ∧
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ
          ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := by
  have hd : (d : ℝ) ≤ n := by exact_mod_cast hdn
  set e := 1 / ((n : ℝ) + 1 - d) with he_
  have he3 : 0 < e / 3 := by
    rw [he_]; exact div_pos (one_div_pos.mpr (by linarith)) (by norm_num)
  -- `log B ≥ 1` eventually.
  have h1 : ∀ᶠ B in Filter.atTop, (1 : ℝ) ≤ Real.log B :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  -- `W(w(B)) ≤ B^{e/3}` eventually.
  have hW : ∀ᶠ B in Filter.atTop, (Work.HP.bigW (Work.HP.wOf B) : ℝ) ≤ B ^ (e / 3) := by
    obtain ⟨B₀, hB₀⟩ := Work.HP.bigW_le_pow (e / 3) he3
    exact Filter.eventually_atTop.mpr ⟨B₀, hB₀⟩
  -- `(log B)^m ≤ B^{e/3}` eventually.
  have hlog : ∀ᶠ B in Filter.atTop, (Real.log B) ^ m ≤ B ^ (e / 3) := by
    have h : (fun x : ℝ => Real.log x ^ m) =o[Filter.atTop] fun x => x ^ (e / 3) := by
      simpa using isLittleO_log_rpow_rpow_atTop (m : ℝ) he3
    filter_upwards [h.eventuallyLE, Filter.eventually_gt_atTop (1 : ℝ)] with B hB hB1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (le_of_lt (Real.log_pos hB1)) m),
        abs_of_pos (Real.rpow_pos_of_pos (by linarith) (e / 3))] at hB
    exact hB
  -- `κ ≤ B^{e/3}` eventually.
  have hk : ∀ᶠ B in Filter.atTop, κ ≤ B ^ (e / 3) :=
    (tendsto_rpow_atTop he3).eventually_ge_atTop κ
  have hBpos : ∀ᶠ B in Filter.atTop, (0 : ℝ) < B := Filter.eventually_gt_atTop 0
  filter_upwards [h1, hW, hlog, hk, hBpos] with B h1 hW hlog hk hBpos
  refine ⟨h1, ?_⟩
  have hlognn : (0 : ℝ) ≤ (Real.log B) ^ m := pow_nonneg (by linarith) m
  have hPpos : 0 < B ^ (e / 3) := Real.rpow_pos_of_pos hBpos _
  have hPnn : 0 ≤ B ^ (e / 3) := le_of_lt hPpos
  calc (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ
      ≤ B ^ (e / 3) * B ^ (e / 3) * B ^ (e / 3) := by
        apply mul_le_mul
        · exact mul_le_mul hW hlog hlognn hPnn
        · exact hk
        · exact le_of_lt hκ
        · exact mul_nonneg hPnn hPnn
    _ = B ^ e := by
        rw [← Real.rpow_add hBpos, ← Real.rpow_add hBpos]
        rw [show e / 3 + e / 3 + e / 3 = e by ring]
    _ = B ^ (1 / ((n : ℝ) + 1 - d)) := by rw [he_]

end Work.HP.HP2
