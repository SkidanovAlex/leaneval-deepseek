import Mathlib
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.tendsto_wOf_atTop
import Submission.Work.HP.HP2.PF_eventually

set_option autoImplicit false

open Filter

namespace Work.ClassCount

/-- **Eventual tube/tail threshold.**  For `d ≤ n`, `n ≥ 1`, `m : ℕ`, `0 < κ`, `0 < Cstar`,
eventually in `B`,

`W^{2 + 1/n} · (log B)^{m+1} · κ ≤ B^{1/((n:ℝ)+1-d)} · Cstar`,  where `W = bigW (wOf B)`.

Route: `bigW_le_pow` gives `W ≤ B^δ` eventually for any `δ > 0`, hence
`W^{(2n+1)/n} ≤ B^{δ(2n+1)/n}`; `isLittleO_log_rpow_rpow_atTop` gives `(log B)^{m+1} ≤ B^{δ'}`
eventually, and `κ ≤ B^{δ'}` eventually (`tendsto_rpow_atTop`).  Choose `δ, δ' > 0` small enough that
`δ(2n+1)/n + 2δ' < 1/((n:ℝ)+1-d)` (possible since the target exponent is positive: `d ≤ n` gives
`(n:ℝ)+1-d ≥ 1`, so it lies in `[1/(n+1), 1]`), then multiply the three bounds and use
`Real.rpow_add`; the final `≤ B^{1/((n:ℝ)+1-d)} · Cstar` holds for large `B` because the exponent
difference is negative while `0 < Cstar`. -/
theorem tube_tail_eventually (d n : ℕ) (hdn : d ≤ n) (hn : 1 ≤ n) (m : ℕ) (κ Cstar : ℝ)
    (hκ : 0 < κ) (hC : 0 < Cstar) :
    ∀ᶠ B in atTop,
      (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ ((2 * (n : ℝ) + 1) / n)
        * (Real.log B) ^ (m + 1) * κ
        ≤ B ^ (1 / ((n : ℝ) + 1 - d)) * Cstar := by
  have hd : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- The target exponent `e = 1/((n : ℝ) + 1 - d)` is positive.
  set e : ℝ := 1 / ((n : ℝ) + 1 - d) with he
  have hepos : 0 < e := by
    rw [he]; exact one_div_pos.mpr (by linarith)
  -- The exponent `p = (2n+1)/n` on `W`.
  set p : ℝ := (2 * (n : ℝ) + 1) / n with hp
  have hppos : 0 < p := by
    rw [hp]; exact div_pos (by linarith) hnpos
  have hpne : p ≠ 0 := ne_of_gt hppos
  -- ## Step 1: `W^p ≤ B^{e/2}` eventually.
  have hW : ∀ᶠ B in atTop,
      (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ p ≤ B ^ (e / 2) := by
    have hδ : 0 < e / (2 * p) := div_pos hepos (by positivity)
    obtain ⟨B₁, hB₁⟩ := Work.HP.bigW_le_pow (e / (2 * p)) hδ
    filter_upwards
      [eventually_atTop.mpr ⟨max B₁ 1, fun B hB => hB₁ B (le_trans (le_max_left _ _) hB)⟩,
        eventually_gt_atTop (0 : ℝ)] with B hWB hBpos
    have hWnn : (0 : ℝ) ≤ (Work.HP.bigW (Work.HP.wOf B) : ℝ) := Nat.cast_nonneg _
    calc (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ p
        ≤ (B ^ (e / (2 * p))) ^ p := Real.rpow_le_rpow hWnn hWB (le_of_lt hppos)
      _ = B ^ ((e / (2 * p)) * p) := by rw [Real.rpow_mul (le_of_lt hBpos)]
      _ = B ^ (e / 2) := by
            congr 1
            field_simp
  -- ## Step 2: `(log B)^{m+1} ≤ B^{e/8}` eventually.
  have hlog : ∀ᶠ B in atTop, (Real.log B) ^ (m + 1) ≤ B ^ (e / 8) := by
    have he8 : 0 < e / 8 := by positivity
    have h : (fun x : ℝ => Real.log x ^ (((m + 1 : ℕ) : ℝ)))
        =o[atTop] fun x => x ^ (e / 8) :=
      isLittleO_log_rpow_rpow_atTop _ he8
    filter_upwards [h.eventuallyLE, eventually_gt_atTop (1 : ℝ)] with B hle hB1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (Real.log_pos hB1)) _),
        abs_of_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < B) _)] at hle
    rwa [Real.rpow_natCast] at hle
  -- ## Step 3: `κ ≤ B^{e/8}` eventually.
  have hk : ∀ᶠ B in atTop, κ ≤ B ^ (e / 8) := by
    have he8 : 0 < e / 8 := by positivity
    exact (tendsto_rpow_atTop he8).eventually_ge_atTop κ
  -- ## Step 4: `B^{3e/4} ≤ B^e * Cstar` eventually.
  have hlarge : ∀ᶠ B in atTop, B ^ (3 * e / 4) ≤ B ^ e * Cstar := by
    have he4 : 0 < e / 4 := by positivity
    have h : ∀ᶠ B in atTop, (1 : ℝ) / Cstar ≤ B ^ (e / 4) :=
      (tendsto_rpow_atTop he4).eventually_ge_atTop (1 / Cstar)
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with B hB hBpos
    have h3 : (0 : ℝ) < B ^ (3 * e / 4) := Real.rpow_pos_of_pos hBpos _
    have h4 : (0 : ℝ) < B ^ (e / 4) := Real.rpow_pos_of_pos hBpos _
    have hCs : 1 ≤ Cstar * B ^ (e / 4) := by
      have h1 : Cstar * (1 / Cstar) ≤ Cstar * B ^ (e / 4) :=
        mul_le_mul_of_nonneg_left hB (le_of_lt hC)
      rwa [mul_one_div, div_self (ne_of_gt hC)] at h1
    calc B ^ (3 * e / 4) = B ^ (3 * e / 4) * 1 := by ring
      _ ≤ B ^ (3 * e / 4) * (Cstar * B ^ (e / 4)) :=
            mul_le_mul_of_nonneg_left hCs (le_of_lt h3)
      _ = B ^ (3 * e / 4) * B ^ (e / 4) * Cstar := by ring
      _ = B ^ e * Cstar := by
            rw [← Real.rpow_add hBpos]
            congr 1
            ring
  -- ## Assembly.
  have hBge1 : ∀ᶠ B in atTop, (1 : ℝ) ≤ B := eventually_ge_atTop 1
  have hBpos : ∀ᶠ B in atTop, (0 : ℝ) < B := eventually_gt_atTop 0
  filter_upwards [hW, hlog, hk, hlarge, hBge1, hBpos] with B hW hlog hk hlarge hBge1 hBpos
  have hlogBnn : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hBge1
  have hlognn : (0 : ℝ) ≤ (Real.log B) ^ (m + 1) := pow_nonneg hlogBnn _
  have he2nn : (0 : ℝ) ≤ B ^ (e / 2) := Real.rpow_nonneg (le_of_lt hBpos) _
  have he8nn : (0 : ℝ) ≤ B ^ (e / 8) := Real.rpow_nonneg (le_of_lt hBpos) _
  have hprod : B ^ (e / 2) * B ^ (e / 8) * B ^ (e / 8) = B ^ (3 * e / 4) := by
    rw [← Real.rpow_add hBpos, ← Real.rpow_add hBpos]
    congr 1
    ring
  calc (Work.HP.bigW (Work.HP.wOf B) : ℝ) ^ p
        * (Real.log B) ^ (m + 1) * κ
      ≤ B ^ (e / 2) * B ^ (e / 8) * B ^ (e / 8) := by
        apply mul_le_mul
        · exact mul_le_mul hW hlog hlognn he2nn
        · exact hk
        · exact le_of_lt hκ
        · exact mul_nonneg he2nn he8nn
    _ = B ^ (3 * e / 4) := hprod
    _ ≤ B ^ e * Cstar := hlarge

end Work.ClassCount
