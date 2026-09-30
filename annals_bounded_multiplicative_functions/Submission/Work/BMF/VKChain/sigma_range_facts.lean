import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Consequences of the strip hypothesis `σ ≥ 1 - (cvk/4) L^{-6/7}` for `0 < cvk ≤ 1`, `L ≥ 1`:
the VK saving conditions `(1-σ)κ ≤ 1`, `1-σ ≤ cvk^{6/7}/2 · L^{-6/7}` (with `κ = (L/cvk)^{6/7}`),
and `σ ≥ 3/4`. -/
theorem sigma_range_facts {cvk L σ : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hL : 1 ≤ L)
    (hσ : 1 - cvk / 4 * L ^ (-(6 / 7) : ℝ) ≤ σ) :
    (1 - σ) * (L / cvk) ^ (6 / 7 : ℝ) ≤ 1 ∧
      1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7) : ℝ) ∧ 3 / 4 ≤ σ := by
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hc : 0 < cvk := hcvk0
  -- The strip hypothesis, rearranged.
  have h1s : 1 - σ ≤ cvk / 4 * L ^ (-(6 / 7) : ℝ) := by linarith
  have hLnn : 0 ≤ L ^ (-(6 / 7) : ℝ) := Real.rpow_nonneg hLpos.le _
  have hLle1 : L ^ (-(6 / 7) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  -- `cvk ≤ cvk^{6/7}`, since `cvk = cvk^{1/7} · cvk^{6/7}` and `cvk^{1/7} ≤ 1`.
  have hcle : cvk ≤ cvk ^ (6 / 7 : ℝ) := by
    have hsplit : cvk = cvk ^ (1 / 7 : ℝ) * cvk ^ (6 / 7 : ℝ) := by
      rw [← Real.rpow_add hc, show (1 : ℝ) / 7 + 6 / 7 = 1 by norm_num, Real.rpow_one]
    conv_lhs => rw [hsplit]
    have h17 : cvk ^ (1 / 7 : ℝ) ≤ 1 := Real.rpow_le_one hc.le hcvk1 (by norm_num)
    have h67nn : 0 ≤ cvk ^ (6 / 7 : ℝ) := Real.rpow_nonneg hc.le _
    calc cvk ^ (1 / 7 : ℝ) * cvk ^ (6 / 7 : ℝ) ≤ 1 * cvk ^ (6 / 7 : ℝ) :=
          mul_le_mul_of_nonneg_right h17 h67nn
      _ = cvk ^ (6 / 7 : ℝ) := one_mul _
  have hratio1 : 0 ≤ cvk / L := div_nonneg hc.le hLpos.le
  have hratio2 : 0 ≤ L / cvk := div_nonneg hLpos.le hc.le
  -- `(cvk/L)^{6/7} = cvk^{6/7} · L^{-6/7}`.
  have hCL : (cvk / L) ^ (6 / 7 : ℝ) = cvk ^ (6 / 7 : ℝ) * L ^ (-(6 / 7) : ℝ) := by
    rw [Real.div_rpow hc.le hLpos.le, Real.rpow_neg hLpos.le (6 / 7)]
    ring
  -- `(cvk/L)^{6/7} · (L/cvk)^{6/7} = 1`.
  have hbase : cvk / L * (L / cvk) = 1 := by field_simp
  have hprod : (cvk / L) ^ (6 / 7 : ℝ) * (L / cvk) ^ (6 / 7 : ℝ) = 1 := by
    rw [← Real.mul_rpow hratio1 hratio2, hbase, Real.one_rpow]
  -- The saving factor `cvk/4 · L^{-6/7}` is dominated by `(cvk/L)^{6/7}`.
  have hquart4 : cvk / 4 ≤ cvk ^ (6 / 7 : ℝ) := by linarith
  have hupper : cvk / 4 * L ^ (-(6 / 7) : ℝ) ≤ (cvk / L) ^ (6 / 7 : ℝ) := by
    rw [hCL]
    exact mul_le_mul_of_nonneg_right hquart4 hLnn
  have hun : 0 ≤ (L / cvk) ^ (6 / 7 : ℝ) := Real.rpow_nonneg hratio2 _
  have hkey : 1 - σ ≤ (cvk / L) ^ (6 / 7 : ℝ) := le_trans h1s hupper
  have h1 : (1 - σ) * (L / cvk) ^ (6 / 7 : ℝ) ≤ 1 := by
    calc (1 - σ) * (L / cvk) ^ (6 / 7 : ℝ)
        ≤ (cvk / L) ^ (6 / 7 : ℝ) * (L / cvk) ^ (6 / 7 : ℝ) :=
          mul_le_mul_of_nonneg_right hkey hun
      _ = 1 := hprod
  -- `cvk/4 ≤ cvk^{6/7}/2` by `cvk ≤ cvk^{6/7}`.
  have hquarter : cvk / 4 ≤ cvk ^ (6 / 7 : ℝ) / 2 := by
    have h67nn : 0 ≤ cvk ^ (6 / 7 : ℝ) := Real.rpow_nonneg hc.le _
    linarith
  have h2 : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7) : ℝ) := by
    calc 1 - σ ≤ cvk / 4 * L ^ (-(6 / 7) : ℝ) := h1s
      _ ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7) : ℝ) := mul_le_mul_of_nonneg_right hquarter hLnn
  -- `cvk/4 · L^{-6/7} ≤ 1/4`, hence `σ ≥ 3/4`.
  have hb : cvk / 4 * L ^ (-(6 / 7) : ℝ) ≤ 1 / 4 := by
    calc cvk / 4 * L ^ (-(6 / 7) : ℝ) ≤ (1 / 4) * 1 := by
          apply mul_le_mul (by linarith) hLle1 hLnn (by norm_num)
      _ = 1 / 4 := by norm_num
  have h3 : 3 / 4 ≤ σ := by linarith
  exact ⟨h1, h2, h3⟩

end Work.BMF.VKChain
