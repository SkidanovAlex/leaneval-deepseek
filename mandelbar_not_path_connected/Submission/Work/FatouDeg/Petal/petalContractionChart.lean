import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- Key scalar inequality for the petal contraction chart.

For `0 < s ≤ 1` and any `n : ℕ`, we have
`(n/3) (1 - s^2) ≤ (s⁻¹)^n - 1`.

The estimate follows from Bernoulli's inequality
`(s⁻¹)^n - 1 ≥ n (s⁻¹ - 1) = n (1-s)/s`
combined with `1 - s^2 = (1-s)(1+s)` and `(1+s)/3 ≤ 1/s` (valid because `s ≤ 1`). -/
lemma petalContraction_key (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (n : ℕ) :
    (n : ℝ) / 3 * (1 - s ^ 2) ≤ (s⁻¹) ^ n - 1 := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hu1 : 1 ≤ s⁻¹ := (one_le_inv₀ hs).mpr hs1
  have hber : 1 + (n : ℝ) * (s⁻¹ - 1) ≤ (s⁻¹) ^ n :=
    one_add_mul_sub_le_pow (by linarith) n
  have hnl : (n : ℝ) * (s⁻¹ - 1) ≤ (s⁻¹) ^ n - 1 := by linarith
  have hsub : s⁻¹ - 1 = (1 - s) / s := by field_simp
  have h3 : (1 + s) / 3 ≤ 1 / s := by
    rw [le_div_iff₀ hs]
    have hh : (1 + s) / 3 * s = (1 + s) * s / 3 := by ring
    rw [hh, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hs, hs1]
  have hle : (1 - s) * ((1 + s) / 3) ≤ (1 - s) * (1 / s) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  calc (n : ℝ) / 3 * (1 - s ^ 2)
      = (n : ℝ) * ((1 - s) * ((1 + s) / 3)) := by ring
    _ ≤ (n : ℝ) * ((1 - s) * (1 / s)) := by
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n)
    _ = (n : ℝ) * (s⁻¹ - 1) := by rw [hsub]; ring
    _ ≤ (s⁻¹) ^ n - 1 := hnl

theorem petalContractionChart (cm : ℝ) (hcm : 0 < cm) (n : ℕ) (hn : 1 ≤ n) {r s : ℝ}
    (hr : 0 < r) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (hδ : (3 / 2) * cm * r ^ n ≤ 1 - s ^ 2) :
    (n : ℝ) * cm / 2 ≤ (r ^ n)⁻¹ * ((s⁻¹) ^ n - 1) := by
  have hs_pos : 0 < s := by linarith
  have hrn_pos : 0 < r ^ n := pow_pos hr n
  have hrni : 0 < (r ^ n)⁻¹ := inv_pos.mpr hrn_pos
  have hkey : (n : ℝ) / 3 * (1 - s ^ 2) ≤ (s⁻¹) ^ n - 1 :=
    petalContraction_key s hs_pos hs1 n
  -- Multiply the hypothesis by `2/3` and clear the factor `r^n`.
  have hcm2 : cm * r ^ n ≤ (2 / 3) * (1 - s ^ 2) := by nlinarith [hδ]
  have hstep1 : cm ≤ (2 / 3) * (1 - s ^ 2) * (r ^ n)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hcm2 (le_of_lt hrni)
    have e : (cm * r ^ n) * (r ^ n)⁻¹ = cm := by
      field_simp
    rwa [e] at h
  have hA : (n : ℝ) * cm / 2 ≤ (r ^ n)⁻¹ * ((n : ℝ) / 3 * (1 - s ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hstep1 (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
    have e1 : (n : ℝ) / 2 * cm = (n : ℝ) * cm / 2 := by ring
    have e2 : (n : ℝ) / 2 * ((2 / 3) * (1 - s ^ 2) * (r ^ n)⁻¹)
        = (r ^ n)⁻¹ * ((n : ℝ) / 3 * (1 - s ^ 2)) := by ring
    rwa [e1, e2] at h
  have hB : (r ^ n)⁻¹ * ((n : ℝ) / 3 * (1 - s ^ 2))
      ≤ (r ^ n)⁻¹ * ((s⁻¹) ^ n - 1) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt hrni)
  exact le_trans hA hB

end Work.FatouDeg.Petal
