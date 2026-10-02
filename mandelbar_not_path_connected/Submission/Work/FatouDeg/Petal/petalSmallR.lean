import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- Elementary "small r" lemma: for `M ≥ 0`, `cm > 0` and `n ≥ 1` there is a radius `R > 0`
such that for every `0 < r < R` all the listed bounds hold.  These are exactly the hypotheses
under which a `n`-th order petal estimate is dominated by the leading term `(cm/2) r^n`. -/
theorem petalSmallR (M cm : ℝ) (hM : 0 ≤ M) (hcm : 0 < cm) (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r < 1 ∧ r ^ n ≤ r ∧ r ^ n ≤ 1 ∧ r * M ≤ 1 ∧ r ^ n * (1 + r * M) ≤ 1 / 2 ∧
      2 * r ^ (n + 1) * M + r ^ (2 * n) * (1 + r * M) ^ 2 ≤ (cm / 2) * r ^ n := by
  -- The radius is chosen so that `r ≤ 1/4`, `r ^ n ≤ cm/16`, `r * M ≤ 1` and `r * M ≤ cm/8`
  -- for all `0 < r < R`.
  let s : ℝ := min 1 (cm / 8)
  let R : ℝ := min (min (1 / 4) (cm / 16)) (s / (M + 1))
  have hM1pos : (0 : ℝ) < M + 1 := by linarith
  have hs_pos : 0 < s := by
    dsimp [s]; exact lt_min zero_lt_one (by linarith)
  have hR1 : R ≤ 1 / 4 := by
    dsimp [R]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hR2 : R ≤ cm / 16 := by
    dsimp [R]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hR3 : R ≤ s / (M + 1) := by
    dsimp [R]; exact min_le_right _ _
  have hRpos : 0 < R := by
    dsimp [R]
    exact lt_min (lt_min (by norm_num) (by linarith)) (div_pos hs_pos hM1pos)
  have hs_le_one : s ≤ 1 := by dsimp [s]; exact min_le_left _ _
  have hs_le_cm8 : s ≤ cm / 8 := by dsimp [s]; exact min_le_right _ _
  have hRM_le_s : R * M ≤ s := by
    have h3 : R * M ≤ R * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hRpos)
    have h4 : R * (M + 1) ≤ (s / (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_right hR3 (le_of_lt hM1pos)
    have h5 : (s / (M + 1)) * (M + 1) = s := div_mul_cancel₀ s (ne_of_gt hM1pos)
    linarith [h3, h4, h5]
  have hRM1 : R * M ≤ 1 := le_trans hRM_le_s hs_le_one
  have hRM2 : R * M ≤ cm / 8 := le_trans hRM_le_s hs_le_cm8
  refine ⟨R, hRpos, ?_⟩
  intro r hr hrR
  have hr_quarter : r < 1 / 4 := lt_of_lt_of_le hrR hR1
  have hr_one : r ≤ 1 := by linarith
  have hr_lt_cm16 : r < cm / 16 := lt_of_lt_of_le hrR hR2
  have hrn_le_r : r ^ n ≤ r := by
    simpa using pow_le_pow_of_le_one (le_of_lt hr) hr_one hn
  have hrn_le_one : r ^ n ≤ 1 := pow_le_one₀ (le_of_lt hr) hr_one
  have hrn_quarter : r ^ n ≤ 1 / 4 := le_trans hrn_le_r (le_of_lt hr_quarter)
  have hrn_cm16 : r ^ n ≤ cm / 16 := le_trans hrn_le_r (le_of_lt hr_lt_cm16)
  have hrM_nonneg : 0 ≤ r * M := mul_nonneg (le_of_lt hr) hM
  have hrM_le_one : r * M ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (le_of_lt hrR) hM) hRM1
  have hrM_le_cm8 : r * M ≤ cm / 8 :=
    le_trans (mul_le_mul_of_nonneg_right (le_of_lt hrR) hM) hRM2
  have hA : (0 : ℝ) ≤ r ^ n := pow_nonneg (le_of_lt hr) n
  refine ⟨by linarith, hrn_le_r, hrn_le_one, hrM_le_one, ?_, ?_⟩
  · -- `r ^ n * (1 + r * M) ≤ 1/2`
    have h1p : 1 + r * M ≤ 2 := by linarith
    have h := mul_le_mul hrn_quarter h1p (by linarith : (0 : ℝ) ≤ 1 + r * M)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith
  · -- the main domination estimate
    have h1p : 1 + r * M ≤ 2 := by linarith
    have hsq : (1 + r * M) ^ 2 ≤ 4 := by nlinarith
    have hterm2 : r ^ n * (1 + r * M) ^ 2 ≤ cm / 4 := by
      have := mul_le_mul hrn_cm16 hsq (sq_nonneg (1 + r * M)) (by linarith : (0 : ℝ) ≤ cm / 16)
      linarith
    have hterm1 : 2 * (r * M) ≤ cm / 4 := by linarith
    have hkey : 2 * (r * M) + r ^ n * (1 + r * M) ^ 2 ≤ cm / 2 := by linarith
    have hmain : 2 * r ^ (n + 1) * M + r ^ (2 * n) * (1 + r * M) ^ 2
        = r ^ n * (2 * (r * M) + r ^ n * (1 + r * M) ^ 2) := by
      rw [pow_succ, show 2 * n = n * 2 from by omega, pow_mul]
      ring
    calc
      2 * r ^ (n + 1) * M + r ^ (2 * n) * (1 + r * M) ^ 2
          = r ^ n * (2 * (r * M) + r ^ n * (1 + r * M) ^ 2) := hmain
      _ ≤ r ^ n * (cm / 2) := mul_le_mul_of_nonneg_left hkey hA
      _ = (cm / 2) * r ^ n := by ring

end Work.FatouDeg.Petal
