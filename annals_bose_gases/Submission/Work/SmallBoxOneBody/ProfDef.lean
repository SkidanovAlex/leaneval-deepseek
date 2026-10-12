import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A smooth bump profile of very small mass

We build a `C^∞` function `Prof : ℝ → ℝ` which is `1` on `(-∞,0]`, `0` on `[1,∞)`,
positive on `(-∞,1)`, and astronomically small already for `s ≥ 1/50`.  It is the
profile used to build a `ContDiffBumpBase` on `ℝ³` whose radius-`2` member has
`L²` mass close to the minimal possible `|B(0,1)|`.
-/

namespace Work.SmallBoxOneBody

open Real
open scoped ContDiff

/-- The profile: `Prof s = v^100 / (v^100 + u)` with `v = expNegInvGlue (1-s)`,
`u = expNegInvGlue s`. -/
noncomputable def Prof (s : ℝ) : ℝ :=
  (expNegInvGlue (1 - s)) ^ 100 /
    ((expNegInvGlue (1 - s)) ^ 100 + expNegInvGlue s)

lemma Prof_denom_pos (s : ℝ) :
    0 < (expNegInvGlue (1 - s)) ^ 100 + expNegInvGlue s := by
  rcases lt_or_ge s 1 with h | h
  · have h1 : 0 < expNegInvGlue (1 - s) := expNegInvGlue.pos_of_pos (by linarith)
    have h2 : 0 < (expNegInvGlue (1 - s)) ^ 100 := pow_pos h1 _
    have h3 : 0 ≤ expNegInvGlue s := expNegInvGlue.nonneg s
    linarith
  · have h1 : 0 ≤ (expNegInvGlue (1 - s)) ^ 100 :=
      pow_nonneg (expNegInvGlue.nonneg _) _
    have h2 : 0 < expNegInvGlue s := expNegInvGlue.pos_of_pos (by linarith)
    linarith

lemma Prof_nonneg (s : ℝ) : 0 ≤ Prof s :=
  div_nonneg (pow_nonneg (expNegInvGlue.nonneg _) _) (Prof_denom_pos s).le

lemma Prof_le_one (s : ℝ) : Prof s ≤ 1 := by
  rw [Prof, div_le_one (Prof_denom_pos s)]
  exact le_add_of_nonneg_right (expNegInvGlue.nonneg s)

lemma expNegInvGlue_eq_exp (x : ℝ) (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  simp [expNegInvGlue, not_le.mpr hx]

lemma Prof_of_nonpos {s : ℝ} (h : s ≤ 0) : Prof s = 1 := by
  have hv : 0 < expNegInvGlue (1 - s) := expNegInvGlue.pos_of_pos (by linarith)
  rw [Prof, expNegInvGlue.zero_of_nonpos h, add_zero]
  exact div_self (pow_ne_zero 100 hv.ne')

lemma Prof_of_one_le {s : ℝ} (h : 1 ≤ s) : Prof s = 0 := by
  have hu : expNegInvGlue (1 - s) = 0 := expNegInvGlue.zero_of_nonpos (by linarith)
  rw [Prof, hu, zero_pow (by norm_num : (100 : ℕ) ≠ 0)]
  simp

lemma Prof_pos {s : ℝ} (h : s < 1) : 0 < Prof s := by
  have hv : 0 < expNegInvGlue (1 - s) := expNegInvGlue.pos_of_pos (by linarith)
  exact div_pos (pow_pos hv 100) (Prof_denom_pos s)

lemma Prof_eq_zero_iff {s : ℝ} : Prof s = 0 ↔ 1 ≤ s := by
  refine ⟨fun h => ?_, fun h => Prof_of_one_le h⟩
  have hden := Prof_denom_pos s
  rw [Prof, div_eq_zero_iff] at h
  rcases h with h | h
  · have hv : expNegInvGlue (1 - s) = 0 := (pow_eq_zero_iff (by norm_num : (100:ℕ) ≠ 0)).mp h
    have : 1 - s ≤ 0 := expNegInvGlue.zero_iff_nonpos.mp hv
    linarith
  · exact absurd h hden.ne'

lemma Prof_ne_zero_iff {s : ℝ} : Prof s ≠ 0 ↔ s < 1 := by
  simp only [ne_eq, Prof_eq_zero_iff, not_le]

lemma Prof_smooth : ContDiff ℝ ∞ Prof := by
  have hv : ContDiff ℝ ∞ fun s : ℝ => expNegInvGlue (1 - s) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hnum : ContDiff ℝ ∞ fun s : ℝ => (expNegInvGlue (1 - s)) ^ 100 := hv.pow 100
  have hden : ContDiff ℝ ∞ fun s : ℝ =>
      (expNegInvGlue (1 - s)) ^ 100 + expNegInvGlue s :=
    hnum.add expNegInvGlue.contDiff
  exact hnum.div hden (fun s => (Prof_denom_pos s).ne')

lemma Prof_exp_bound {s : ℝ} (h : 1 / 50 ≤ s) : Prof s ≤ Real.exp (-50) := by
  rcases lt_or_ge s 1 with hs | hs
  · have hs0 : 0 < s := by linarith
    have h1s : 0 < 1 - s := by linarith
    have hv : expNegInvGlue (1 - s) = Real.exp (-(1 - s)⁻¹) := expNegInvGlue_eq_exp _ h1s
    have hu : expNegInvGlue s = Real.exp (-s⁻¹) := expNegInvGlue_eq_exp _ hs0
    have hden := Prof_denom_pos s
    have hnum_pos : 0 < (expNegInvGlue (1 - s)) ^ 100 :=
      pow_pos (expNegInvGlue.pos_of_pos h1s) 100
    have hle : Prof s ≤ (expNegInvGlue (1 - s)) ^ 100 / expNegInvGlue s := by
      rw [Prof]
      exact div_le_div_of_nonneg_left (by positivity) (expNegInvGlue.pos_of_pos hs0)
        (by linarith [pow_nonneg (expNegInvGlue.nonneg (1 - s)) 100])
    have hexp : (expNegInvGlue (1 - s)) ^ 100 / expNegInvGlue s
        = Real.exp (-100 * (1 - s)⁻¹ + s⁻¹) := by
      rw [hv, hu, ← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    have hA : s⁻¹ ≤ 50 := by
      rw [inv_le_comm₀ hs0 (by norm_num : (0:ℝ) < 50)]
      norm_num
      exact h
    have hB : 1 ≤ (1 - s)⁻¹ := by
      rw [one_le_inv₀ h1s]
      linarith
    have hkey : -100 * (1 - s)⁻¹ + s⁻¹ ≤ -50 := by
      have : -100 * (1 - s)⁻¹ ≤ -100 * 1 := by nlinarith [hB]
      linarith
    calc Prof s ≤ (expNegInvGlue (1 - s)) ^ 100 / expNegInvGlue s := hle
      _ = Real.exp (-100 * (1 - s)⁻¹ + s⁻¹) := hexp
      _ ≤ Real.exp (-50) := Real.exp_le_exp.mpr hkey
  · rw [Prof_of_one_le hs]
    exact (Real.exp_pos (-50)).le

end Work.SmallBoxOneBody
