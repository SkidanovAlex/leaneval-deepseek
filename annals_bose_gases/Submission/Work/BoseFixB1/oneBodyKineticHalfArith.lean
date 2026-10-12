import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.paramsAt_facts
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.oneBodyKineticHalfArith` — the `ε₀` arithmetic for the sliding comparison

The two-cut smearing comparison `Work.BoseFixB1.chiB_proj_le_mix` carries three numerical
criteria on FS's small parameters `(s, d) = ((μa³)^{1/323}, (μa³)^{6/323})` and the two fixed
profile moments `M₁ = (2π)⁻³∫‖t‖ profHat(t)²`, `M₂ = (2π)⁻³∫‖t‖² profHat(t)²`:

    `4M₂s² ≤ (1−d)²`,  `128M₁s ≤ 1`,  `64s⁷ ≤ d`.

Since `d = s⁶` the third reads `64s ≤ 1`; all three are upper bounds on `s = t^{1/323}`, hence
hold for `t = μa³ ≤ ε₀` with `ε₀` a suitable power of the fixed constants.  This module records
the monotonicity lemmas (`(u^{323/k})^{k/323} = u`) and the criterion transfer.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB1

open Work.BoseBox

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The first moment of the squared bump profile. -/
noncomputable def profM1 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3, ‖t‖ * (Work.OneBodyKin.profHat t) ^ 2

/-- The second moment of the squared bump profile. -/
noncomputable def profM2 : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3, ‖t‖ ^ 2 * (Work.OneBodyKin.profHat t) ^ 2

lemma profM1_nonneg : 0 ≤ profM1 := by
  rw [profM1]
  exact mul_nonneg (by positivity)
    (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (sq_nonneg _))

lemma profM2_nonneg : 0 ≤ profM2 := by
  rw [profM2]
  exact mul_nonneg (by positivity) (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-! ## 1. The monomial arithmetic `(u^{323/k})^{k/323} = u` -/

/-- `(u^{323/k})^{k/323} = u` for `u > 0`, `k ≠ 0`. -/
lemma rpow_ratio_left {u k : ℝ} (hu : 0 < u) (hk : 0 < k) : (u ^ (323 / k)) ^ (k / 323) = u := by
  rw [← Real.rpow_mul hu.le]
  have h : 323 / k * (k / 323) = 1 := by field_simp
  rw [h, Real.rpow_one]

/-- **The master comparison.**  `t ≤ u^{323/k}` implies `t^{k/323} ≤ u` (`t ≥ 0`, `u > 0`). -/
lemma rpow_le_of_le_rpow {t u k : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hk : 0 < k)
    (h : t ≤ u ^ (323 / k)) : t ^ (k / 323) ≤ u := by
  calc t ^ (k / 323) ≤ (u ^ (323 / k)) ^ (k / 323) :=
        Real.rpow_le_rpow ht h (by positivity)
    _ = u := rpow_ratio_left hu hk

/-- The same in terms of `fsXp`: `t ≤ u^{323/k}` implies `fsXp t k ≤ u`. -/
lemma fsXp_le_of_bound {t u k : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hk : 0 < k)
    (h : t ≤ u ^ (323 / k)) : fsXp t k ≤ u := by
  rw [fsXp]
  exact rpow_le_of_le_rpow ht hu hk h

/-! ## 2. The criterion transfer -/

/-- **The criterion transfer.**  If `t^{k/323} ≤ u`, `0 ≤ f` and `f·u ≤ c`, then
`f·t^{k/323} ≤ c`. -/
lemma criterion_gen {t u f c k : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hf : 0 ≤ f) (hk : 0 < k)
    (hfu : f * u ≤ c) (h : t ≤ u ^ (323 / k)) : f * t ^ (k / 323) ≤ c := by
  have ht1 : t ^ (k / 323) ≤ u := rpow_le_of_le_rpow ht hu hk h
  calc f * t ^ (k / 323) ≤ f * u := mul_le_mul_of_nonneg_left ht1 hf
    _ ≤ c := hfu

/-- The `k = 1` criterion: `128M₁s ≤ 1` (`s = t^{1/323}`) on the dilute side. -/
lemma criterion_one {t u f c : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hf : 0 ≤ f) (hfu : f * u ≤ c)
    (h : t ≤ u ^ (323 : ℝ)) : f * t ^ ((1 : ℝ) / 323) ≤ c := by
  have := criterion_gen (k := (1 : ℝ)) ht hu hf (by norm_num) hfu (by simpa using h)
  simpa using this

/-- The `k = 2` criterion: `4M₂s² ≤ 1/4`. -/
lemma criterion_two {t u g c : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hg : 0 ≤ g) (hgu : g * u ≤ c)
    (h : t ≤ u ^ ((323 : ℝ) / 2)) : g * t ^ ((2 : ℝ) / 323) ≤ c :=
  criterion_gen (k := (2 : ℝ)) ht hu hg (by norm_num) hgu h

/-- The `k = 6` criterion: `d t^{6/323}` bounds. -/
lemma criterion_six {t u f c : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hf : 0 ≤ f) (hfu : f * u ≤ c)
    (h : t ≤ u ^ ((323 : ℝ) / 6)) : f * t ^ ((6 : ℝ) / 323) ≤ c :=
  criterion_gen (k := (6 : ℝ)) ht hu hf (by norm_num) hfu h

/-- The `k = 23/4` criterion: `ε_T = t^{(23/4)/323}` bounds. -/
lemma criterion_eT {t u f c : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hf : 0 ≤ f) (hfu : f * u ≤ c)
    (h : t ≤ u ^ ((323 : ℝ) / (23 / 4))) : f * t ^ (((23 : ℝ) / 4) / 323) ≤ c :=
  criterion_gen (k := ((23 : ℝ) / 4)) ht hu hf (by norm_num) hfu h


/-! ## 3. The criteria in the FS parameter block -/

/-- `fsXp t 1 = t^{1/323}` (definitional). -/
lemma fsXp_one_eq (t : ℝ) : fsXp t 1 = t ^ ((1 : ℝ) / 323) := rfl

/-- `(fsXp t 1) ^ 6 = t^{6/323}`. -/
lemma fsXp_one_pow_six {t : ℝ} (ht : 0 ≤ t) : (fsXp t 1) ^ 6 = t ^ ((6 : ℝ) / 323) := by
  rw [fsXp_one_eq, ← Real.rpow_natCast (t ^ ((1 : ℝ) / 323)) 6, ← Real.rpow_mul ht]
  norm_num

/-- **The interface**: on the dilute side `t = μa³ ≤ ε₀` all the numerical criteria of the
two-cut smearing comparison hold, with `d = t^{6/323}`, `s = t^{1/323}`, `ε_T = t^{23/(4·323)}`.

All three criteria are consequences of the single multiplicative bound `C·s ≤ 1` with
`C := 128(M₁+1) + 8(M₂+1) + 2`: `s ≤ 1/C ≤ 1/(8(M₂+1))` gives `4M₂s² ≤ 1/4`,
`s ≤ 1/C ≤ 1/(128(M₁+1))` gives `128M₁s ≤ 1`, and `s ≤ 1/C ≤ 1/64` turns `64s⁷ ≤ d = s⁶`
into `64s ≤ 1`. -/
theorem exists_eps₀_criteria :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t : ℝ, 0 < t → t ≤ ε₀ →
      fsXp t 1 ≤ 1 / 2 ∧ fsXp t 6 ≤ 1 / 2 ∧ fsXp t (23 / 4) ≤ 1 / 2 ∧
      4 * profM2 * (fsXp t 1) ^ 2 ≤ (1 - fsXp t 6) ^ 2 ∧
      128 * profM1 * fsXp t 1 ≤ 1 ∧
      64 * (fsXp t 1) ^ 7 ≤ fsXp t 6 := by
  set C : ℝ := 128 * (profM1 + 1) + 8 * (profM2 + 1) + 2 with hC
  have hC1 : 128 * (profM1 + 1) ≤ C := by rw [hC]; nlinarith [profM2_nonneg]
  have hC2 : 8 * (profM2 + 1) ≤ C := by rw [hC]; nlinarith [profM1_nonneg]
  have hC64 : 64 ≤ C := by rw [hC]; nlinarith [profM1_nonneg, profM2_nonneg]
  have hCpos : 0 < C := by linarith
  have hCle : (1 : ℝ) / C ≤ 1 := by rw [div_le_one hCpos]; linarith
  refine ⟨(1 / C) ^ (323 : ℝ), by positivity, ?_⟩
  intro t ht0 ht1
  have htle1 : t ≤ 1 := by
    refine le_trans ht1 ?_
    calc (1 / C) ^ (323 : ℝ) ≤ (1 : ℝ) ^ (323 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hCle (by norm_num)
      _ = 1 := Real.one_rpow _
  -- the master multiplicative bound `C · s ≤ 1`
  have hCs : C * fsXp t 1 ≤ 1 := by
    have h := criterion_one (f := C) (c := 1) (u := 1 / C) ht0.le (by positivity)
      (le_of_lt hCpos)
      (by rw [mul_one_div, div_self (ne_of_gt hCpos)]) ht1
    rw [fsXp_one_eq]
    exact h
  have hs0 : 0 ≤ fsXp t 1 := by
    rw [fsXp_one_eq]; exact (Real.rpow_pos_of_pos ht0 _).le
  have hs1 : fsXp t 1 ≤ 1 / 2 := by nlinarith [hCs, hs0, hC64]
  have hd1 : fsXp t 6 ≤ 1 / 2 :=
    le_trans (fsXp_le_fsXp ht0 htle1 (by norm_num : (1 : ℝ) ≤ 6)) hs1
  have heT1 : fsXp t (23 / 4) ≤ 1 / 2 :=
    le_trans (fsXp_le_fsXp ht0 htle1 (by norm_num : (1 : ℝ) ≤ 23 / 4)) hs1
  -- (4) 4M₂s² ≤ 1/4
  have hsq : 16 * profM2 ≤ C ^ 2 := by nlinarith [hC2, profM2_nonneg]
  have hs2 : 4 * profM2 * (fsXp t 1) ^ 2 ≤ 1 / 4 := by
    have h0 : 0 ≤ C * fsXp t 1 := mul_nonneg hCpos.le hs0
    have hCsq : (C * fsXp t 1) ^ 2 ≤ 1 := by nlinarith [hCs, h0]
    nlinarith [hsq, hCsq, profM2_nonneg, hs0]
  -- (5) 128M₁s ≤ 1
  have hM1 : 128 * profM1 * fsXp t 1 ≤ 1 := by
    nlinarith [hCs, hC1, profM1_nonneg, hs0]
  -- (6) 64 s⁷ ≤ d
  have hs7 : 64 * (fsXp t 1) ^ 7 ≤ fsXp t 6 := by
    have h64 : 64 * fsXp t 1 ≤ 1 := by nlinarith [hCs, hC64, hs0]
    have hd6 : fsXp t 6 = (fsXp t 1) ^ 6 := (fsXp_one_pow_six ht0.le).symm
    rw [hd6, show (fsXp t 1) ^ 7 = (fsXp t 1) ^ 6 * fsXp t 1 by ring]
    nlinarith [h64, pow_nonneg hs0 6]
  refine ⟨hs1, hd1, heT1, ?_, hM1, hs7⟩
  have h3 : (1 : ℝ) / 2 ≤ 1 - fsXp t 6 := by linarith
  nlinarith [sq_nonneg (1 - fsXp t 6), hs2]

end Work.BoseFixB1
