import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.selberg_sharp_low
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers
import Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab

namespace Work.ChenPlan.LinearSieve.JR2

open Work.NumberTheory.Chen.APSwitchUpper

/-- `log ⌈z⌉₊ ≤ 2 log z` for `z ≥ 2` (`⌈z⌉₊ < z + 1 ≤ 2z`). -/
private theorem log_ceil_le_two_log {z : ℝ} (hz : 2 ≤ z) :
    Real.log ((⌈z⌉₊ : ℕ) : ℝ) ≤ 2 * Real.log z := by
  have hz0 : 0 < z := by linarith
  have h1 : Real.log ((⌈z⌉₊ : ℕ) : ℝ) ≤ Real.log (z + 1) :=
    Real.log_le_log (by positivity) (le_of_lt (Nat.ceil_lt_add_one hz0.le))
  have h2 : Real.log (z + 1) ≤ Real.log (2 * z) :=
    Real.log_le_log (by linarith) (by linarith)
  have h3 : Real.log (2 * z) = Real.log 2 + Real.log z :=
    Real.log_mul (by norm_num) (by linarith)
  have h4 : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz
  linarith

/-- The clearing of denominators in the sharp-Selberg transfer: `A/(u/b) ≤ A/(u/a) + 1/1000`
follows from `A·b ≤ A·a + u/1000` when `u, a, b > 0`. -/
private theorem div_div_le_add {A u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b)
    (h : A * b ≤ A * a + u / 1000) :
    A / (u / b) ≤ A / (u / a) + 1 / 1000 := by
  have h1 : A / (u / b) = A * b / u := by field_simp
  have h2 : A / (u / a) = A * a / u := by field_simp
  rw [h1, h2, div_le_iff₀ hu]
  have heq : (A * a / u + 1 / 1000) * u = A * a + u / 1000 := by field_simp
  linarith [heq]

/-- **The `σ ≤ 2` (Selberg) case of the upper sieve bound, against `Utab`.**  Applying the
sharp Selberg bound `hSel : SelbergLow` at the natural limit `Z = ⌈z⌉₊` (with `s' = log D/log Z ∈
[1/4,2]`) and transferring `2e^γ/s' ≤ Utab s` (using `Z < z+1`, `z ≥ e^8`, and on `[3/2,2]` the
closed form `riUp s = 2e^γ/s` plus the 1/1000 slack of `Numerics.riUp_le_Utab`).

Suggested imports: `Submission.Work.ChenPlan.LinearSieve.JR2.Defs`,
`Submission.Work.ChenPlan.LinearSieve.JR2.selberg_sharp_low`,
`Submission.Work.ChenPlan.LinearSieve.Framework`,
`Submission.Work.ChenPlan.LinearSieve.FrameworkR`,
`Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers`,
`Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab`. -/
theorem selberg_case_upper (hSel : Work.ChenPlan.LinearSieve.JR2.SelbergLow) :
    ∀ (K : ℝ), 0 ≤ K → ∀ η : ℝ, 0 < η → ∃ Ds : ℝ,
      ∀ (A : BoundingSieve) (z D : ℝ),
        2 ≤ z → Real.exp 8 ≤ z → Ds ≤ D → Submission.ChenPlan.IsLinear A z K → 0 ≤ A.totalMass →
        1 ≤ Real.log D / Real.log z → Real.log D / Real.log z ≤ 2 →
        Work.ChenPlan.LinearSieve.siftedSumR A z ≤ A.totalMass * Work.ChenPlan.LinearSieve.VfR A z *
          (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η)
          + Submission.ChenPlan.remSum A D := by
  intro K hK η hη
  obtain ⟨D₀, hD₀⟩ := hSel K hK η hη
  refine ⟨D₀, ?_⟩
  intro A z D hz2 hze hD hlin hX hs1 hs2
  -- basic positivity and the parameter `σ = log D / log z ∈ [1,2]`
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogDpos : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogz).mp hs1
    linarith
  have hlogD_ge : Real.log z ≤ Real.log D := by
    have h := (le_div_iff₀ hlogz).mp hs1
    linarith
  have hlogD_le : Real.log D ≤ 2 * Real.log z := (div_le_iff₀ hlogz).mp hs2
  -- the natural limit `Z = ⌈z⌉₊`
  have hZgeR : z ≤ ((⌈z⌉₊ : ℕ) : ℝ) := Nat.le_ceil z
  have hZ2R : (2 : ℝ) ≤ ((⌈z⌉₊ : ℕ) : ℝ) := le_trans hz2 hZgeR
  have hZ2 : 2 ≤ ⌈z⌉₊ := by exact_mod_cast hZ2R
  have hZ1 : 1 < ⌈z⌉₊ := by omega
  have hlogZ : 0 < Real.log (((⌈z⌉₊ : ℕ) : ℝ)) := Real.log_pos (by exact_mod_cast hZ1)
  have hlogZge : Real.log z ≤ Real.log (((⌈z⌉₊ : ℕ) : ℝ)) := Real.log_le_log hz0 hZgeR
  have hlogZ_le : Real.log (((⌈z⌉₊ : ℕ) : ℝ)) ≤ 2 * Real.log z := log_ceil_le_two_log hz2
  have hs'le : Real.log D / Real.log (((⌈z⌉₊:ℕ):ℝ)) ≤ 2 := by
    rw [div_le_iff₀ hlogZ]; linarith
  have hs'ge : 1/4 ≤ Real.log D / Real.log (((⌈z⌉₊:ℕ):ℝ)) := by
    rw [le_div_iff₀ hlogZ]; linarith
  -- the sharp Selberg bound at the natural limit `⌈z⌉₊`
  have hlinZ : IsLinearNat A (⌈z⌉₊) K := isLinearNat_of_isLinear A hz2 hK hZgeR hlin
  have hS' := hD₀ A (⌈z⌉₊) D hZ2 hD hlinZ hX hs'ge hs'le
  have hVf : Vf A (⌈z⌉₊) = VfR A z := (VfR_eq_Vf A z).symm
  have hsift : siftedSumLt A (⌈z⌉₊) = siftedSumR A z := (siftedSumR_eq_siftedSumLt A z).symm
  rw [hVf, hsift] at hS'
  simp only [] at hS'
  -- the numerical transfer `2e^γ/σ' ≤ Utab σ`
  have hE1 : (1:ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
    rw [Real.one_le_exp_iff]; linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hElt2 : Real.exp Real.eulerMascheroniConstant < 2 := by
    linarith [two_exp_gamma_lt_four]
  have hsub : Real.log (((⌈z⌉₊:ℕ):ℝ)) - Real.log z ≤ 1 / z := by
    have h1 : Real.log (((⌈z⌉₊:ℕ):ℝ)) ≤ Real.log (z + 1) :=
      Real.log_le_log (by positivity) (le_of_lt (Nat.ceil_lt_add_one hz0.le))
    have h2 : Real.log (z + 1) - Real.log z ≤ 1 / z := by
      rw [← Real.log_div (by linarith : z + 1 ≠ 0) (by linarith : z ≠ 0)]
      have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (z + 1) / z by positivity)
      have h4 : (z + 1) / z - 1 = 1 / z := by
        rw [add_div, div_self (ne_of_gt hz0), add_sub_cancel_left]
      linarith
    linarith
  have hclear : (2 * Real.exp Real.eulerMascheroniConstant) * Real.log (((⌈z⌉₊:ℕ):ℝ))
      ≤ (2 * Real.exp Real.eulerMascheroniConstant) * Real.log z + Real.log D / 1000 := by
    have hzb : (2000:ℝ) ≤ z := le_trans two_thousand_le_exp_eight hze
    have hz8 : (8:ℝ) ≤ Real.log z := by
      have h := Real.log_le_log (Real.exp_pos 8) hze
      rwa [Real.log_exp] at h
    have hz8D : (8:ℝ) ≤ Real.log D := le_trans hz8 hlogD_ge
    have h1 : (2 * Real.exp Real.eulerMascheroniConstant) * (Real.log (((⌈z⌉₊:ℕ):ℝ)) - Real.log z)
        ≤ (2 * Real.exp Real.eulerMascheroniConstant) * (1 / z) :=
      mul_le_mul_of_nonneg_left hsub (by positivity)
    have h2 : (2 * Real.exp Real.eulerMascheroniConstant) * (1 / z) ≤ Real.log D / 1000 := by
      rw [mul_one_div, div_le_iff₀ (by linarith : (0:ℝ) < z)]
      have hprod : (8:ℝ) * 2000 ≤ Real.log D * z :=
        mul_le_mul hz8D hzb (by norm_num) (by linarith)
      nlinarith [hElt2, hprod]
    linarith
  have hσ_sharp : 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log (((⌈z⌉₊:ℕ):ℝ)))
      ≤ 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log z) + 1 / 1000 :=
    div_div_le_add hlogDpos hlogz hlogZ hclear
  have hUtabσ : 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log z) + 1 / 1000
      ≤ Submission.ChenPlan.Utab (Real.log D / Real.log z) := by
    have hσpos : 0 < Real.log D / Real.log z := div_pos hlogDpos hlogz
    rcases lt_or_ge (Real.log D / Real.log z) (3/2) with h32 | h32
    · -- `σ < 3/2`: `Utab σ = 1.005·2e^γ/σ`
      rw [Utab_of_lt h32]
      have hL : 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log z) + 1/1000
          = (2 * Real.exp Real.eulerMascheroniConstant + (Real.log D / Real.log z)/1000)
            / (Real.log D / Real.log z) := by field_simp
      rw [hL, div_le_div_iff_of_pos_right hσpos]
      nlinarith [hE1, h32, hσpos]
    · -- `3/2 ≤ σ ≤ 2`: the closed form `riUp σ = 2e^γ/σ` plus the table slack
      have hclosed := Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div
        (Real.log D / Real.log z) hs1 (by linarith)
      have hU := Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab (Real.log D / Real.log z) hs1
      have hri' : 1 + riPhi (Real.log D / Real.log z)
          = 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log z) := hclosed
      linarith [hri', hU]
  have hUfin : 2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log (((⌈z⌉₊:ℕ):ℝ)))
      ≤ Submission.ChenPlan.Utab (Real.log D / Real.log z) := le_trans hσ_sharp hUtabσ
  have hVnn : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
  have hstep : A.totalMass * VfR A z * (2 * Real.exp Real.eulerMascheroniConstant
        / (Real.log D / Real.log (((⌈z⌉₊:ℕ):ℝ))) + η)
      ≤ A.totalMass * VfR A z * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η) :=
    mul_le_mul_of_nonneg_left (by linarith) hVnn
  linarith [hS', hstep]

end Work.ChenPlan.LinearSieve.JR2
