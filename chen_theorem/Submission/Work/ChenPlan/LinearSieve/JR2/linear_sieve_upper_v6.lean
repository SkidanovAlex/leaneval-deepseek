import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers
import Submission.Work.ChenPlan.LinearSieve.JR2.sharp_gp
import Submission.Work.ChenPlan.LinearSieve.JR2.q_trick_upper_core
import Submission.Work.ChenPlan.LinearSieve.JR2.subSieve_SharpNorm
import Submission.Work.ChenPlan.LinearSieve.JR2.Qmod_mul_VfR
import Submission.Work.ChenPlan.LinearSieve.JR2.Qb
import Submission.Work.ChenPlan.LinearSieve.JR2.riUp_shift_le_utab
import Submission.Work.ChenPlan.LinearSieve.JR2.selberg_case_upper
import Submission.Work.ChenPlan.LinearSieve.JR2.qtrick_upper_bound
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt
import Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab
import Submission.Work.ChenPlan.LinearSieve.Utab.one_le_Utab

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

noncomputable section

open Work.ChenPlan.LinearSieve
open Work.NumberTheory.Chen.APSwitchUpper

set_option maxHeartbeats 1000000

/-! ## The assembly -/

/-- **The upper half of the v6 contract, assembled** (see `JR2/NOTES.md`, `JR2/Defs.lean`).

Inputs (hypotheses, so this file is independent of the in-flight lemmas):
`hL : LayerSharpBound 1000 (99/100)` (the per-layer crux),
`hSel : SelbergLow` (the sharp Selberg/Ankeny–Onishi bound `S ≤ X·Vf·(2e^γ/s + η) + R` for
`s ∈ [1/4, 2]`), `hLip : RiLipschitz` (`riUp`, `riPsi` are Lipschitz on `[2,∞)`).

RECIPE.  Given `K ≥ 0`, `η > 0`, put `ε := min (1/100) (min η 1 / 10^11)`,
`u₀ := max 2 (exp (K/ε))` (`JR2/numeric_helpers.u0_bounds` gives `2 ≤ u₀`, `K ≤ ε log u₀`),
`Qb := ∏_{p < ⌈u₀⌉₊} p`, `Ds` from `hSel (η/2)`, and take the thresholds
`D₀ := max (max 2 (2*Qb+2)) Ds`, `z₀ := max (max (exp 8) (u₀+1)) (exp (10^6·(u₀+2)^2))`.
`JR2/numeric_helpers.log2000_le_log` gives `14251 ≤ z log z` and `sharpness_error_le` gives
`ε·(1000·10100)·errH σ ≤ 1/4000` for `σ := log D/log z ≥ 1`.

* **`σ ≤ 2`**: apply `hSel` to `A` with the natural limit `Z = ⌈z⌉₊` and the level `D`
  (`IsLinear A z K → IsLinearNat A ⌈z⌉₊ K` via `isLinearNat_of_isLinear`; `Vf A Z = VfR A z`;
  `siftedSumLt A Z = siftedSumR A z = A.siftedSum`, the last via `siftedSumLt_eq_siftedSum`).
  The parameter `σ' = log D/log Z` satisfies `1/4 ≤ σ' ≤ σ ≤ 2` and `log Z ≤ log z + 1/z`, so
  `2e^γ/σ' ≤ (2e^γ/σ)(1 + 1/(z log z)) ≤ Utab σ` (`JR2/selberg_case_upper`).
* **`σ > 2`**: the `Q`-trick with `Q := Qmod A u₀ ≤ Qb`, `D'' := ⌊D/Q⌋` (`Q·D'' ≤ D`, `D'' ≥ 2`).
  `JR2/qtrick_upper_bound` gives `S ≤ X VfR z (riUp σ'' + ε·1000·10100·errH σ'') + remSum A D`
  for `σ'' := log D''/log z`; `σ - σ'' ≤ log(2Qb)/log z ≤ 1/500000` (`JR2/Qb.sigma_shift_le`), and
  `JR2/riUp_shift_le_utab` converts `riUp σ'' + ε·C₂·errH σ'' ≤ Utab σ`.
* Conclude with `siftedSumR A z = A.siftedSum`, `VfR A z = sieveV A`. -/
theorem linear_sieve_upper_v6 (hL : Work.ChenPlan.LinearSieve.JR2.LayerSharpBound 1000 (99/100))
    (hSel : Work.ChenPlan.LinearSieve.JR2.SelbergLow)
    (hLip : Work.ChenPlan.LinearSieve.JR2.RiLipschitz) :
    Submission.ChenPlan.LinearSieveUpper := by
  intro K hK η hη
  let ε : ℝ := min (1 / 100) (min η 1 / 10 ^ 11)
  have hε0 : 0 < ε := by
    have : 0 < min (1 / 100 : ℝ) (min η 1 / 10 ^ 11) :=
      lt_min (by norm_num) (div_pos (lt_min hη one_pos) (by norm_num))
    simpa only [ε] using this
  have hε0' : 0 ≤ ε := hε0.le
  have hε1 : ε ≤ 1 / 100 := by
    have : min (1 / 100 : ℝ) (min η 1 / 10 ^ 11) ≤ 1 / 100 := min_le_left _ _
    simpa only [ε] using this
  have hεη : ε ≤ min η 1 / 10 ^ 11 := by
    have : min (1 / 100 : ℝ) (min η 1 / 10 ^ 11) ≤ min η 1 / 10 ^ 11 := min_le_right _ _
    simpa only [ε] using this
  let u₀ : ℝ := max 2 (Real.exp (K / ε))
  have hu₀2 : 2 ≤ u₀ := by
    have : 2 ≤ max (2:ℝ) (Real.exp (K / ε)) := le_max_left _ _
    simpa only [u₀] using this
  have hKε : K ≤ ε * Real.log u₀ := by
    have := (u0_bounds K ε hε0).2
    simpa only [u₀] using this
  obtain ⟨Ds, hDs⟩ := selberg_case_upper hSel K hK η hη
  refine ⟨max (max 2 (2 * (Qb u₀ : ℝ) + 2)) Ds,
    max (max (Real.exp 8) (u₀ + 1)) (Real.exp (10 ^ 6 * (u₀ + 2) ^ 2)), ?_⟩
  intro A z D hD hz hz2 hlin hlinR hlinL hlinM hX hσ1
  -- bounds on `z`
  have hze8 : Real.exp 8 ≤ z :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hu₀z : u₀ ≤ z :=
    le_trans (by linarith : u₀ ≤ u₀ + 1)
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hz))
  have hzbig : Real.exp (10 ^ 6 * (u₀ + 2) ^ 2) ≤ z :=
    le_trans (le_max_right _ _) hz
  have hzp : ∀ p ∈ A.prodPrimes.primeFactors, (p : ℝ) < z := hlin.1
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  rw [← siftedSumR_eq_siftedSum A hzp, ← VfR_eq_sieveV A hzp]
  by_cases hσ2le : Real.log D / Real.log z ≤ 2
  · -- `σ ≤ 2`: the sharp Selberg bound
    exact hDs A z D hz2 hze8 (le_trans (le_max_right _ _) hD) hlin hX hσ1 hσ2le
  · -- `σ > 2`: the `Q`-trick
    push_neg at hσ2le
    have hQ1 : 1 ≤ Qmod A u₀ :=
      Nat.one_le_iff_ne_zero.mpr (Qmod_ne_zero A u₀)
    have hQpos : (0 : ℝ) < (Qmod A u₀ : ℝ) := by exact_mod_cast hQ1
    have hQleR : (Qmod A u₀ : ℝ) ≤ (Qb u₀ : ℝ) := by
      exact_mod_cast (Qmod_le_Qb A u₀)
    have hDbig : 2 * (Qb u₀ : ℝ) + 2 ≤ D :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hD)
    have h2Q : 2 * (Qmod A u₀ : ℝ) ≤ D := by linarith
    have hDpos : (0 : ℝ) < D := by linarith
    have hQ1R : (1 : ℝ) ≤ (Qmod A u₀ : ℝ) := by exact_mod_cast hQ1
    have hD''2 : 2 ≤ ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) := by
      have h1 : (2 : ℝ) ≤ D / (Qmod A u₀ : ℝ) := by
        rw [le_div_iff₀ hQpos]; linarith
      exact_mod_cast Nat.le_floor h1
    have hD''pos : (0 : ℝ) < ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) := by linarith
    have hDle : ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) * (Qmod A u₀ : ℝ) ≤ D := by
      have h := Nat.floor_le (div_nonneg hDpos.le hQpos.le)
      have h2 := mul_le_mul_of_nonneg_right h hQpos.le
      rwa [div_mul_cancel₀ D (ne_of_gt hQpos)] at h2
    have hdiff : Real.log D / Real.log z
        - Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z ≤ 1 / 500000 :=
      sigma_shift_le (A := A) hu₀2 hzbig hDbig
    have hσ''1 : 1 ≤ Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z := by
      linarith
    have hσ''le : Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z
        ≤ Real.log D / Real.log z := by
      have hD''leD : ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) ≤ D := by
        have h := Nat.floor_le (div_nonneg hDpos.le hQpos.le)
        have h2 : D / (Qmod A u₀ : ℝ) ≤ D := by
          rw [div_le_iff₀ hQpos]; nlinarith
        linarith
      have hlog := Real.log_le_log hD''pos hD''leD
      rw [div_le_div_iff_of_pos_right hlogz]
      exact hlog
    have hQb := qtrick_upper_bound hL A hε0' hε1 hu₀2 hu₀z hz2 hK hKε hX hlinR hDle hD''2 hσ''1
    have hR := riUp_shift_le_utab hLip (σ := Real.log D / Real.log z)
      (σ'' := Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z)
      hε0' hεη hη.le hσ1 hσ2le hσ''1 hσ''le hdiff
    have hnn : 0 ≤ A.totalMass * VfR A z := mul_nonneg hX (VfR_nonneg A z)
    calc siftedSumR A z
        ≤ A.totalMass * VfR A z *
            (riUp (Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z)
             + ε * (1000 * 10100) * errH
                (Real.log ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z))
          + Submission.ChenPlan.remSum A D := hQb
      _ ≤ A.totalMass * VfR A z * (Submission.ChenPlan.Utab (Real.log D / Real.log z) + η)
          + Submission.ChenPlan.remSum A D := by
          linarith [mul_le_mul_of_nonneg_left hR hnn]

end

end Work.ChenPlan.LinearSieve.JR2
