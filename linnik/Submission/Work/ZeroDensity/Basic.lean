import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.FamilyZeroCountTrivial
import Submission.Work.LinnikAreas.FamilyZeroDensitySplitting
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

/-!
# `Work.ZeroDensity.Basic` — the elementary API and the bridges to the Areas

Everything in this file is proved, with no hypothesis: it is the interface through which the Areas
consume this chapter.

* `trivial_bound` — the σ-blind family count of the workspace, in this chapter's vocabulary.
* `trivial_famDensityPowerRange` — consequently `FamDensityPowerRange σlo σhi c B` holds in the
  *trivial range* `c(1-σhi) > 1`.
* `FamDensityEpsRange.toFamDensityRange`, `FamDensityEpsRange.toFamDensityPowerRange` — the
  `ε`-in-the-base form is stronger than the additive form and than the form with a logarithmic
  power.
* `famDensityPowerRange_glue` — gluing two ranges of `σ` (the larger of the two constants).
* monotonicity of the predicates in their exponents and ranges.
* `montgomerySharp_and_trivial` — the sharp Montgomery exponent plus the σ-blind count already give
  the `12/5` bound on `σ ≤ 3/4` (the remaining range `3/4 < σ ≤ 4/5` needs Huxley's theorem; see
  `Main.lean` for how the consumer `FamilyZeroDensityMontgomery` is discharged).
* the bridges `familyZeroDensityJutila_of_famDensityEpsRange`,
  `familyZeroDensityMontgomery_of_powerForm`, `pairDensityInput_of_dhLogFreeSpec`,
  `pairDensityHeightInput_of_dhLogFreeHeightSpec`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity

open Work.LinnikContract

/-! ## 1. The counting functions: basic facts -/

lemma zCount_eq_zeroCountIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    zCount χ σ T = Work.LinnikAreas.zeroCountIn χ σ T := rfl

lemma famCount_eq_sum (q : ℕ) [NeZero q] (σ T : ℝ) :
    famCount q σ T = ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T := rfl

lemma restCount_eq_pairCount {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (t : ℝ) :
    restCount χ₁ β₁ t = Work.LinnikAreas.Siegel.pairCount χ₁ β₁ t := rfl

lemma restCountHeight_eq_pairCountHeight {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) (t T : ℝ) :
    restCountHeight χ₁ β₁ t T = Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T := rfl

lemma zCount_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    0 ≤ zCount χ σ T := by
  rw [zCount, Work.LinnikAreas.zeroCountIn]
  refine finsum_nonneg (fun ρ => ?_)
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos h]; exact Nat.cast_nonneg _
  · rw [if_neg h]

lemma famCount_nonneg (q : ℕ) [NeZero q] (σ T : ℝ) : 0 ≤ famCount q σ T :=
  Finset.sum_nonneg (fun χ _ => zCount_nonneg χ σ T)

lemma multCount_nonneg (q : ℕ) [NeZero q] (lam : ℝ) : 0 ≤ multCount q lam :=
  Finset.sum_nonneg (fun χ _ => by
    refine finsum_nonneg (fun ρ => ?_)
    by_cases h : zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ lamOf q ρ ≤ lam
    · rw [if_pos h]; exact Nat.cast_nonneg _
    · rw [if_neg h])

lemma restCount_nonneg {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (t : ℝ) :
    0 ≤ restCount χ₁ β₁ t := by
  rw [restCount, Work.LinnikAreas.Siegel.pairCount]
  refine Finset.sum_nonneg (fun χ _ => ?_)
  refine finsum_nonneg (fun ρ => ?_)
  by_cases h : zeroMult χ ρ ≠ 0 ∧ lamOf q ρ ≤ t ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = β₁)
  · rw [if_pos h]; exact Nat.cast_nonneg _
  · rw [if_neg h]

/-- The base `qT` is positive for `q ≥ 2`, `T ≥ 1`. -/
lemma rpow_base_pos {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 0 < (q : ℝ) * T := by
  have h1 : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  nlinarith

lemma rpow_base_nonneg {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 0 ≤ (q : ℝ) * T :=
  le_of_lt (rpow_base_pos hq hT)

/-- `1 ≤ qT` for `q ≥ 2`, `T ≥ 1`. -/
lemma one_le_base {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) : 1 ≤ (q : ℝ) * T := by
  have h1 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

lemma logrpow_nonneg' {q : ℕ} (hq : 2 ≤ q) {T B : ℝ} (hT : 1 ≤ T) :
    0 ≤ (Real.log ((q : ℝ) * T)) ^ B :=
  Real.rpow_nonneg (Real.log_nonneg (one_le_base hq hT)) B

/-- The non-negativity of the right-hand side of every estimate of this chapter. -/
lemma rpow_log_mul_nonneg {q : ℕ} (hq : 2 ≤ q) {T c ε B σ : ℝ} (hT : 1 ≤ T) :
    0 ≤ ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) * (Real.log ((q : ℝ) * T)) ^ B :=
  mul_nonneg (Real.rpow_nonneg (rpow_base_nonneg hq hT) _) (logrpow_nonneg' hq hT)

/-- Above `σ = 1` there are no zeros in the rectangle at all, so the per-character count vanishes. -/
lemma zCount_eq_zero_of_one_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ T : ℝ}
    (h : 1 < σ) : zCount χ σ T = 0 := by
  rw [zCount, Work.LinnikAreas.zeroCountIn]
  refine finsum_eq_zero_of_forall_eq_zero (fun ρ => ?_)
  by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · exact absurd hc (fun hc => by linarith [hc.1, hc.2.1])
  · rw [if_neg hc]

lemma famCount_eq_zero_of_one_lt (q : ℕ) [NeZero q] {σ T : ℝ} (h : 1 < σ) :
    famCount q σ T = 0 := by
  rw [famCount_eq_sum]
  exact Finset.sum_eq_zero (fun χ _ => zCount_eq_zero_of_one_lt χ h)

/-! ## 2. The trivial (σ-blind) bound, and the trivial range of a density estimate -/

/-- The σ-blind family count of the workspace (`Work.LinnikAreas.FamilyZeroCountTrivial`),
restated in this chapter's vocabulary. -/
theorem trivial_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      famCount q σ T ≤ C * ((q : ℝ) * T) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := Work.LinnikAreas.FamilyZeroCountTrivial ε hε
  exact ⟨C, hC, fun q hq _ σ T h0 h1 hT => h q hq σ T h0 h1 hT⟩

/-- **The trivial range of a density estimate.**  If `c·(1-σhi) > 1` (and `0 ≤ σlo`, `σhi ≤ 1`,
`c > 0`, `B ≥ 0`) then `FamDensityPowerRange σlo σhi c B` holds: on `σ ≤ σhi` the exponent
`(c+ε)(1-σ)` of the estimate dominates `1+ε'`, the exponent supplied by the σ-blind bound
`trivial_bound`.  (For `c = 12/5` this covers `σ ≤ 7/12`; for `c = 2` it covers `σ ≤ 1/2`.) -/
theorem trivial_famDensityPowerRange {σlo σhi c B : ℝ} (hc : 0 < c) (hσlo : 0 ≤ σlo)
    (hσhi : σhi ≤ 1) (hB : 0 ≤ B) (h : 1 < c * (1 - σhi)) :
    FamDensityPowerRange σlo σhi c B := by
  intro ε hε
  obtain ⟨C, hC, htriv⟩ := trivial_bound (min (ε / 2) ((c * (1 - σhi) - 1) / 2))
    (lt_min (by linarith) (by linarith))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (Real.log 2) ^ B, by positivity, ?_⟩
  intro q hq _inst σ T hσlo' hσhi' hT
  have hσ0 : 0 ≤ σ := le_trans hσlo hσlo'
  have hσ1 : σ ≤ 1 := le_trans hσhi' hσhi
  have hbase2 : (2 : ℝ) ≤ (q : ℝ) * T := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hle1 : 1 - σhi ≤ 1 - σ := by linarith
  have hexp : 1 + min (ε / 2) ((c * (1 - σhi) - 1) / 2) ≤ (c + ε) * (1 - σ) := by
    have h2 : min (ε / 2) ((c * (1 - σhi) - 1) / 2) ≤ (c * (1 - σhi) - 1) / 2 :=
      min_le_right _ _
    have h3 : 1 + (c * (1 - σhi) - 1) / 2 = (1 + c * (1 - σhi)) / 2 := by ring
    have h4 : (1 + c * (1 - σhi)) / 2 ≤ c * (1 - σhi) := by linarith
    have h5 : c * (1 - σhi) ≤ (c + ε) * (1 - σ) := by
      have h6 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hc)
      have h7 : 0 ≤ ε * (1 - σ) := mul_nonneg (le_of_lt hε) (by linarith)
      nlinarith
    linarith
  have hstep1 : C * ((q : ℝ) * T) ^ (1 + min (ε / 2) ((c * (1 - σhi) - 1) / 2))
      ≤ C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase1 hexp) (le_of_lt hC)
  have hlogge : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hbase2
  have hpowlog : (Real.log 2) ^ B ≤ (Real.log ((q : ℝ) * T)) ^ B :=
    Real.rpow_le_rpow hlog2.le hlogge hB
  have hstep2 : C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
      ≤ C / (Real.log 2) ^ B * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
          * (Real.log ((q : ℝ) * T)) ^ B := by
    have hCeq : C ≤ (C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B := by
      calc C = (C / (Real.log 2) ^ B) * (Real.log 2) ^ B := by
            rw [div_mul_cancel₀]; exact ne_of_gt (Real.rpow_pos_of_pos hlog2 B)
        _ ≤ (C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B :=
            mul_le_mul_of_nonneg_left hpowlog (by positivity)
    calc C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
        ≤ ((C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B)
            * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) :=
          mul_le_mul_of_nonneg_right hCeq (Real.rpow_nonneg hbase0 _)
      _ = C / (Real.log 2) ^ B * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
            * (Real.log ((q : ℝ) * T)) ^ B := by ring
  exact le_trans (htriv q hq σ T hσ0 hσ1 hT) (le_trans hstep1 hstep2)

/-! ## 3. Monotonicity, gluing, and the relations between the forms -/

lemma famDensityRange_mono {σlo σlo' σhi σhi' c c' : ℝ} (hsl : σlo ≤ σlo')
    (hsh : σhi' ≤ σhi) (hc : c ≤ c') (h : FamDensityRange σlo σhi c) :
    FamDensityRange σlo' σhi' c' := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hsl' hsh' hT
  by_cases hσ1 : σ ≤ 1
  · have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    refine le_trans (hh q hq σ T (le_trans hsl hsl') (le_trans hsh' hsh) hT) ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
    refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
    have hnn : (0 : ℝ) ≤ 1 - σ := by linarith
    nlinarith
  · push_neg at hσ1
    rw [famCount_eq_zero_of_one_lt q hσ1]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _)

lemma famDensityEpsRange_mono {σlo σlo' σhi σhi' c c' : ℝ} (hsl : σlo ≤ σlo')
    (hsh : σhi' ≤ σhi) (hc : c ≤ c') (h : FamDensityEpsRange σlo σhi c) :
    FamDensityEpsRange σlo' σhi' c' := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hsl' hsh' hT
  by_cases hσ1 : σ ≤ 1
  · have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    refine le_trans (hh q hq σ T (le_trans hsl hsl') (le_trans hsh' hsh) hT) ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
    refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
    have hnn : (0 : ℝ) ≤ 1 - σ := by linarith
    nlinarith
  · push_neg at hσ1
    rw [famCount_eq_zero_of_one_lt q hσ1]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _)

lemma famDensityPowerRange_mono {σlo σlo' σhi σhi' c c' B : ℝ} (hsl : σlo ≤ σlo')
    (hsh : σhi' ≤ σhi) (hc : c ≤ c') (h : FamDensityPowerRange σlo σhi c B) :
    FamDensityPowerRange σlo' σhi' c' B := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hsl' hsh' hT
  by_cases hσ1 : σ ≤ 1
  · have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    have hmono : ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) ≤ ((q : ℝ) * T) ^ ((c' + ε) * (1 - σ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
      have hnn : (0 : ℝ) ≤ 1 - σ := by linarith
      nlinarith
    refine le_trans (hh q hq σ T (le_trans hsl hsl') (le_trans hsh' hsh) hT) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono (le_of_lt hC))
      (logrpow_nonneg' hq hT)
  · push_neg at hσ1
    rw [famCount_eq_zero_of_one_lt q hσ1]
    exact mul_nonneg (mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _))
      (logrpow_nonneg' hq hT)

/-- **Gluing two ranges of `σ`.** -/
theorem famDensityPowerRange_glue {σlo m σhi c B : ℝ}
    (h1 : FamDensityPowerRange σlo m c B) (h2 : FamDensityPowerRange m σhi c B) :
    FamDensityPowerRange σlo σhi c B := by
  intro ε hε
  obtain ⟨C1, hC1, hh1⟩ := h1 ε hε
  obtain ⟨C2, hC2, hh2⟩ := h2 ε hε
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro q hq _inst σ T hσlo hσhi hT
  rcases le_total σ m with h | h
  · refine le_trans (hh1 q hq σ T hσlo h hT) ?_
    have hfac : C1 * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
        ≤ max C1 C2 * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _)
    exact mul_le_mul_of_nonneg_right hfac (logrpow_nonneg' hq hT)
  · refine le_trans (hh2 q hq σ T h hσhi hT) ?_
    have hfac : C2 * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
        ≤ max C1 C2 * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _)
    exact mul_le_mul_of_nonneg_right hfac (logrpow_nonneg' hq hT)

theorem FamDensityEpsRange.toFamDensityRange {σlo σhi c : ℝ} (h0 : 0 ≤ σlo)
    (h : FamDensityEpsRange σlo σhi c) : FamDensityRange σlo σhi c := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h (ε / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hsl hsh hT
  by_cases hσ1 : σ ≤ 1
  · have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      nlinarith
    refine le_trans (hh q hq σ T hsl hsh hT) ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
    refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
    have hnn : (0 : ℝ) ≤ 1 - σ := by linarith
    have hσ0 : (0 : ℝ) ≤ σ := le_trans h0 hsl
    have hle : (ε / 2) * (1 - σ) ≤ ε := by nlinarith
    nlinarith
  · push_neg at hσ1
    rw [famCount_eq_zero_of_one_lt q hσ1]
    exact mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (rpow_base_nonneg hq hT) _)

/-- A log-free estimate gives the version with a logarithmic power: for `B ≥ 0`,
`(log qT)^B ≥ (log 2)^B > 0` because `qT ≥ 2`, so the logarithmic factor is absorbed into the
constant. -/
theorem FamDensityEpsRange.toFamDensityPowerRange {σlo σhi c B : ℝ} (hB : 0 ≤ B)
    (h : FamDensityEpsRange σlo σhi c) : FamDensityPowerRange σlo σhi c B := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (Real.log 2) ^ B, by positivity, ?_⟩
  intro q hq _inst σ T hsl hsh hT
  have hbase2 : (2 : ℝ) ≤ (q : ℝ) * T := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * T := by linarith
  have hlogge : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hbase2
  have hpowlog : (Real.log 2) ^ B ≤ (Real.log ((q : ℝ) * T)) ^ B :=
    Real.rpow_le_rpow hlog2.le hlogge hB
  refine le_trans (hh q hq σ T hsl hsh hT) ?_
  have hCeq : C ≤ (C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B := by
    calc C = (C / (Real.log 2) ^ B) * (Real.log 2) ^ B := by
          rw [div_mul_cancel₀]; exact ne_of_gt (Real.rpow_pos_of_pos hlog2 B)
      _ ≤ (C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B :=
          mul_le_mul_of_nonneg_left hpowlog (by positivity)
  calc C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
      ≤ ((C / (Real.log 2) ^ B) * (Real.log ((q : ℝ) * T)) ^ B)
          * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)) :=
        mul_le_mul_of_nonneg_right hCeq (Real.rpow_nonneg hbase0 _)
    _ = C / (Real.log 2) ^ B * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
          * (Real.log ((q : ℝ) * T)) ^ B := by ring

/-! ## 4. Montgomery's sharp exponent plus the σ-blind count -/

/-- **The sharp Montgomery exponent implies the `12/5` exponent on `σ ≤ 3/4`.**  On `σ ≤ 3/4` one
has `3/(2-σ) ≤ 12/5`, so `3(1-σ)/(2-σ) + ε ≤ (12/5 + 4ε)(1-σ)` because `1 - σ ≥ 1/4`. -/
theorem montgomerySharp_to_powerRange {B : ℝ} (hB : 0 ≤ B) (h : MontgomerySharp B) :
    FamDensityPowerRange (1/2) (3/4) (12/5) B := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h (ε / 4) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hsl hsh hT
  have hbase1 : (1 : ℝ) ≤ (q : ℝ) * T := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hlog0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg hbase1
  have hσ1 : σ ≤ 1 := by linarith
  refine le_trans (hh q hq σ T hsl hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC))
    (Real.rpow_nonneg hlog0 B)
  refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
  have hden : (0 : ℝ) < 2 - σ := by linarith
  have hd : 3 / (2 - σ) ≤ 12 / 5 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    linarith
  have hmul : 3 * (1 - σ) / (2 - σ) = (3 / (2 - σ)) * (1 - σ) := by ring
  rw [hmul]
  have hquarter : (1 : ℝ) / 4 ≤ 1 - σ := by linarith
  have hA : (3 / (2 - σ)) * (1 - σ) ≤ (12 / 5) * (1 - σ) :=
    mul_le_mul_of_nonneg_right hd (by linarith)
  have hB : ε / 4 ≤ ε * (1 - σ) := by nlinarith
  linarith

/-- **The `12/5` family bound on `σ ≤ 3/4`, from the sharp Montgomery estimate alone.** -/
theorem famDensityPowerForm_three_quarters_of_montgomerySharp
    (h : ∀ B : ℝ, 0 < B → MontgomerySharp B) : FamDensityPowerForm 0 (3/4) (12/5) := by
  intro B hB
  have hB0 : (0 : ℝ) ≤ B := le_of_lt hB
  exact famDensityPowerRange_glue (σlo := 0) (m := 1/2) (σhi := 3/4) (c := 12/5) (B := B)
    (trivial_famDensityPowerRange (σlo := 0) (σhi := 1/2) (c := 12/5) (B := B)
      (by norm_num) le_rfl (by norm_num) hB0 (by norm_num))
    (montgomerySharp_to_powerRange hB0 (h B hB))

/-- **Gluing two ranges of `σ`** for the `ε`-in-the-base form. -/
theorem famDensityEpsRange_glue {σlo m σhi c c' : ℝ}
    (h1 : FamDensityEpsRange σlo m c) (h2 : FamDensityEpsRange m σhi c') :
    FamDensityEpsRange σlo σhi (max c c') := by
  intro ε hε
  obtain ⟨C1, hC1, hh1⟩ := h1 ε hε
  obtain ⟨C2, hC2, hh2⟩ := h2 ε hε
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro q hq _inst σ T hσlo hσhi hT
  have hnn : (0 : ℝ) ≤ (q : ℝ) * T := le_of_lt (rpow_base_pos hq hT)
  have hCmax : (0 : ℝ) < max C1 C2 := lt_of_lt_of_le hC1 (le_max_left _ _)
  by_cases hσ1 : σ ≤ 1
  · have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
    rcases le_total σ m with h | h
    · have hX : ((q : ℝ) * T) ^ ((c + ε) * (1 - σ))
          ≤ ((q : ℝ) * T) ^ ((max c c' + ε) * (1 - σ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (one_le_base hq hT) ?_
        nlinarith [le_max_left c c']
      refine le_trans (hh1 q hq σ T hσlo h hT) ?_
      refine le_trans (mul_le_mul_of_nonneg_right (le_max_left C1 C2)
        (Real.rpow_nonneg hnn _)) ?_
      exact mul_le_mul_of_nonneg_left hX (le_of_lt hCmax)
    · have hX : ((q : ℝ) * T) ^ ((c' + ε) * (1 - σ))
          ≤ ((q : ℝ) * T) ^ ((max c c' + ε) * (1 - σ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (one_le_base hq hT) ?_
        nlinarith [le_max_right c c']
      refine le_trans (hh2 q hq σ T h hσhi hT) ?_
      refine le_trans (mul_le_mul_of_nonneg_right (le_max_right C1 C2)
        (Real.rpow_nonneg hnn _)) ?_
      exact mul_le_mul_of_nonneg_left hX (le_of_lt hCmax)
  · push_neg at hσ1
    rw [famCount_eq_zero_of_one_lt q hσ1]
    exact mul_nonneg (le_of_lt hCmax) (Real.rpow_nonneg hnn _)

/-! ## 4b. From a log-free family density estimate to a log-free count at height `1` -/

/-- `FamDensityEpsRange 0 1 c` gives the `λ`-count at height `1` with exponent `c + δ` for every
`δ > 0` (the `ε` of the density estimate is paid for by `δ`). -/
theorem logFreeFamHalf_of_density {c δ : ℝ} (hδ : 0 < δ)
    (h : FamDensityEpsRange 0 1 c) : LogFreeFamHalf (c + δ) := by
  obtain ⟨C, hC, hh⟩ := h (min (δ / 2) 1) (lt_min (by linarith) one_pos)
  refine ⟨C, hC, 2, fun q hq _ σ h0 h1 => ?_⟩
  have hbase1 : (1 : ℝ) ≤ (q : ℝ) * 1 := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hstep := hh q hq σ 1 h0 h1 le_rfl
  simp only [mul_one] at hstep
  refine le_trans hstep ?_
  have hmin : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  have hexp : (c + min (δ / 2) 1) * (1 - σ) ≤ (c + δ) * (1 - σ) := by
    have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
    nlinarith
  calc (q : ℝ) ^ ((c + min (δ / 2) 1) * (1 - σ))
      = Real.exp (((c + min (δ / 2) 1) * (1 - σ)) * Real.log (q : ℝ)) := by
        rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < (q:ℝ))]
        ring_nf
    _ ≤ Real.exp (((c + δ) * (1 - σ)) * Real.log (q : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1m : (0 : ℝ) ≤ 1 - σ := by linarith
        nlinarith
    _ = Real.exp ((c + δ) * ((1 - σ) * Real.log (q : ℝ))) := by ring_nf

/-- `LogFreeFamHalf` is monotone in its exponent. -/
theorem LogFreeFamHalf.mono {c c' : ℝ} (h : c ≤ c') (hc : LogFreeFamHalf c) :
    LogFreeFamHalf c' := by
  obtain ⟨C, hC, q₀, hh⟩ := hc
  refine ⟨C, hC, max q₀ 2, fun q hq _ σ h0 h1 => ?_⟩
  have hq' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hlog0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (q : ℝ) := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hq)
      linarith
    exact this)
  refine le_trans (hh q hq' σ h0 h1) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  refine Real.exp_le_exp.mpr ?_
  have hnn : (0 : ℝ) ≤ (1 - σ) * Real.log (q : ℝ) := mul_nonneg (by linarith) hlog0
  nlinarith

/-! ## 5. The bridges to the Areas -/

/-- **Jutila's log-free bound** (`Work.LinnikAreas.FamilyZeroDensityJutila`, the Area 2 input)
follows from `FamDensityEpsRange (4/5) 1 2`. -/
theorem familyZeroDensityJutila_of_famDensityEpsRange (h : FamDensityEpsRange (4/5) 1 2) :
    Work.LinnikAreas.FamilyZeroDensityJutila := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  exact ⟨C, hC, fun q hq _ σ T hσ hσ1 hT => hh q hq σ T hσ hσ1 hT⟩

/-- **Montgomery's density theorem** (`Work.LinnikAreas.FamilyZeroDensityMontgomery`, the Area 2
input) follows from `FamDensityPowerForm 0 (4/5) (12/5)`. -/
theorem familyZeroDensityMontgomery_of_powerForm (h : FamDensityPowerForm 0 (4/5) (12/5)) :
    Work.LinnikAreas.FamilyZeroDensityMontgomery := by
  intro ε hε B hB
  obtain ⟨C, hC, hh⟩ := h B hB ε hε
  exact ⟨C, hC, fun q hq _ σ T h0 hσ hT => hh q hq σ T h0 hσ hT⟩

/-- **The Deuring–Heilbronn `λ₁`-saving count in the working region** is
`Work.LinnikAreas.Siegel.PairDensityInput` (the Area 6 input). -/
theorem pairDensityInput_of_dhLogFreeSpec (h : DHLogFreeSpec) :
    Work.LinnikAreas.Siegel.PairDensityInput := by
  obtain ⟨c, hc, C, hC, q₀, hh⟩ := h
  exact ⟨C, hC, c, hc, q₀, fun q hq _ χ₁ β₁ h1 h2 h3 h4 h5 t ht htq =>
    hh q hq χ₁ β₁ h1 h2 h3 h4 h5 t ht htq⟩

/-- **The Deuring–Heilbronn `λ₁`-saving count in the full height range** is
`Work.LinnikAreas.Siegel.PairDensityHeightInput` (the other Area 6 input). -/
theorem pairDensityHeightInput_of_dhLogFreeHeightSpec (h : DHLogFreeHeightSpec) :
    Work.LinnikAreas.Siegel.PairDensityHeightInput := by
  obtain ⟨c, c', hc, hc', C, hC, q₀, hh⟩ := h
  exact ⟨C, hC, c, hc, c', hc', q₀, fun q hq _ χ₁ β₁ h1 h2 h3 h4 h5 t T ht htq hT =>
    hh q hq χ₁ β₁ h1 h2 h3 h4 h5 t T ht htq hT⟩

end Work.ZeroDensity
