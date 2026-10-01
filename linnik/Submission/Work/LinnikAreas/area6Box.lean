import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.ZeroDensity.Basic

/-! The machinery of the *box part* of AREA 6 (HB §13–§14): the collapsing of the box sum to the exceptional term, the splitting of the far-zero sum, and the closing arithmetic.  Extracted from `LinnikAreas/area6.lean` so that the capped assembly (`LinnikAreas/boxSumCap.lean`) and the frozen target (`LinnikAreas/area6.lean`) can both use it without an import cycle. -/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option linter.unusedVariables false

namespace Siegel

open Work.LinnikContract

/-! ## 7. The box part of the zero sum, and the splitting of the far part

With the repulsion `λ(ρ) ≥ Λ := c_r log(1/λ₁)` in force and `Λ > R`, no zero other than the
exceptional one `β₁` lies in the box `InBox q R` (a zero with `|Im ρ| > 1` is outside it because
`|Im ρ|·𝓛 > 𝓛 > R`).  Hence

* the box sum of every `χ ≠ χ₁` vanishes, and the box sum of `χ₁` is the single exceptional term;
* the far-zero sum splits into the working region `|Im ρ| ≤ 1` (`restLowZeroSum`, controlled by the
  repulsion together with `PairDensityInput`) and the far heights (`restHighZeroSum`, controlled by
  `PairDensityHeightInput`). -/

open scoped Classical in
/-- **`‖χ a‖ = 1`** for a real character (`χ² = 1`) and `a` coprime to the level. -/
theorem norm_char_apply_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ^ 2 = 1)
    {a : ℕ} (ha : a.Coprime q) : ‖χ (a : ZMod q)‖ = 1 := by
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have h2 : χ (a : ZMod q) * χ (a : ZMod q) = 1 := by
    have hh : (χ * χ) (a : ZMod q) = 1 := by
      rw [show χ * χ = 1 from by rw [← pow_two]; exact h]
      exact MulChar.one_apply hu
    rwa [MulChar.mul_apply] at hh
  have h3 : ‖χ (a : ZMod q)‖ ^ 2 = 1 := by
    rw [pow_two, ← norm_mul, h2, norm_one]
  nlinarith [norm_nonneg (χ (a : ZMod q))]

/-- If every zero of the working region is repelled (`Λ ≤ λ(ρ)`), with `Λ > R` and `R < 𝓛`, then no
pair other than `(χ₁,β₁)` lies in the box. -/
theorem not_inBox_of_repulsion {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ}
    {R Λ : ℝ} (hq : 2 ≤ q) (hRlog : R < Real.log q)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ)
    (hΛR : R < Λ) :
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      ¬ InBox q R ρ := by
  intro χ ρ hz hne hbox
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  by_cases him : |ρ.im| ≤ 1
  · have h := hrep χ ρ hz him hne
    linarith [hbox.1, h]
  · have hlt : 1 < |ρ.im| := not_le.mp him
    have h2 : Real.log q < |ρ.im| * Real.log q := by nlinarith [hlt, hlog]
    linarith [hbox.2, h2]

/-- The box sum of any character `χ ≠ χ₁` vanishes in the Siegel case. -/
theorem boxSum_eq_zero_of_ne {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ}
    {R Λ : ℝ} (hq : 2 ≤ q) (hRlog : R < Real.log q)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ)
    (hΛR : R < Λ) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ χ₁) :
    boxSum q (11 / 2) (3 / 10) R χ = 0 := by
  rw [boxSum]
  rw [finsum_congr (g := fun _ => (0 : ℂ)) ?_, finsum_zero]
  intro ρ
  by_cases hbox : InBox q R ρ
  · have hz : zeroMult χ ρ = 0 := by
      by_contra hz
      exact not_inBox_of_repulsion hq hRlog hrep hΛR χ ρ hz (fun h => hχ h.1) hbox
    rw [if_pos hbox, hz]
    simp
  · rw [if_neg hbox]

/-- The box sum of `χ₁` is the single exceptional term. -/
theorem boxSum_eq_exceptional {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ}
    {R Λ : ℝ} (hq : 2 ≤ q) (hRlog : R < Real.log q)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ)
    (hΛR : R < Λ) (hR0 : 0 ≤ R) (hlamR : lamOf q (β₁ : ℂ) ≤ R) :
    boxSum q (11 / 2) (3 / 10) R χ₁
      = (zeroMult χ₁ (β₁ : ℂ) : ℂ) * Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ)) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  -- the box contains no zero of `χ₁` other than `β₁`
  have hzero : ∀ ρ : ℂ, ρ ≠ (β₁ : ℂ) → InBox q R ρ → zeroMult χ₁ ρ = 0 := by
    intro ρ hρ hbox
    by_contra hz
    have him : |ρ.im| ≤ 1 := by
      have h2 : |ρ.im| * Real.log q ≤ R := hbox.2
      have h3 : |ρ.im| * Real.log q < 1 * Real.log q := by simpa using lt_of_le_of_lt h2 hRlog
      exact le_of_lt (lt_of_mul_lt_mul_right h3 hlog.le)
    have h := hrep χ₁ ρ hz him (fun h => hρ h.2)
    linarith [hbox.1, h]
  rw [boxSum]
  rw [finsum_eq_single (f := fun ρ : ℂ => if InBox q R ρ then
      (zeroMult χ₁ ρ : ℂ) * Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ)) else 0)
    (β₁ : ℂ)]
  · rw [if_pos (show InBox q R (β₁ : ℂ) from ⟨hlamR, by
      simp only [Complex.ofReal_im, abs_zero, zero_mul]
      exact hR0⟩)]
  · intro ρ hρ
    by_cases hbox : InBox q R ρ
    · rw [if_pos hbox, hzero ρ hρ hbox]
      simp
    · rw [if_neg hbox]

/-- **The box sum is at most the exceptional term**: with the repulsion `Λ > R`, all box sums but
the exceptional one vanish, and `Re(χ̄₁(a)·Hk(λ₁)) ≤ ‖Hk(λ₁)‖`. -/
theorem signedBoxSumAll_le_exceptional {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {β₁ : ℝ}
    {R Λ : ℝ} (hq : 2 ≤ q) (hRlog : R < Real.log q) (hsq : χ₁ ^ 2 = 1)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ)
    (hΛR : R < Λ) (hR0 : 0 ≤ R) (hlamR : lamOf q (β₁ : ℂ) ≤ R)
    (hsimple : zeroMult χ₁ (β₁ : ℂ) = 1)
    {a : ℕ} (ha : a.Coprime q) :
    signedBoxSumAll q (11 / 2) (3 / 10) R a
      ≤ ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖ := by
  rw [signedBoxSumAll]
  rw [Finset.sum_eq_single χ₁]
  · have hnorm : ‖(starRingEnd ℂ) (χ₁ (a : ZMod q))‖ = 1 := by
      rw [Complex.norm_conj, norm_char_apply_eq_one hsq ha]
    rw [boxSum_eq_exceptional hq hRlog hrep hΛR hR0 hlamR, hsimple]
    simp only [Nat.cast_one, one_mul]
    refine le_trans (Complex.re_le_norm _) (le_of_eq ?_)
    rw [norm_mul, hnorm, one_mul]
  · intro χ _ hχ
    rw [boxSum_eq_zero_of_ne hq hRlog hrep hΛR hχ]
    simp
  · intro h
    exact absurd (Finset.mem_univ χ₁) h

/-- **The far-zero sum splits** into the working region (`|Im ρ| ≤ 1`) and the far heights
(`1 < |Im ρ|`): every pair other than the exceptional one is outside the box, and each is counted
in exactly one of the two pieces.  The hypothesis `hsum` is the summability of the kernel-weighted
zero sum (proved in `Submission.Work.LinnikAreas.siegelZeroWeightSummable`). -/
theorem farZeroSum_le_restLow_add_restHigh {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q}
    {β₁ : ℝ} {R Λ : ℝ} (hq : 2 ≤ q) (hRlog : R < Real.log q)
    (hrep : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Λ ≤ lamOf q ρ)
    (hΛR : R < Λ) (hlamR : lamOf q (β₁ : ℂ) ≤ R) (him0 : |(β₁ : ℂ).im| * Real.log q ≤ R)
    (hsum : ∀ χ : DirichletCharacter ℂ q, Summable (fun ρ : ℂ => (zeroMult χ ρ : ℝ) *
      ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖)) :
    farZeroSum q (11 / 2) (3 / 10) R
      ≤ restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        + restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) := by
  rw [farZeroSum, restLowZeroSum, restHighZeroSum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun χ _ => ?_
  have hMnn : ∀ ρ : ℂ, 0 ≤ (zeroMult χ ρ : ℝ) *
      ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ :=
    fun ρ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hMsum : Summable (fun ρ : ℂ => (zeroMult χ ρ : ℝ) *
      ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖) := hsum χ
  have hlow_sum : Summable (fun ρ : ℂ => if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then (zeroMult χ ρ : ℝ) *
        ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hMsum
    · by_cases h : zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
      · rw [if_pos h]
        exact hMnn ρ
      · rw [if_neg h]
    · by_cases h : zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
      · rw [if_pos h]
      · rw [if_neg h]
        exact hMnn ρ
  have hhigh_sum : Summable (fun ρ : ℂ => if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then (zeroMult χ ρ : ℝ) *
        ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hMsum
    · by_cases h : zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
      · rw [if_pos h]
        exact hMnn ρ
      · rw [if_neg h]
    · by_cases h : zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ))
      · rw [if_pos h]
      · rw [if_neg h]
        exact hMnn ρ
  have hfar_le : ∀ ρ : ℂ, (if InBox q R ρ then 0 else (zeroMult χ ρ : ℝ) *
        ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖)
      ≤ (if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0)
        + (if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) := by
    intro ρ
    by_cases hz : zeroMult χ ρ = 0
    · have hzero : (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10)
          ((1 - ρ) * (Real.log q : ℂ))‖ = 0 := by
        rw [hz]
        simp
      rw [hzero]
      by_cases hbox : InBox q R ρ <;> simp [hbox]
    · by_cases hexc : χ = χ₁ ∧ ρ = (β₁ : ℂ)
      · have hbox : InBox q R ρ := by
          rw [hexc.2]
          exact ⟨hlamR, him0⟩
        have h1 : (if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) = 0 := by
          rw [if_neg]
          rintro ⟨-, -, h⟩
          exact h hexc
        have h2 : (if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) = 0 := by
          rw [if_neg]
          rintro ⟨-, -, h⟩
          exact h hexc
        rw [if_pos hbox, h1, h2]
        simp
      · have hnotin : ¬ InBox q R ρ := not_inBox_of_repulsion hq hRlog hrep hΛR χ ρ hz hexc
        rw [if_neg hnotin]
        by_cases him : |ρ.im| ≤ 1
        · have h2 : (if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) = 0 := by
            rw [if_neg]
            rintro ⟨-, hlt, -⟩
            exact absurd hlt (not_lt.mpr him)
          rw [if_pos ⟨hz, him, hexc⟩, h2]
          simp
        · have hlt : 1 < |ρ.im| := not_le.mp him
          have h1 : (if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
              (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) = 0 := by
            rw [if_neg]
            rintro ⟨-, hle, -⟩
            exact absurd hle (not_le.mpr hlt)
          rw [h1, if_pos ⟨hz, hlt, hexc⟩]
          simp
  have hfar_sum : Summable (fun ρ : ℂ => if InBox q R ρ then 0 else (zeroMult χ ρ : ℝ) *
      ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) hfar_le (hlow_sum.add hhigh_sum)
    by_cases hbox : InBox q R ρ
    · rw [if_pos hbox]
    · rw [if_neg hbox]
      exact hMnn ρ
  calc (∑' ρ : ℂ, if InBox q R ρ then 0 else (zeroMult χ ρ : ℝ) *
        ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖)
      ≤ ∑' ρ : ℂ, ((if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0)
          + (if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0)) :=
        Summable.tsum_le_tsum hfar_le hfar_sum (hlow_sum.add hhigh_sum)
    _ = (∑' ρ : ℂ, if zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0)
          + ∑' ρ : ℂ, (if zeroMult χ ρ ≠ 0 ∧ 1 < |ρ.im| ∧ ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) then
            (zeroMult χ ρ : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖ else 0) :=
        Summable.tsum_add hlow_sum hhigh_sum

/-! ## 6. The closing arithmetic of the Siegel case

The two lemmas below are pure real arithmetic: they turn the three estimates

* exceptional zero: `‖Hk L K ((1-β₁)𝓛)‖ ≤ K²e^{-a₀λ₁}`,
* working region: `restLowZeroSum ≤ C₁λ₁^{1+δ}` (`δ > 0`),
* far heights: `restHighZeroSum ≤ C₂λ₁𝓛^{e}` (`e < 0`),

into `BoxSumBound`.  The exponential slack `(1 - e^{-a₀λ₁}) - a₀λ₁/2 ≥ a₀λ₁/4` (valid for
`a₀λ₁ ≤ 2/5`) is what pays for the two error terms, and the two thresholds
`λ₁ ≤ (K²a₀/(8C₁))^{1/δ}` and `𝓛^{e} ≤ K²a₀/(8C₂)` are what make them fit. -/

/-- For `0 ≤ t ≤ 2/5`, `e^{-t} ≤ 1 - 3t/4`; equivalently `(1 - e^{-t}) - t/2 ≥ t/4`. -/
theorem exp_neg_le_one_sub_three_quarters {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5) :
    Real.exp (-t) ≤ 1 - 3 * t / 4 := by
  have hsum := Real.sum_le_exp_of_nonneg (x := t) ht0 3
  have hval : (∑ i ∈ Finset.range 3, t ^ i / ((i.factorial : ℕ) : ℝ)) = 1 + t + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hval] at hsum
  have hpos : 0 < 1 + t + t ^ 2 / 2 := by positivity
  calc Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    _ ≤ (1 + t + t ^ 2 / 2)⁻¹ := inv_anti₀ hpos hsum
    _ ≤ 1 - 3 * t / 4 := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith [ht0, ht, sq_nonneg t]

/-- **The closing inequality of the Siegel case.**  If the working-region zeros contribute
`C₁λ^{1+δ}` (`δ > 0`) and the far zeros contribute `C₂λ𝓛^{e}` (`e < 0`), while `𝓛^{e}` is so small
that `C₂𝓛^{e} ≤ K²a₀/8`, then for `λ ≤ lamS` small,

`K²e^{-a₀λ} + C₁λ^{1+δ} + C₂λ𝓛^{e} ≤ K²(1 - a₀λ/2)`,

which is exactly the `BoxSumBound` inequality. -/
theorem siegel_close_arith {K a₀ C₁ δ C₂ e Lq : ℝ} (hK : 0 < K) (ha₀ : 0 < a₀) (hC₁ : 0 < C₁)
    (hδ : 0 < δ) (hC₂ : 0 ≤ C₂) (he : e < 0) (hLq : 1 ≤ Lq)
    (hC₂L : C₂ * Lq ^ e ≤ K ^ 2 * a₀ / 8) :
    let lamS : ℝ := min (min (1 / 2) (2 / (5 * a₀))) ((K ^ 2 * a₀ / (8 * C₁)) ^ (1 / δ))
    ∀ x : ℝ, 0 < x → x ≤ lamS →
      K ^ 2 * Real.exp (-(a₀ * x)) + C₁ * x ^ (1 + δ) + C₂ * x * Lq ^ e
        ≤ K ^ 2 * (1 - a₀ * x / 2) := by
  intro lamS x hx0 hxle
  have hxs : x ≤ min (1 / 2) (2 / (5 * a₀)) := le_trans hxle (min_le_left _ _)
  have hxA : x ≤ (K ^ 2 * a₀ / (8 * C₁)) ^ (1 / δ) := le_trans hxle (min_le_right _ _)
  have hx12 : x ≤ 1 / 2 := le_trans hxs (min_le_left _ _)
  have hxa₀ : x ≤ 2 / (5 * a₀) := le_trans hxs (min_le_right _ _)
  have hApos : 0 < K ^ 2 * a₀ / (8 * C₁) := by positivity
  have hxδ : x ^ δ ≤ K ^ 2 * a₀ / (8 * C₁) := by
    calc x ^ δ ≤ ((K ^ 2 * a₀ / (8 * C₁)) ^ (1 / δ)) ^ δ := Real.rpow_le_rpow hx0.le hxA hδ.le
      _ = K ^ 2 * a₀ / (8 * C₁) := by
          rw [← Real.rpow_mul hApos.le]
          have h1 : (1 / δ) * δ = 1 := by field_simp
          rw [h1, Real.rpow_one]
  -- working region
  have hnoise1 : C₁ * x ^ (1 + δ) ≤ K ^ 2 * a₀ / 8 * x := by
    have h2 : C₁ * x ^ δ ≤ K ^ 2 * a₀ / 8 := by
      have h3 := mul_le_mul_of_nonneg_left hxδ hC₁.le
      have h4 : C₁ * (K ^ 2 * a₀ / (8 * C₁)) = K ^ 2 * a₀ / 8 := by field_simp
      rwa [h4] at h3
    rw [Real.rpow_add hx0, Real.rpow_one]
    nlinarith [h2, hx0]
  -- far heights
  have hnoise2 : C₂ * x * Lq ^ e ≤ K ^ 2 * a₀ / 8 * x := by
    have h2 : C₂ * Lq ^ e ≤ K ^ 2 * a₀ / 8 := hC₂L
    nlinarith [h2, hx0]
  -- the exceptional zero
  have hax : a₀ * x ≤ 2 / 5 := by
    have h3 : a₀ * x ≤ a₀ * (2 / (5 * a₀)) := mul_le_mul_of_nonneg_left hxa₀ ha₀.le
    have h4 : a₀ * (2 / (5 * a₀)) = 2 / 5 := by field_simp
    linarith [h3, h4]
  have hexp := exp_neg_le_one_sub_three_quarters (by positivity : 0 ≤ a₀ * x) hax
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hmain : K ^ 2 * Real.exp (-(a₀ * x)) ≤ K ^ 2 * (1 - 3 * (a₀ * x) / 4) :=
    mul_le_mul_of_nonneg_left hexp hK2
  linarith [hmain, hnoise1, hnoise2, hK2, ha₀, hx0]

end Siegel

end

end Work.LinnikAreas
