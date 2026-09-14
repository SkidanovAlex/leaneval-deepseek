import Submission.NBody.MarchalModelInstantiate

/-!
# The two-sided model negativity: FT's circle-average device

The symmetric change of variables replaces one and the same displacement `δ` on **both** sides of the
collision time.  Ferrario--Terracini's `theo:aa` shows that the average over a circle of directions
of the model action difference is negative; the decisive point for the two-sided version is that
the `θ`-average of the **sum** of the two sides' model differences is negative as well (the cross
terms average to `0` and the quadratic terms are `θ`-independent), so there is a single direction `δ`
for which the sum is `< 0`.

We also arrange that `δ` avoids a prescribed **finite** set of exceptional directions (the directions
parallel to a pair separation, for which the bumped profile could meet a collision): this is the
"good direction" condition.  The tool is the elementary observation that a finite set is null for the
Lebesgue measure, so an integral can only be negative if some point outside the finite set is.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Avoiding a finite bad set.**  If a function has negative integral over `(0, 2π)` then it takes
a negative value at some point of `[0, 2π]` outside any prescribed finite set. -/
theorem exists_notMem_of_integral_neg {f : ℝ → ℝ} {B : Set ℝ} (hB : volume B = 0)
    (hint : (∫ θ in (0:ℝ)..(2 * Real.pi), f θ) < 0) :
    ∃ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), θ ∉ B ∧ f θ < 0 := by
  by_contra hcon
  push_neg at hcon
  have hpi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  set g : ℝ → ℝ := fun θ => if θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) then f θ else 0 with hg
  have heq : (∫ θ in (0:ℝ)..(2 * Real.pi), g θ) = ∫ θ in (0:ℝ)..(2 * Real.pi), f θ := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hpi]
    filter_upwards with θ hθ
    rw [hg]
    simp only [hθ, if_true]
  have hnn : 0 ≤ ∫ θ in (0:ℝ)..(2 * Real.pi), g θ := by
    refine intervalIntegral.integral_nonneg_of_ae hpi ?_
    show ∀ᵐ θ ∂(volume : Measure ℝ), 0 ≤ g θ
    rw [ae_iff]
    refine measure_mono_null ?_ hB
    intro θ hθ
    simp only [mem_setOf_eq] at hθ
    by_contra hmem
    rw [hg] at hθ
    by_cases hI : θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi)
    · simp only [hI, if_true] at hθ
      exact hθ (hcon θ ⟨hI.1.le, hI.2⟩ hmem)
    · simp only [hI, if_false] at hθ
      exact hθ le_rfl
  rw [heq] at hnn
  linarith

end Submission.NBody

namespace Submission.NBody

/-- **FT's circle average, two-sided.**  Averaging the *sum* of the two sides' model action
differences over the circle of directions of radius `ρ`, the cross terms average to `0`, the
quadratic terms contribute `ρ · stdPertCoefSq`, and the potential terms contribute at most
`-(AR+AL)√ρ + (BR+BL)ρ²`; for small `ρ` the total is negative, hence some direction `δ` of the
circle has `modelDiff_R δ + modelDiff_L δ < 0` (and avoids any prescribed finite set of
exceptional directions). -/
theorem exists_model_dir_negative_two_sided_avoid {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κR κL T : ℝ} (hκR : 0 < κR) (hκL : 0 < κL)
    (hT : 0 < T) (sbarR sbarL : EN E N) (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {B : Set ℝ} (hB : volume B = 0)
    {AR AL BR BL ρmax : ℝ} (hA : 0 < AR + AL) (hBR : 0 ≤ BR) (hBL : 0 ≤ BL)
    (hρmax : 0 < ρmax) (hρmaxT : ρmax ≤ T / 2)
    (hpotR : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κR sbarR T (ρ • circleDir e f θ)
          ≤ -AR * ρ ^ ((1:ℝ)/2) + BR * ρ ^ 2)
    (hpotL : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κL sbarL T (ρ • circleDir e f θ)
          ≤ -AL * ρ ^ ((1:ℝ)/2) + BL * ρ ^ 2)
    :
    ∃ ρ > (0:ℝ), ρ ≤ ρmax ∧ ∃ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), θ ∉ B ∧
      modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
        + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ) < 0 := by
  classical
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    Commons.Analysis.Asymptotic.exists_pos_forall_neg_rpow_half_add
      (A := AR + AL) (B := stdPertCoefSq m k i₀) (C := BR + BL)
      hA (stdPertCoefSq_nonneg (fun i => (hm i).le) k i₀) (by linarith)
  set ρ : ℝ := min ρ₀ ρmax / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos (lt_min hρ₀pos hρmax) (by norm_num)
  have hρltρ₀ : ρ < ρ₀ := by
    rw [hρdef]; have := min_le_left ρ₀ ρmax; linarith
  have hρltρmax : ρ < ρmax := by
    rw [hρdef]; have := min_le_right ρ₀ ρmax; linarith
  have hρT : ρ ≤ T := by rw [hρdef]; linarith
  have hρT2 : ρ ≤ T / 2 := by rw [hρdef]; linarith
  have hmem : ρ ∈ Set.Ioo (0:ℝ) ρmax := ⟨hρpos, hρltρmax⟩
  -- continuity of the kinetic parts, for each side
  have hcrosscontR : Continuous (fun θ : ℝ =>
      modelCrossVal m k i₀ κR sbarR T (ρ • circleDir e f θ)) := by
    have hpt : (fun θ : ℝ => modelCrossVal m k i₀ κR sbarR T (ρ • circleDir e f θ))
        = fun θ => (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κR * t ^ (-(1:ℝ)/3)) *
              (if t ≤ T - ρ then 0 else -1))
            * (massInner m sbarR (stdPertVec m k i₀ e) * Real.cos θ
              + massInner m sbarR (stdPertVec m k i₀ f) * Real.sin θ) := by
      funext θ
      rw [modelCrossVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT sbarR e f θ
          (norm_circleDir he hf hef θ),
        stdPertVec_circleDir, massInner_add_right, massInner_smul_right, massInner_smul_right]
      ring
    rw [hpt]
    fun_prop
  have hcrosscontL : Continuous (fun θ : ℝ =>
      modelCrossVal m k i₀ κL sbarL T (ρ • circleDir e f θ)) := by
    have hpt : (fun θ : ℝ => modelCrossVal m k i₀ κL sbarL T (ρ • circleDir e f θ))
        = fun θ => (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κL * t ^ (-(1:ℝ)/3)) *
              (if t ≤ T - ρ then 0 else -1))
            * (massInner m sbarL (stdPertVec m k i₀ e) * Real.cos θ
              + massInner m sbarL (stdPertVec m k i₀ f) * Real.sin θ) := by
      funext θ
      rw [modelCrossVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT sbarL e f θ
          (norm_circleDir he hf hef θ),
        stdPertVec_circleDir, massInner_add_right, massInner_smul_right, massInner_smul_right]
      ring
    rw [hpt]
    fun_prop
  have hquadcont : Continuous (fun θ : ℝ => modelQuadVal m k i₀ T (ρ • circleDir e f θ)) := by
    have hpt : (fun θ : ℝ => modelQuadVal m k i₀ T (ρ • circleDir e f θ))
        = fun _ => (1/2) * ρ * stdPertCoefSq m k i₀ := funext fun θ =>
      modelQuadVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT e f θ
        (norm_circleDir he hf hef θ)
    rw [hpt]
    exact continuous_const
  have hcrossR : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelCrossVal m k i₀ κR sbarR T (ρ • circleDir e f θ)) = 0 :=
    circleAvg_modelCrossVal (κ := κR) (sbar := sbarR) (fun i => (hm i).le) k i₀
      hT hρpos hρT e f he hf hef
  have hcrossL : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelCrossVal m k i₀ κL sbarL T (ρ • circleDir e f θ)) = 0 :=
    circleAvg_modelCrossVal (κ := κL) (sbar := sbarL) (fun i => (hm i).le) k i₀
      hT hρpos hρT e f he hf hef
  have hquad : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelQuadVal m k i₀ T (ρ • circleDir e f θ)) = (1/2) * ρ * stdPertCoefSq m k i₀ :=
    circleAvg_modelQuadVal (T := T) (ρ := ρ) (fun i => (hm i).le) k i₀ hT hρpos
      hρT e f he hf hef
  -- the decomposition of each side's θ-integral
  have hdecomp : ∀ (κ : ℝ) (sbar : EN E N), 0 < κ →
      (∫ θ in (0:ℝ)..(2*Real.pi), modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
        = (∫ θ in (0:ℝ)..(2*Real.pi), modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ))
          + (∫ θ in (0:ℝ)..(2*Real.pi), modelQuadVal m k i₀ T (ρ • circleDir e f θ))
          + (∫ θ in (0:ℝ)..(2*Real.pi), modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
    intro κ sbar hκpos
    have hcont1 : Continuous (fun θ : ℝ => modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
      have hpt : (fun θ : ℝ => modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ))
          = fun θ => (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
                (if t ≤ T - ρ then 0 else -1))
              * (massInner m sbar (stdPertVec m k i₀ e) * Real.cos θ
                + massInner m sbar (stdPertVec m k i₀ f) * Real.sin θ) := by
        funext θ
        rw [modelCrossVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT sbar e f θ
            (norm_circleDir he hf hef θ),
          stdPertVec_circleDir, massInner_add_right, massInner_smul_right, massInner_smul_right]
        ring
      rw [hpt]
      fun_prop
    have hcont2 : Continuous (fun θ : ℝ => modelQuadVal m k i₀ T (ρ • circleDir e f θ)) := by
      have hpt : (fun θ : ℝ => modelQuadVal m k i₀ T (ρ • circleDir e f θ))
          = fun _ => (1/2) * ρ * stdPertCoefSq m k i₀ := funext fun θ =>
        modelQuadVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT e f θ
          (norm_circleDir he hf hef θ)
      rw [hpt]
      exact continuous_const
    have hint : IntervalIntegrable (fun θ : ℝ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        volume 0 (2*Real.pi) :=
      intervalIntegrable_modelPotVal_circle hκpos hT hρpos sbar e f he hf hef
    rw [show (fun θ : ℝ => modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
        = fun θ => (modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)
            + modelQuadVal m k i₀ T (ρ • circleDir e f θ))
            + modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ) from rfl]
    rw [intervalIntegral.integral_add (μ := volume)
      ((hcont1.intervalIntegrable _ _).add (hcont2.intervalIntegrable _ _)) hint]
    rw [intervalIntegral.integral_add (μ := volume) (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
  have htotR := hdecomp κR sbarR hκR
  have htotL := hdecomp κL sbarL hκL
  -- integrability of `modelDiff ∘ δ` for each side
  have hintR : IntervalIntegrable
      (fun θ => modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)) volume 0 (2*Real.pi) := by
    rw [show (fun θ : ℝ => modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ))
        = fun θ => (modelCrossVal m k i₀ κR sbarR T (ρ • circleDir e f θ)
            + modelQuadVal m k i₀ T (ρ • circleDir e f θ))
            + modelPotVal m k i₀ κR sbarR T (ρ • circleDir e f θ) from rfl]
    exact ((hcrosscontR.intervalIntegrable _ _).add (hquadcont.intervalIntegrable _ _)).add
      (intervalIntegrable_modelPotVal_circle hκR hT hρpos sbarR e f he hf hef)
  have hintL : IntervalIntegrable
      (fun θ => modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ)) volume 0 (2*Real.pi) := by
    rw [show (fun θ : ℝ => modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ))
        = fun θ => (modelCrossVal m k i₀ κL sbarL T (ρ • circleDir e f θ)
            + modelQuadVal m k i₀ T (ρ • circleDir e f θ))
            + modelPotVal m k i₀ κL sbarL T (ρ • circleDir e f θ) from rfl]
    exact ((hcrosscontL.intervalIntegrable _ _).add (hquadcont.intervalIntegrable _ _)).add
      (intervalIntegrable_modelPotVal_circle hκL hT hρpos sbarL e f he hf hef)
  have hsumint : (∫ θ in (0:ℝ)..(2*Real.pi),
        (modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
          + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ)))
      = (∫ θ in (0:ℝ)..(2*Real.pi), modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ))
        + (∫ θ in (0:ℝ)..(2*Real.pi), modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ)) :=
    intervalIntegral.integral_add (μ := volume) hintR hintL
  -- the explicit value of the average
  have hub : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        (modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
          + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ)))
      ≤ -(AR + AL) * ρ ^ ((1:ℝ)/2) + stdPertCoefSq m k i₀ * ρ + (BR + BL) * ρ ^ 2 := by
    have hpR := hpotR ρ hmem
    have hpL := hpotL ρ hmem
    rw [hsumint, htotR, htotL, mul_add, mul_add, mul_add]
    linarith [hcrossR, hcrossL, hquad, hpR, hpL]
  have hneg : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        (modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
          + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ))) < 0 :=
    lt_of_le_of_lt hub (hρ₀ ρ ⟨hρpos, hρltρ₀⟩)
  have hlt : (∫ θ in (0:ℝ)..(2*Real.pi),
        (modelDiff m k i₀ κR sbarR T (ρ • circleDir e f θ)
          + modelDiff m k i₀ κL sbarL T (ρ • circleDir e f θ))) < 0 := by
    have h := mul_lt_mul_of_pos_left hneg hpi
    rw [← mul_assoc, one_div, mul_inv_cancel₀ hpi.ne', one_mul, mul_zero] at h
    exact h
  obtain ⟨θ, hθI, hθB, hθneg⟩ := exists_notMem_of_integral_neg hB hlt
  exact ⟨ρ, hρpos, hρltρmax.le, θ, hθI, hθB, hθneg⟩

end Submission.NBody
