import Mathlib.CategoryTheory.Countable
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc13_differentiableAt`

The clean fibre `pairGc13 ℓ p hp Θ₀ A B` of `pairGCore` is the map

    (w, y) ↦ ∫_{x' ∈ boxPiSet ℓ} ∫_{u ∈ boxL ℓ}
        star (Θ₀ (insertCoord p.2 w x')) * A (x' p.1) * star (B u) * Θ₀ (confY13 p y u x')

and it is differentiable in its first variable `w`.  The variable `w` enters only through the
`C^∞` factor `Θ₀ (insertCoord p.2 · x')`, whose derivative is bounded on the compact box (thanks to
`ContDiff ℝ ⊤ Θ₀`), while the remaining factors enter only through the two bounds
`‖A ·‖ ≤ cA`, `‖B ·‖ ≤ cB`.  This is exactly the situation covered by Mathlib's parametric
differentiation under the integral sign
`MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The two elementary continuous linear maps -/

/-- The insertion of a vector into slot `j`, as a continuous linear map. -/
noncomputable def insCLM {n : ℕ} (j : Fin n) : E3 →L[ℝ] (Fin n → E3) :=
  ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) j

/-- Complex conjugation, as an `ℝ`-linear isometry of `ℂ`. -/
noncomputable def conjCLM : ℂ →L[ℝ] ℂ := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)

lemma conjCLM_apply (z : ℂ) : conjCLM z = star z := by
  rw [conjCLM]
  exact starL'_apply ℝ z

lemma insCLM_apply {n : ℕ} (j : Fin n) (v : E3) : insCLM j v = Pi.single j v := by
  rw [insCLM, ContinuousLinearMap.single_apply]

/-- The insertion map is the linear map `insCLM` plus the constant fibre. -/
lemma insertCoord_eq_insCLM {n : ℕ} (p : Fin n × Fin n)
    (z : ({k : Fin n // k ≠ p.2} → E3) × E3) (w : E3) :
    insertCoord p.2 w z.1 = insCLM p.2 w + insertCoord p.2 0 z.1 := by
  funext k
  simp only [Pi.add_apply, insCLM, ContinuousLinearMap.single_apply, Pi.single_apply,
    insertCoord_eq]
  split_ifs <;> simp_all

/-- The derivative of `w ↦ insertCoord p.2 w x'`. -/
lemma hasFDerivAt_insertCoord {n : ℕ} (p : Fin n × Fin n)
    (z : ({k : Fin n // k ≠ p.2} → E3) × E3) (x : E3) :
    HasFDerivAt (fun w : E3 => insertCoord p.2 w z.1) (insCLM p.2) x := by
  rw [show (fun w : E3 => insertCoord p.2 w z.1)
      = fun w => insCLM p.2 w + insertCoord p.2 0 z.1 from by
    funext w; exact insertCoord_eq_insCLM p z w]
  exact (ContinuousLinearMap.hasFDerivAt (insCLM p.2)).add_const _

/-! ## 2. Continuity of the configuration maps -/

/-- `z ↦ insertCoord j w z.1` is continuous (the value `w` is held fixed). -/
lemma continuous_insertCoord_fst {n : ℕ} (j : Fin n) (w : E3) :
    Continuous (fun z : ({k : Fin n // k ≠ j} → E3) × E3 => insertCoord j w z.1) := by
  rw [continuous_pi_iff]
  intro k
  by_cases hk : k = j
  · have h : (fun z : ({k : Fin n // k ≠ j} → E3) × E3 =>
        insertCoord j w z.1 k) = fun _ => w := by
      funext z; simp only [insertCoord_eq]; rw [dif_pos hk]
    rw [h]; exact continuous_const
  · have h : (fun z : ({k : Fin n // k ≠ j} → E3) × E3 =>
        insertCoord j w z.1 k) = fun z => z.1 ⟨k, hk⟩ := by
      funext z; simp only [insertCoord_eq]; rw [dif_neg hk]
    rw [h]; exact (continuous_apply _).comp continuous_fst

/-- `(w, x') ↦ insertCoord j w x'` is continuous in both variables. -/
lemma continuous_insertCoord_pair {n : ℕ} (j : Fin n) :
    Continuous (fun q : E3 × (({k : Fin n // k ≠ j} → E3) × E3) =>
      insertCoord j q.1 q.2.1) := by
  rw [continuous_pi_iff]
  intro k
  by_cases hk : k = j
  · have h : (fun q : E3 × (({k : Fin n // k ≠ j} → E3) × E3) =>
        insertCoord j q.1 q.2.1 k) = fun q => q.1 := by
      funext q; simp only [insertCoord_eq]; rw [dif_pos hk]
    rw [h]; exact continuous_fst
  · have h : (fun q : E3 × (({k : Fin n // k ≠ j} → E3) × E3) =>
        insertCoord j q.1 q.2.1 k) = fun q => q.2.1 ⟨k, hk⟩ := by
      funext q; simp only [insertCoord_eq]; rw [dif_neg hk]
    rw [h]; exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)

/-- `z ↦ confY13 p y z.2 z.1` is continuous. -/
lemma continuous_confY13_pair {n : ℕ} (p : Fin n × Fin n) (y : E3) :
    Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
      confY13 p y z.2 z.1) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        confY13 p y z.2 z.1 k) = fun _ => y := by
      funext z; simp only [confY13]; rw [dif_pos h1]
    rw [h]; exact continuous_const
  · by_cases h2 : k = p.2
    · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
          confY13 p y z.2 z.1 k) = fun z => z.2 := by
        funext z; simp only [confY13]; rw [dif_neg h1, dif_pos h2]
      rw [h]; exact continuous_snd
    · have h : (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
          confY13 p y z.2 z.1 k) = fun z => z.1 ⟨k, h2⟩ := by
        funext z; simp only [confY13]; rw [dif_neg h1, dif_neg h2]
      rw [h]; exact (continuous_apply _).comp continuous_fst

/-! ## 3. The norm of a scalar multiple of a continuous linear map -/

/-- The pointwise `ℂ`-action on `E3 →L[ℝ] ℂ` is submultiplicative for the operator norm. -/
lemma norm_smul_clm_le (d : ℂ) (L : E3 →L[ℝ] ℂ) : ‖d • L‖ ≤ ‖d‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc ‖d * L v‖ ≤ ‖d‖ * ‖L v‖ := norm_mul_le _ _
    _ ≤ ‖d‖ * (‖L‖ * ‖v‖) := mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg _)
    _ = ‖d‖ * ‖L‖ * ‖v‖ := by ring

/-! ## 4. The integrand and the derivative candidate -/

/-- The integrand of the clean fibre `pairGc13`, with the `w`-variable first. -/
noncomputable def gc13Int {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (Θ₀ : Xn n → ℂ)
    (A B : E3 → ℂ) (y : E3) : E3 → (({k : Fin n // k ≠ p.2} → E3) × E3) → ℂ :=
  fun w z => star (Θ₀ (insertCoord p.2 w z.1)) * A (z.1 ⟨p.1, hp⟩) * star (B z.2)
    * Θ₀ (confY13 p y z.2 z.1)

lemma pairGc13_eq_setIntegral_gc13Int {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ₀ : Xn n → ℂ) (A B : E3 → ℂ) (y w : E3) :
    pairGc13 ℓ p hp Θ₀ A B w y
      = ∫ z in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
          gc13Int p hp Θ₀ A B y w z := rfl

/-- The candidate derivative of `w ↦ gc13Int p hp Θ₀ A B y w z` at `x`. -/
noncomputable def gc13Deriv {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (Θ₀ : Xn n → ℂ)
    (A B : E3 → ℂ) (y : E3) (x : E3) (z : ({k : Fin n // k ≠ p.2} → E3) × E3) :
    E3 →L[ℝ] ℂ :=
  Θ₀ (confY13 p y z.2 z.1) • (star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
    (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)))))

/-! ## 5. The theorem -/

theorem pairGc13_differentiableAt {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (y w : EuclideanSpace ℝ (Fin 3)) :
    DifferentiableAt ℝ (fun w' => Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B w' y) w := by
  classical
  have hcA : 0 ≤ cA := (norm_nonneg (A 0)).trans (hAb 0)
  have hcB : 0 ≤ cB := (norm_nonneg (B 0)).trans (hBb 0)
  -- the integration domain
  set box : Set (({k : Fin n // k ≠ p.2} → E3) × E3) :=
    boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ with hboxdef
  have hboxc : IsCompact box := by
    rw [hboxdef]
    exact (isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.2}) hℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have hboxm : MeasurableSet box := hboxc.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict box) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxc.measure_lt_top⟩
  -- ## the three bounds
  obtain ⟨Mfd, hMfd0, hMfd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Metric.closedBall w 1,
      ∀ z ∈ box, ‖fderiv ℝ Θ₀ (insertCoord p.2 x z.1)‖ ≤ M := by
    have hK : IsCompact ((fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        insertCoord p.2 q.1 q.2.1) '' (Metric.closedBall w 1 ×ˢ box)) :=
      ((isCompact_closedBall w 1).prod hboxc).image (continuous_insertCoord_pair p.2)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun q : Xn n => fderiv ℝ Θ₀ q) (hΘ₀.continuous_fderiv (by simp)).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx z hz =>
      (hC _ ⟨(x, z), ⟨hx, hz⟩, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨MΘ, hMΘ0, hMΘ⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Metric.closedBall w 1,
      ∀ z ∈ box, ‖Θ₀ (insertCoord p.2 x z.1)‖ ≤ M := by
    have hK : IsCompact ((fun q : E3 × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        insertCoord p.2 q.1 q.2.1) '' (Metric.closedBall w 1 ×ˢ box)) :=
      ((isCompact_closedBall w 1).prod hboxc).image (continuous_insertCoord_pair p.2)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ₀.continuous.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx z hz =>
      (hC _ ⟨(x, z), ⟨hx, hz⟩, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨MY, hMY0, hMY⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ box,
      ‖Θ₀ (confY13 p y z.2 z.1)‖ ≤ M := by
    have hK : IsCompact ((fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        confY13 p y z.2 z.1) '' box) := hboxc.image (continuous_confY13_pair p y)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ₀.continuous.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun z hz =>
      (hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩
  -- ## measurability of the integrand in `z`
  have hFmeas : ∀ x : E3, Measurable (gc13Int p hp Θ₀ A B y x) := by
    intro x
    have h1 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        star (Θ₀ (insertCoord p.2 x z.1))) :=
      continuous_star.measurable.comp
        (hΘ₀.continuous.measurable.comp (continuous_insertCoord_fst p.2 x).measurable)
    have h2 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        A (z.1 ⟨p.1, hp⟩)) :=
      hA.comp ((continuous_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2})).comp
        continuous_fst).measurable
    have h3 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => star (B z.2)) :=
      continuous_star.measurable.comp (hB.comp continuous_snd.measurable)
    have h4 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        Θ₀ (confY13 p y z.2 z.1)) :=
      hΘ₀.continuous.measurable.comp (continuous_confY13_pair p y).measurable
    exact ((h1.mul h2).mul h3).mul h4
  -- ## integrability of the integrand at `w`
  have hFbound : ∀ z ∈ box, ‖gc13Int p hp Θ₀ A B y w z‖ ≤ MΘ * cA * cB * MY := by
    intro z hz
    have h1 : ‖gc13Int p hp Θ₀ A B y w z‖
        = ‖Θ₀ (insertCoord p.2 w z.1)‖ * ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖
          * ‖Θ₀ (confY13 p y z.2 z.1)‖ := by
      simp only [gc13Int, norm_mul, norm_star]
    rw [h1]
    refine mul_le_mul (mul_le_mul (mul_le_mul ?_ (hAb _) (norm_nonneg _) hMΘ0)
      (hBb _) (norm_nonneg _) (by positivity)) (hMY z hz) (norm_nonneg _) (by positivity)
    exact hMΘ w (Metric.mem_closedBall_self zero_le_one) z hz
  have hF_int : Integrable (gc13Int p hp Θ₀ A B y w) (volume.restrict box) := by
    refine Integrable.of_bound (hFmeas w).aestronglyMeasurable (MΘ * cA * cB * MY) ?_
    filter_upwards [self_mem_ae_restrict hboxm] with z hz
    exact hFbound z hz
  -- ## measurability of the derivative candidate
  have hF'meas : AEStronglyMeasurable (gc13Deriv p hp Θ₀ A B y w) (volume.restrict box) := by
    refine Measurable.aestronglyMeasurable ?_
    have hG : Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 w z.1)).comp (insCLM p.2))) := by
      have hL : Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
          fderiv ℝ Θ₀ (insertCoord p.2 w z.1)) :=
        (hΘ₀.continuous_fderiv (by simp)).comp (continuous_insertCoord_fst p.2 w)
      have hM : Continuous (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
          (fderiv ℝ Θ₀ (insertCoord p.2 w z.1)).comp (insCLM p.2)) :=
        ((ContinuousLinearMap.compL ℝ E3 (Xn n) ℂ).flip (insCLM p.2)).continuous.comp hL
      exact ((ContinuousLinearMap.compL ℝ E3 ℂ ℂ) conjCLM).continuous.comp hM
    have h2 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        A (z.1 ⟨p.1, hp⟩)) :=
      hA.comp ((continuous_apply (⟨p.1, hp⟩ : {k : Fin n // k ≠ p.2})).comp
        continuous_fst).measurable
    have h3 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => star (B z.2)) :=
      continuous_star.measurable.comp (hB.comp continuous_snd.measurable)
    have h4 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 =>
        Θ₀ (confY13 p y z.2 z.1)) :=
      hΘ₀.continuous.measurable.comp (continuous_confY13_pair p y).measurable
    exact h4.smul (h3.smul (h2.smul hG.measurable))
  -- ## the uniform bound on the derivative
  have hbound : ∀ᵐ z ∂(volume.restrict box), ∀ x ∈ Metric.closedBall w 1,
      ‖gc13Deriv p hp Θ₀ A B y x z‖ ≤ Mfd * cA * cB * MY := by
    filter_upwards [self_mem_ae_restrict hboxm] with z hz
    intro x hx
    have hGbound : ‖conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp
        (insCLM p.2))‖ ≤ Mfd := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have hv : (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))) v
          = star (fderiv ℝ Θ₀ (insertCoord p.2 x z.1) (insCLM p.2 v)) := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, conjCLM_apply]
      rw [hv, norm_star]
      calc ‖fderiv ℝ Θ₀ (insertCoord p.2 x z.1) (insCLM p.2 v)‖
          ≤ ‖fderiv ℝ Θ₀ (insertCoord p.2 x z.1)‖ * ‖insCLM p.2 v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ Θ₀ (insertCoord p.2 x z.1)‖ * ‖v‖ := by
            rw [insCLM_apply, Pi.norm_single]
        _ ≤ Mfd * ‖v‖ := mul_le_mul_of_nonneg_right (hMfd x hx z hz) (norm_nonneg _)
    have hd1 : ‖A (z.1 ⟨p.1, hp⟩)‖ ≤ cA := hAb _
    have hd2 : ‖star (B z.2)‖ ≤ cB := by rw [norm_star]; exact hBb _
    have hd3 : ‖Θ₀ (confY13 p y z.2 z.1)‖ ≤ MY := hMY z hz
    have hstep : ‖star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
          (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))))‖
        ≤ ‖star (B z.2)‖ * (‖A (z.1 ⟨p.1, hp⟩)‖ *
          ‖conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))‖) := by
      calc ‖star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
            (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))))‖
          ≤ ‖star (B z.2)‖ * ‖A (z.1 ⟨p.1, hp⟩) •
              (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)))‖ :=
            norm_smul_clm_le _ _
        _ ≤ ‖star (B z.2)‖ * (‖A (z.1 ⟨p.1, hp⟩)‖ *
              ‖conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))‖) :=
            mul_le_mul_of_nonneg_left (norm_smul_clm_le _ _) (norm_nonneg _)
    have hP : ‖Θ₀ (confY13 p y z.2 z.1) • (star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
            (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)))))‖
        ≤ MY * (cB * (cA * Mfd)) := by
      calc ‖Θ₀ (confY13 p y z.2 z.1) • (star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
            (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)))))‖
          ≤ ‖Θ₀ (confY13 p y z.2 z.1)‖ * ‖star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
              (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))))‖ :=
            norm_smul_clm_le _ _
        _ ≤ ‖Θ₀ (confY13 p y z.2 z.1)‖ * (‖star (B z.2)‖ * (‖A (z.1 ⟨p.1, hp⟩)‖ *
              ‖conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))‖)) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
        _ ≤ MY * (cB * (cA * Mfd)) :=
            mul_le_mul hd3 (mul_le_mul hd2 (mul_le_mul hd1 hGbound (norm_nonneg _) hcA)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcB) (by positivity) hMY0
    calc ‖gc13Deriv p hp Θ₀ A B y x z‖
        = ‖Θ₀ (confY13 p y z.2 z.1) • (star (B z.2) • (A (z.1 ⟨p.1, hp⟩) •
            (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)))))‖ :=
          rfl
      _ ≤ MY * (cB * (cA * Mfd)) := hP
      _ = Mfd * cA * cB * MY := by ring
  -- ## the derivative of the integrand, pointwise in `z`
  have hdiff : ∀ᵐ z ∂(volume.restrict box), ∀ x ∈ Metric.closedBall w 1,
      HasFDerivAt (gc13Int p hp Θ₀ A B y · z) (gc13Deriv p hp Θ₀ A B y x z) x := by
    refine Filter.Eventually.of_forall fun z x _ => ?_
    have hstar : HasFDerivAt (fun w' : E3 => star (Θ₀ (insertCoord p.2 w' z.1)))
        (conjCLM.comp ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2))) x := by
      have h1 : HasFDerivAt (fun w' : E3 => Θ₀ (insertCoord p.2 w' z.1))
          ((fderiv ℝ Θ₀ (insertCoord p.2 x z.1)).comp (insCLM p.2)) x :=
        ((hΘ₀.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
          (hasFDerivAt_insertCoord p z x)
      exact h1.star
    exact ((hstar.mul_const (A (z.1 ⟨p.1, hp⟩))).mul_const (star (B z.2))).mul_const
      (Θ₀ (confY13 p y z.2 z.1))
  -- ## parametric differentiation
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict box) (F := gc13Int p hp Θ₀ A B y)
    (F' := fun x z => gc13Deriv p hp Θ₀ A B y x z)
    (s := Metric.closedBall w 1) (x₀ := w) (bound := fun _ => Mfd * cA * cB * MY)
    (Metric.closedBall_mem_nhds w one_pos)
    (Filter.Eventually.of_forall fun x => (hFmeas x).aestronglyMeasurable)
    hF_int hF'meas hbound (integrable_const _) hdiff
  exact key.differentiableAt

end Work.BoseBoxFock
