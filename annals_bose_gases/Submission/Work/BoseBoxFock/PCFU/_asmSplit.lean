import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.integrableOn_abox_W1_shift
import Submission.Work.BoseBoxFock.PCFU.taper_pairing_aux
import Submission.Work.BoseBoxFock.boxAvgAux
import Submission.Work.BoseBoxFock.qVecFrameWeighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **Shifted-`W₁` slot integrability.** -/
theorem integrable_slot_shift {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {i j : Fin n} (hij : i ≠ j) (c : E3)
    {Θ Γ : Submission.BoseGases.X n → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hΓm : Measurable Γ) (hΓb : ∀ x, |Γ x| ≤ D) :
    Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ) * (Γ x : ℂ)) := by
  have hW1 : Integrable (fun z : E3 => Work.BoseFixR.W1fun v h ℓ z) := by
    have h1 := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ)
      hR hv_supp h hℓ hRℓ
    simpa [Work.BoseFixR.W1fun] using h1
  have hpair : Integrable (fun p : E3 × E3 => Work.BoseFixR.W1fun v h ℓ (p.2 - p.1 + c))
      (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    integrable_prod_restrict_shift (Submission.BoseGases.acube_measurable ℓ)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le) c hW1
  have hOn : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseFixR.W1fun v h ℓ (x j - x i + c)) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_pair_pullback_abox hℓ hij hpair
  have hχ0 : (0 : ℝ) ≤ Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos.le
  set M : ℝ := C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * D with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ) * (Γ x : ℂ))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h1 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Complex.measurable_ofReal.comp hΘm).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Complex.measurable_ofReal.comp
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable.comp
          (measurable_pi_apply i))).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Complex.measurable_ofReal.comp
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable.comp
          (measurable_pi_apply j))).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Complex.measurable_ofReal.comp_aemeasurable hOn.aemeasurable).aestronglyMeasurable
    have h5 : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => ((Γ x : ℝ) : ℂ))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Complex.measurable_ofReal.comp hΓm).aestronglyMeasurable
    exact (((h1.mul h2).mul h3).mul h4).mul h5
  have hbound : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖(Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ) * (Γ x : ℂ)‖
      ≤ M * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)| := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x _
    have hχi : |Submission.BoseGases.chiScale ℓ (x i)| ≤ Submission.BoseGases.chiSup :=
      Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x i)
    have hχj : |Submission.BoseGases.chiScale ℓ (x j)| ≤ Submission.BoseGases.chiSup :=
      Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x j)
    have hnorm : ‖(Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ) * (Γ x : ℂ)‖
        = |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
          * |Submission.BoseGases.chiScale ℓ (x j)|
          * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)| * |Γ x| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hM]
    have h1 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        ≤ C * Submission.BoseGases.chiSup :=
      mul_le_mul (hΘb x) hχi (abs_nonneg _) hC
    have h2 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        * |Submission.BoseGases.chiScale ℓ (x j)|
        ≤ C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup :=
      mul_le_mul h1 hχj (abs_nonneg _) (mul_nonneg hC hχ0)
    have h3 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        * |Submission.BoseGases.chiScale ℓ (x j)| * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)|
        ≤ C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup
          * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)| :=
      mul_le_mul h2 le_rfl (abs_nonneg _) (by positivity)
    calc |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
          * |Submission.BoseGases.chiScale ℓ (x j)|
          * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)| * |Γ x|
        ≤ (C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup
            * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)|) * D :=
          mul_le_mul h3 (hΓb x) (abs_nonneg _) (by positivity)
      _ = C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * D
            * |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)| := by ring
  have hIntOn : Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + c) : ℝ) : ℂ) * (Γ x : ℂ))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    MeasureTheory.Integrable.mono' (hOn.abs.const_mul M) hmeas hbound
  refine ((integrable_indicator_iff (Submission.BoseGases.abox_measurable n ℓ)).mpr
    hIntOn).congr (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    have h0 : Θ x = 0 := by
      by_contra hc
      exact hx (hΘs (Function.mem_support.mpr hc))
    simp only [h0, Complex.ofReal_zero, zero_mul, mul_zero]

/-- **Bounded-kernel slot integrability.** -/
theorem integrable_slot_bdd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    {K : E3 → ℂ} (hK : Continuous K) {MK : ℝ} (hKb : ∀ z, ‖K z‖ ≤ MK)
    {Θ Γ : Submission.BoseGases.X n → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hΓm : Measurable Γ) (hΓb : ∀ x, |Γ x| ≤ D) :
    Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * K (x j - x i) * (Γ x : ℂ)) := by
  have hχ0 : (0 : ℝ) ≤ Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos.le
  have hMK : (0 : ℝ) ≤ max MK 0 := le_max_right _ _
  set M : ℝ := C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * D * max MK 0 with hM
  have hmaj : Integrable (fun _ : Submission.BoseGases.X n => M)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    MeasureTheory.integrableOn_const (C := M)
      (lt_top_iff_ne_top.mp (Submission.BoseGases.abox_lt_top n ℓ hℓ.le))
  have hmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * K (x j - x i) * (Γ x : ℂ))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h1 : Measurable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp hΘm
    have h2 : Measurable (fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.chiScale ℓ (x i) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable.comp
          (measurable_pi_apply i))
    have h3 : Measurable (fun x : Submission.BoseGases.X n =>
        ((Submission.BoseGases.chiScale ℓ (x j) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable.comp
          (measurable_pi_apply j))
    have h4 : Measurable (fun x : Submission.BoseGases.X n => K (x j - x i)) :=
      hK.measurable.comp (by fun_prop : Measurable (fun x : Submission.BoseGases.X n => x j - x i))
    have h5 : Measurable (fun x : Submission.BoseGases.X n => ((Γ x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp hΓm
    exact ((((h1.mul h2).mul h3).mul h4).mul h5).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖(Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * K (x j - x i) * (Γ x : ℂ)‖ ≤ M := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x _
    have hχi : |Submission.BoseGases.chiScale ℓ (x i)| ≤ Submission.BoseGases.chiSup :=
      Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x i)
    have hχj : |Submission.BoseGases.chiScale ℓ (x j)| ≤ Submission.BoseGases.chiSup :=
      Submission.BoseGases.abs_chiScale_le_chiSup ℓ (x j)
    have hKx : ‖K (x j - x i)‖ ≤ max MK 0 := le_trans (hKb _) (le_max_left _ _)
    have hnorm : ‖(Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * K (x j - x i) * (Γ x : ℂ)‖
        = |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
          * |Submission.BoseGases.chiScale ℓ (x j)| * ‖K (x j - x i)‖ * |Γ x| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hM]
    have h1 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        ≤ C * Submission.BoseGases.chiSup :=
      mul_le_mul (hΘb x) hχi (abs_nonneg _) hC
    have h2 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        * |Submission.BoseGases.chiScale ℓ (x j)|
        ≤ C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup :=
      mul_le_mul h1 hχj (abs_nonneg _) (mul_nonneg hC hχ0)
    have h3 : |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
        * |Submission.BoseGases.chiScale ℓ (x j)| * ‖K (x j - x i)‖
        ≤ C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * max MK 0 :=
      mul_le_mul h2 hKx (norm_nonneg _) (by positivity)
    calc |Θ x| * |Submission.BoseGases.chiScale ℓ (x i)|
          * |Submission.BoseGases.chiScale ℓ (x j)| * ‖K (x j - x i)‖ * |Γ x|
        ≤ (C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * max MK 0) * D :=
          mul_le_mul h3 (hΓb x) (abs_nonneg _) (by positivity)
      _ = C * Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * D * max MK 0 := by ring
  have hIntOn : Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * K (x j - x i) * (Γ x : ℂ))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    MeasureTheory.Integrable.mono' hmaj hmeas hbound
  refine ((integrable_indicator_iff (Submission.BoseGases.abox_measurable n ℓ)).mpr
    hIntOn).congr (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    have h0 : Θ x = 0 := by
      by_contra hc
      exact hx (hΘs (Function.mem_support.mpr hc))
    simp only [h0, Complex.ofReal_zero, zero_mul, mul_zero]

/-! ## The finite expansion of the periodisation on the box -/

/-- `latPer3` is the finite lattice sum on the box. -/
lemma latPer3_pair_eq_sum {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hW : ∀ z : E3, R < ‖z‖ → W z = 0) {n : ℕ} {i j : Fin n}
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    latPer3 ℓ W (x j - x i)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
          ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
  refine Work.BoseBoxFock.latPer3_eq_sum_latFinSet hℓ hW ?_
  rw [norm_sub_rev]
  exact Work.BoseBoxFock.norm_sub_le_of_mem_acube hℓ.le
    ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx i)
    ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j)

/-- The pointwise identity behind the integrability of the images half: the `χχ`-weighted
periodisation is the finite sum of the shifted `W₁`-terms (everywhere, since `Θ` vanishes off the
box). -/
lemma latPer3_slot_sum {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hW : ∀ z : E3, R < ‖z‖ → W z = 0) {n : ℕ} {i j : Fin n} {Θ Γ : Submission.BoseGases.X n → ℝ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) (x : Submission.BoseGases.X n) :
    (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
        (((ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
          * ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * (Γ x : ℂ))))
      = (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
          * latPer3 ℓ W (x j - x i) * (Γ x : ℂ) := by
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [latPer3_pair_eq_sum hℓ hW hx,
      show (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
          ((ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
            * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
            * ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * (Γ x : ℂ)))
        = ((ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
            * (Submission.BoseGases.chiScale ℓ (x j) : ℂ) * (Γ x : ℂ))
          * (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
              ((W (x j - x i + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)]
    ring
  · have h0 : Θ x = 0 := by
      by_contra hc
      exact hx (hΘs (Function.mem_support.mpr hc))
    simp only [h0, Complex.ofReal_zero, zero_mul, mul_zero, Finset.sum_const_zero]

/-- **Periodisation slot integrability.** -/
theorem integrable_slot_latPer3 {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {i j : Fin n} (hij : i ≠ j)
    {Θ Γ : Submission.BoseGases.X n → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hΓm : Measurable Γ) (hΓb : ∀ x, |Γ x| ≤ D) :
    Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
        * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
        * latPer3 ℓ (Work.BoseFixR.W1fun v h ℓ) (x j - x i) * (Γ x : ℂ)) := by
  have hW : ∀ z : E3, R < ‖z‖ → Work.BoseFixR.W1fun v h ℓ z = 0 := fun z hz =>
    W1fun_eq_zero_of_le_norm' hv_supp hz.le
  have hsum : Integrable (fun x : Submission.BoseGases.X n =>
      ∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
        (((ℓ ^ 3 : ℝ) : ℂ) * ((Θ x : ℂ) * (Submission.BoseGases.chiScale ℓ (x i) : ℂ)
          * (Submission.BoseGases.chiScale ℓ (x j) : ℂ)
          * ((Work.BoseFixR.W1fun v h ℓ (x j - x i + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
          * (Γ x : ℂ)))) := by
    refine integrable_finsetSum _ (fun m _ => ?_)
    exact (integrable_slot_shift v h hR hℓ hv_supp hRℓ hij (ℓ • Work.BoseBoxFock.latVec m)
      hC hD hΘm hΘb hΘs hΓm hΓb).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall
    (fun x => latPer3_slot_sum (i := i) (j := j) (Θ := Θ) (Γ := Γ) hℓ hW hΘs x))

/-- **The `chAslot` split.**  The `(A)`-slot kernel `KfrU − ℓ³W₁` splits into the *taper*
`KfrU − latPer3 ℓ W₁` and the *images* `latPer3 ℓ W₁ − ℓ³W₁`. -/
theorem chAslotSplitMine {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) {R μ : ℝ} (hR : 0 < R) (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (N : ℕ) {i j : Fin n} (hij : i ≠ j)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    Work.BoseBoxFock.PCFU.chAslot v h fc fu μ N i j Θ
      = (∫ x : Submission.BoseGases.X n,
          (Θ x : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
            * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i))
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
          (Θ x : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
            * (Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i)
                - ((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
                    * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
            * ((Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                    (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ)) := by
  classical
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ := by
    rw [Work.BoseBoxFock.PCFU.chKappa]
    refine inv_pos.mpr (mul_pos (pow_pos ?_ 2) (Work.BoseBox.sideAt_pos hμ hav))
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  obtain ⟨C, hC⟩ := hΘb
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (0 : Submission.BoseGases.X n))
  obtain ⟨hΓm, D, hD0, hΓb⟩ := Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_measurable_bounded
    (fc := fc) (μ := μ) (ℓ := Work.BoseBoxFock.ellH v μ)
    (κ := Work.BoseBoxFock.PCFU.chKappa v μ)
    (Cθ := C) (i := i) (j := j) hℓ hκ hC0 hΘm hC
  let L : Submission.BoseGases.X n → ℝ := fun x =>
    Work.BoseBoxFix.lowSlot fc (Work.BoseBoxFock.PCFU.chKappa v μ)
      (Work.BoseBoxFock.ellH v μ) j
      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x
  have hLm : Measurable L := hΓm
  have hLb : ∀ x, |L x| ≤ D := hΓb
  have hshiftW : Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℂ)
        * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℂ)
        * (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
            * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
        * (L x : ℂ)) := by
    refine ((integrable_slot_shift v h hR hℓ hv_supp hRℓ hij (0 : E3) hC0 hD0 hΘm hC hΘs
      hLm hLb).const_mul (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)).congr ?_
    filter_upwards with x
    rw [Complex.ofReal_pow]
    ac_rfl
  have hbdd : Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℂ)
        * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℂ)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i) * (L x : ℂ)) :=
    integrable_slot_bdd hℓ (i := i) (j := j)
      (K := Work.BoseBoxFock.PCFU.KfrU v h μ fu N)
      (Work.BoseBoxFock.PCFU.continuous_KfrU v h μ fu N)
      (MK := ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
      (Work.BoseBoxFock.PCFU.norm_KfrU_le v h μ fu N) hC0 hD0 hΘm hC hΘs hLm hLb
  have hlat : Integrable (fun x : Submission.BoseGases.X n =>
      (Θ x : ℂ) * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℂ)
        * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℂ)
        * Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i) * (L x : ℂ)) :=
    integrable_slot_latPer3 v h hR hℓ hv_supp hRℓ hij hC0 hD0 hΘm hC hΘs hLm hLb
  let Tfun : Submission.BoseGases.X n → ℂ := fun x =>
    (Θ x : ℂ) * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℂ)
      * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℂ)
      * (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
          - Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i))
      * (L x : ℂ)
  let Ifun : Submission.BoseGases.X n → ℂ := fun x =>
    (Θ x : ℂ) * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x i) : ℂ)
      * (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) (x j) : ℂ)
      * (Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (x j - x i)
          - ((Work.BoseBoxFock.ellH v μ) ^ 3 : ℂ)
              * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (x j - x i) : ℝ) : ℂ))
      * (L x : ℂ)
  have hTint : Integrable Tfun := by
    refine (hbdd.sub hlat).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply, Tfun, chiLam_eq_chiScale, Complex.ofReal_pow]
    ring
  have hIint : Integrable Ifun := by
    refine (hlat.sub hshiftW).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply, Ifun, chiLam_eq_chiScale, Complex.ofReal_pow]
    ring
  have hpoint : Work.BoseBoxFock.PCFU.chAslot v h fc fu μ N i j Θ
      = ∫ x : Submission.BoseGases.X n, (Tfun x + Ifun x) := by
    simp only [Work.BoseBoxFock.PCFU.chAslot, chiLam_eq_chiScale]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    rw [show ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
        = ((Work.BoseBoxFock.ellH v μ ^ 3 : ℝ) : ℂ) from (Complex.ofReal_pow _ 3).symm]
    simp only [Tfun, Ifun, chiLam_eq_chiScale, Complex.ofReal_pow]
    ring
  rw [hpoint, integral_add hTint hIint]

end Work.BoseBoxFock.PCFU
