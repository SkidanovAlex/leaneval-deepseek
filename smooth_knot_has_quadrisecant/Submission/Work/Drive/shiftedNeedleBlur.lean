import Mathlib
import Submission.Work.Drive.shiftedNeedleDefs
import Submission.Work.Drive.avgChordIdentity
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.shiftedNeedleWindow

/-!
# The double blur of the shifted needle, and the chart inequality

`Work.Drive.needleFam r D lam δ₁ δ₂ ε` is the double convolution of the chamfered loop: the loop
parameter is blurred at scale `δ₁` (`sweepSmoothT`) and the sweep parameter at scale `δ₂`.  This
module

* swaps the two convolutions (`Work.Drive.needleFam_eq_blur_loop`), so that the needle is the `δ₁`
  average of the `σ`-blurred loop point `Work.Drive.loopBlur`;
* converts the *pointwise* chart bound of `loopBlur` (`Drive/loopBlur_chart`) into the bound on the
  needle itself (`Work.Drive.needleFam_chart`):

    `|⟪needleFam τ - chordEndA, v⟫ - ℓ * ∫ u, bump u * needleFrac lam (τ - δ₁ u)| ≤ ℓ/8`.

The swap is the step that makes the estimate possible at all: the frame of the `σ`-blurred loop
(whose chord is `chordEndA`, `chordEndB`) is *the* frame of the needle, so the mismatch between the
loop's own chord frame at `σ` and the needle's frame integrates to zero, and only the quadratic
deviation survives (`arcPointDeviationBound`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **Fubini for interval integrals of `Space`-valued functions.** -/
lemma intervalIntegral_swap_vec (f : ℝ → ℝ → Space) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d)))) :
    (∫ s in a..b, ∫ t in c..d, f s t) = ∫ t in c..d, ∫ s in a..b, f s t := by
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.integral_integral_swap hf

/-- **The needle is the `δ₁`-average of the `σ`-blurred loop point.** -/
theorem needleFam_eq_blur_loop {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (lam δ₁ δ₂ ε τ : ℝ) :
    needleFam r D lam δ₁ δ₂ ε τ
      = ∫ u in (-1 : ℝ)..1, sweepBump u • loopBlur r D lam δ₂ ε (τ - δ₁ * u) := by
  obtain ⟨C, hC0, hC⟩ := exists_sweepLoopChamfer_bound hr D lam
  have hmeas : Measurable (fun p : ℝ × ℝ => sweepBump p.1 • (sweepBump p.2 •
      sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2))) := by
    have hloop : Measurable (fun p : ℝ × ℝ =>
        sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2)) :=
      (sweepLoopChamfer_measurable D hr lam).comp
        (show Measurable (fun p : ℝ × ℝ => (ε - δ₂ * p.1, τ - δ₁ * p.2)) from
          (by fun_prop : Continuous fun p : ℝ × ℝ => (ε - δ₂ * p.1, τ - δ₁ * p.2)).measurable)
    exact (continuous_sweepBump.measurable.comp measurable_fst).smul
      ((continuous_sweepBump.measurable.comp measurable_snd).smul hloop)
  have hbnd : ∀ p : ℝ × ℝ, ‖sweepBump p.1 • (sweepBump p.2 •
      sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2))‖ ≤ C := by
    intro p
    have h1 : ‖sweepBump p.1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg p.1)]; exact sweepBump_le_one p.1
    have h2 : ‖sweepBump p.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg p.2)]; exact sweepBump_le_one p.2
    have h3 : ‖sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2)‖ ≤ C := hC _ _
    rw [norm_smul, norm_smul]
    calc ‖sweepBump p.1‖ * (‖sweepBump p.2‖ *
          ‖sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2)‖)
        ≤ 1 * (1 * C) := by
          refine mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
      _ = C := by ring
  have hInt : Integrable (Function.uncurry (fun v u : ℝ => sweepBump v • (sweepBump u •
      sweepLoopChamfer r D lam (ε - δ₂ * v) (τ - δ₁ * u))))
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).prod (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    show Integrable (fun p : ℝ × ℝ => sweepBump p.1 • (sweepBump p.2 •
      sweepLoopChamfer r D lam (ε - δ₂ * p.1) (τ - δ₁ * p.2))) _
    exact Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall hbnd)
  have hswap := intervalIntegral_swap_vec (fun v u : ℝ => sweepBump v • (sweepBump u •
      sweepLoopChamfer r D lam (ε - δ₂ * v) (τ - δ₁ * u))) (by norm_num : (-1 : ℝ) ≤ 1)
    (by norm_num) hInt
  simp only [needleFam, sweepFam, sweepSmoothT, loopBlur]
  simp_rw [← intervalIntegral.integral_smul]
  rw [hswap]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  refine intervalIntegral.integral_congr (fun v _ => ?_)
  exact smul_comm (sweepBump v) (sweepBump u)
    (sweepLoopChamfer r D lam (ε - δ₂ * v) (τ - δ₁ * u))

/-! ## The chart inequality for the needle -/

/-- **The `σ`-blurred loop point is measurable in the loop parameter.** -/
lemma aestronglyMeasurable_loopBlur_comp {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (lam δ₂ ε δ₁ τ : ℝ) :
    AEStronglyMeasurable (fun u : ℝ => loopBlur r D lam δ₂ ε (τ - δ₁ * u)) volume := by
  have hmeas : Measurable (fun p : ℝ × ℝ => sweepBump p.2 •
      sweepLoopChamfer r D lam (ε - δ₂ * p.2) (τ - δ₁ * p.1)) :=
    ((Continuous.measurable sweepBump_continuous).comp measurable_snd).smul
      ((sweepLoopChamfer_measurable D hr lam).comp
        (show Measurable (fun p : ℝ × ℝ => (ε - δ₂ * p.2, τ - δ₁ * p.1)) from
          (by fun_prop : Continuous fun p : ℝ × ℝ => (ε - δ₂ * p.2, τ - δ₁ * p.1)).measurable))
  have h := hmeas.aestronglyMeasurable.integral_prod_right'
    (μ := volume) (ν := volume.restrict (Set.Ioc (-1 : ℝ) 1))
  simpa only [loopBlur, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h

/-- **A uniform bound for the `σ`-blurred loop point.** -/
lemma loopBlurNormBound {r : ℝ → Space} (hr : Continuous r) {d : BandArcData} (D : SweepData d)
    (lam δ₂ ε : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ' : ℝ, ‖loopBlur r D lam δ₂ ε τ'‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_sweepLoopChamfer_bound hr D lam
  refine ⟨C, hC0, fun τ' => ?_⟩
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ')
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine ((Continuous.measurable sweepBump_continuous).smul
      ((sweepLoopChamfer_measurable D hr lam).comp
        (show Measurable (fun v : ℝ => (ε - δ₂ * v, τ')) from
          (by fun_prop : Continuous fun v : ℝ => (ε - δ₂ * v, τ')).measurable))).aestronglyMeasurable.restrict
  have hbnd : ∀ᵐ v ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)),
      ‖sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖ ≤ C * sweepBump v := by
    filter_upwards with v
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    calc sweepBump v * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖ ≤ sweepBump v * C :=
          mul_le_mul_of_nonneg_left (hC _ _) (sweepBump_nonneg v)
      _ = C * sweepBump v := by ring
  have hint : IntervalIntegrable
      (fun v : ℝ => sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ') volume (-1) 1 :=
    IntervalIntegrable.mono_fun' ((sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1)
      hmeas hbnd
  rw [loopBlur]
  calc ‖∫ v in (-1 : ℝ)..1, sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖
      ≤ ∫ v in (-1 : ℝ)..1, ‖sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ v in (-1 : ℝ)..1, sweepBump v * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖ := by
        refine intervalIntegral.integral_congr (fun v _ => ?_)
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    _ ≤ ∫ v in (-1 : ℝ)..1, C * sweepBump v := by
        have hnorm : IntervalIntegrable
            (fun v : ℝ => sweepBump v * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖) volume (-1) 1 :=
          (hint.norm).congr_ae (Filter.Eventually.of_forall (fun v => by
            show ‖sweepBump v • sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖
              = sweepBump v * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖
            rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]))
        refine intervalIntegral.integral_mono_on (by norm_num) hnorm
          ((sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1) (fun v _ => ?_)
        calc sweepBump v * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) τ'‖ ≤ sweepBump v * C :=
              mul_le_mul_of_nonneg_left (hC _ _) (sweepBump_nonneg v)
          _ = C * sweepBump v := by ring
    _ = C := by rw [intervalIntegral.integral_const_mul, integral_sweepBump, mul_one]

/-- **The chart inequality for the `δ₁`-average of the `σ`-blurred loop point.** -/
theorem needleFam_chart_self {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε : ℝ} {v A : Space} {ℓ : ℝ} (hv : ‖v‖ = 1) (hℓ : 0 ≤ ℓ)
    (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hblur : ∀ τ' : ℝ,
      |inner ℝ (loopBlur r D lam δ₂ ε τ' - A) v - ℓ * needleFrac lam τ'| ≤ (1 / 8) * ℓ) :
    ∀ τ : ℝ,
      |inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - A) v
        - ℓ * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))| ≤ (1 / 8) * ℓ := by
  intro τ
  obtain ⟨C, hC0, hCb⟩ := loopBlurNormBound hr D lam δ₂ ε
  have hAESM : AEStronglyMeasurable (fun u : ℝ => loopBlur r D lam δ₂ ε (τ - δ₁ * u)) volume :=
    aestronglyMeasurable_loopBlur_comp hr D lam δ₂ ε δ₁ τ
  -- integrability of the blurred loop and of its inner product with `v`
  have hLI : IntervalIntegrable
      (fun u : ℝ => sweepBump u • loopBlur r D lam δ₂ ε (τ - δ₁ * u)) volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun' ((sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1)
      ?_ ?_
    · exact (((Continuous.measurable sweepBump_continuous).aestronglyMeasurable.smul hAESM).restrict)
    · filter_upwards with u
      rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
      calc sweepBump u * ‖loopBlur r D lam δ₂ ε (τ - δ₁ * u)‖ ≤ sweepBump u * C :=
            mul_le_mul_of_nonneg_left (hCb _) (sweepBump_nonneg u)
        _ = C * sweepBump u := by ring
  have hLIin : IntervalIntegrable
      (fun u : ℝ => sweepBump u * inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u)) v) volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun' ((sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1)
      ?_ ?_
    · exact (((Continuous.measurable sweepBump_continuous).aestronglyMeasurable.mul
        (hAESM.inner aestronglyMeasurable_const)).restrict)
    · filter_upwards with u
      rw [norm_mul, Real.norm_of_nonneg (sweepBump_nonneg u), Real.norm_eq_abs]
      calc sweepBump u * |inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u)) v|
          ≤ sweepBump u * (‖loopBlur r D lam δ₂ ε (τ - δ₁ * u)‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (sweepBump_nonneg u)
        _ = sweepBump u * ‖loopBlur r D lam δ₂ ε (τ - δ₁ * u)‖ := by rw [hv, mul_one]
        _ ≤ sweepBump u * C := mul_le_mul_of_nonneg_left (hCb _) (sweepBump_nonneg u)
        _ = C * sweepBump u := by ring
  have hintA0 : IntervalIntegrable (fun u : ℝ => sweepBump u * inner ℝ A v) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  -- the inner product of the needle
  have hstep : inner ℝ (needleFam r D lam δ₁ δ₂ ε τ) v
      = ∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u)) v := by
    rw [needleFam_eq_blur_loop hr D lam δ₁ δ₂ ε τ, inner_intervalIntegral_comm_left hLI v]
    exact intervalIntegral.integral_congr (fun u _ => by rw [real_inner_smul_left])
  -- the two pieces of the target integrand
  have hintA : IntervalIntegrable
      (fun u : ℝ => sweepBump u * inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v)
      volume (-1) 1 := by
    have h1 := hLIin.sub hintA0
    refine h1.congr_ae ?_
    filter_upwards with u
    rw [inner_sub_left]
    ring
  have hintB : IntervalIntegrable
      (fun u : ℝ => sweepBump u * (ℓ * needleFrac lam (τ - δ₁ * u))) volume (-1) 1 := by
    refine ((intervalIntegrable_bump_mul_needleFrac (δ := δ₁) (τ := τ) h0 h1).const_mul ℓ).congr_ae ?_
    filter_upwards with u
    ring

  have htarget : inner ℝ (needleFam r D lam δ₁ δ₂ ε τ - A) v
      - ℓ * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))
      = ∫ u in (-1 : ℝ)..1, sweepBump u * (inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v
          - ℓ * needleFrac lam (τ - δ₁ * u)) := by
    rw [inner_sub_left, hstep]
    rw [show inner ℝ A v = ∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ A v from by
      rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]]
    rw [show ℓ * (∫ u in (-1 : ℝ)..1, sweepBump u * needleFrac lam (τ - δ₁ * u))
        = ∫ u in (-1 : ℝ)..1, sweepBump u * (ℓ * needleFrac lam (τ - δ₁ * u)) from by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun u _ => by ring)]
    rw [← intervalIntegral.integral_sub hLIin hintA0]
    rw [← intervalIntegral.integral_sub (hLIin.sub hintA0) hintB]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [inner_sub_left]
    ring
  rw [htarget]
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u * (inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v
        - ℓ * needleFrac lam (τ - δ₁ * u))‖ ≤ sweepBump u * ((1 / 8) * ℓ) := by
    intro u _
    rw [norm_mul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg u)
    rw [Real.norm_eq_abs]
    exact hblur (τ - δ₁ * u)
  have hintC : IntervalIntegrable
      (fun u : ℝ => sweepBump u * (inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v
        - ℓ * needleFrac lam (τ - δ₁ * u))) volume (-1) 1 :=
    (hintA.sub hintB).congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [← Real.norm_eq_abs]
  calc ‖∫ u in (-1 : ℝ)..1, sweepBump u * (inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v
        - ℓ * needleFrac lam (τ - δ₁ * u))‖
      ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u * (inner ℝ (loopBlur r D lam δ₂ ε (τ - δ₁ * u) - A) v
          - ℓ * needleFrac lam (τ - δ₁ * u))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ((1 / 8) * ℓ) :=
        intervalIntegral.integral_mono_on (by norm_num) hintC.norm
          ((sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1) hpt
    _ = (1 / 8) * ℓ := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

end Work.Drive
