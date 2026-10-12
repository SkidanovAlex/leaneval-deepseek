import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.abs_wSmallPair_le
import Submission.Work.BoseFixB1.integrableOn_pair_sub_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

theorem integrableOn_slot_wSmallPair {N : ℕ} {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    {M : ℕ} (hM : 1 ≤ M) (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {i j : Fin N} (hij : i ≠ j)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : MeasureTheory.AEStronglyMeasurable S (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), |S x| ≤ B) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- The numerator profile, shifted by the pair `x i - x j`, is integrable over the box.
  have hFint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => f (x i - x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_pair_sub_abox (N := N) (ℓ := ℓ) (f := f) (i := i) (j := j) hℓ hf hij
  have hFint' : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => f (x i - x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := hFint
  -- Non-negativity of the various kernel constants.
  have hc1 : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hc2 : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hc3 : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hM2 : 0 ≤ (2 / Work.SmallBoxSliding.smallConvLower M) *
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
    mul_nonneg (div_nonneg (by norm_num) hc3.le) (mul_nonneg hc1 hc2)
  -- The dominating function.
  have hdom : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        (B * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
          ((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)))) *
          |f (x i - x j)|)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    hFint'.norm.const_mul _
  -- Continuity of the cutoff and normalisation factors of the kernel.
  have hcont_chiA : Continuous (fun x : Submission.BoseGases.X N =>
      Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    have h1 : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chiScale ℓ (x i)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)
    have h2 : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x i - u)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp
        (((continuous_apply i).const_smul ((ℓ * d)⁻¹)).sub continuous_const)
    have heq : (fun x : Submission.BoseGases.X N => Submission.BoseGases.chiSmallB M ℓ d u (x i))
        = fun x => Submission.BoseGases.chiScale ℓ (x i) *
            Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x i - u) := by
      funext x; rfl
    rw [heq]; exact h1.mul h2
  have hcont_chiB : Continuous (fun x : Submission.BoseGases.X N =>
      Submission.BoseGases.chiSmallB M ℓ d u (x j)) := by
    have h1 : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chiScale ℓ (x j)) :=
      (Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)
    have h2 : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x j - u)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp
        (((continuous_apply j).const_smul ((ℓ * d)⁻¹)).sub continuous_const)
    have heq : (fun x : Submission.BoseGases.X N => Submission.BoseGases.chiSmallB M ℓ d u (x j))
        = fun x => Submission.BoseGases.chiScale ℓ (x j) *
            Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x j - u) := by
      funext x; rfl
    rw [heq]; exact h1.mul h2
  have hcont_css : Continuous (fun x : Submission.BoseGases.X N =>
      Submission.BoseGases.convScaleSmall M (ℓ * d) (x i - x j)) := by
    have hcont : Continuous (fun x : Submission.BoseGases.X N => (ℓ * d)⁻¹ • (x i - x j)) :=
      (((continuous_apply i).sub (continuous_apply j)).const_smul ((ℓ * d)⁻¹))
    have h3 : Continuous (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (x i - x j))) :=
      (Submission.BoseGases.conv3Small_continuous hM).comp hcont
    simpa [Submission.BoseGases.convScaleSmall] using h3
  have hcont_cs : Continuous (fun x : Submission.BoseGases.X N =>
      Submission.BoseGases.convScale ℓ (x i - x j)) :=
    (Submission.BoseGases.convScale_continuous ℓ).comp
      ((continuous_apply i).sub (continuous_apply j))
  -- A.e. strong measurability of the kernel slot, assembled from the pieces above.
  have hker : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    have hmid : AEMeasurable (fun x : Submission.BoseGases.X N =>
        f (x i - x j) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x i - x j)
          / Submission.BoseGases.convScale ℓ (x i - x j))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hFint'.aemeasurable.div hcont_css.aemeasurable).div hcont_cs.aemeasurable
    have hmain : AEMeasurable (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.chiSmallB M ℓ d u (x i) *
          (f (x i - x j) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x i - x j)
            / Submission.BoseGases.convScale ℓ (x i - x j)) *
          Submission.BoseGases.chiSmallB M ℓ d u (x j))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      ((hcont_chiA.aemeasurable.mul hmid).mul hcont_chiB.aemeasurable)
    refine (hmain.congr ?_).aestronglyMeasurable
    filter_upwards with x
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  have hints : MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
      S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := hSm.mul hker
  refine MeasureTheory.Integrable.mono' hdom hints ?_
  filter_upwards [hSb] with x hSx
  rw [Real.norm_eq_abs, abs_mul]
  -- Pointwise domination of the kernel.
  have hab := abs_wSmallPair_le (M := M) hM hℓ hd hfsupp hR hRχ u (x i) (x j)
  have hchi : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x i - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x i - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  have hstep : |Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j)| ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * |f (x i - x j)|) := by
    refine le_trans hab ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hchi hc1)
      (mul_nonneg hM2 (abs_nonneg _))
  have hfinal : |S x| * |Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j)| ≤
      B * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * |f (x i - x j)|)) :=
    mul_le_mul hSx hstep (abs_nonneg _) hB
  calc |S x| * |Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j)|
      ≤ B * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * |f (x i - x j)|)) := hfinal
    _ = (B * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
          ((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)))) *
          |f (x i - x j)| := by ring

end Work.BoseFixB1
