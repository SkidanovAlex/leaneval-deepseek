import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

/-- The angular weight `sin(2θ)^{-η}`. -/
private def sw (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

private lemma sin_two_nonneg_Iθ_block {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- A function continuous on the open strip `(δ,R) × (0,π/2)` is almost everywhere strongly
measurable for the product of Lebesgue measure restricted to `[δ,R]` and to `Iθ`. -/
private theorem aesm_of_continuousOn_stripR {δ R : ℝ} (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioo δ R ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable g
      ((volume.restrict (Set.Icc δ R)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hz : Set.Icc δ R =ᵐ[volume] Set.Ioo δ R :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := δ) (b := R)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Set.Icc δ R ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hUm : MeasurableSet (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

theorem interp_swap_clean {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry F) (Set.Icc δ R ×ˢ Work.Spaces.Iθ))
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc δ R → ∀ θ : ℝ, F z θ = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  change (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, F z θ * sw θ))
      = ∫ θ in Spaces.Iθ, (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * F z θ) * sw θ
  have hδle : δ ≤ R := hδR.le
  have hη0 : 0 < Spaces.eta := by norm_num [Spaces.eta]
  have hη1 : Spaces.eta < 1 := by norm_num [Spaces.eta]
  have hbox : MeasurableSet (Set.Icc δ R ×ˢ Spaces.Iθ) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hμbox : (volume.restrict (Set.Icc δ R)).prod (volume.restrict Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Icc δ R ×ˢ Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
  -- ## Step 1: integrability of the double integrand
  have hInt : Integrable (fun p : ℝ × ℝ => (Spaces.w p.1) ^ 2 * (F p.1 p.2 * sw p.2))
      ((volume.restrict (Set.Icc δ R)).prod (volume.restrict Spaces.Iθ)) := by
    -- bounds on the compact box
    obtain ⟨K2, hK2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (f := Function.uncurry F) hcont
    have hwcont : ContinuousOn (fun z : ℝ => (Spaces.w z) ^ 2) (Set.Icc δ R) := by
      simp only [Spaces.w]
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.div ((continuousOn_const.add continuous_id.continuousOn).pow 2)
        (continuous_id.continuousOn.pow 2) (fun z hz => ?_)
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hδ hz.1))
    obtain ⟨K1, hK1⟩ := isCompact_Icc.exists_bound_of_continuousOn hwcont
    -- the dominating function is integrable
    have hzfull : Integrable (Set.indicator (Set.Icc δ R) (fun _ : ℝ => K1 * K2))
        (volume : Measure ℝ) :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (s := Set.Icc δ R) (C := K1 * K2)
          (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hzind : Integrable (Set.indicator (Set.Icc δ R) (fun _ : ℝ => K1 * K2))
        (volume.restrict (Set.Icc δ R)) := hzfull.restrict
    have hθmaj : Integrable
        (fun θ : ℝ => (Real.pi / 4) ^ Spaces.eta
          * (θ ^ (-(Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Spaces.eta))))
        (volume.restrict Spaces.Iθ) :=
      Spaces.integrableOn_majorant_rpow Spaces.eta hη0 hη1
    have hdom : Integrable (fun p : ℝ × ℝ =>
        Set.indicator (Set.Icc δ R) (fun _ : ℝ => K1 * K2) p.1
          * ((Real.pi / 4) ^ Spaces.eta
              * (p.2 ^ (-(Spaces.eta)) + (Real.pi / 2 - p.2) ^ (-(Spaces.eta)))))
        ((volume.restrict (Set.Icc δ R)).prod (volume.restrict Spaces.Iθ)) :=
      hzind.mul_prod hθmaj
    -- almost everywhere strong measurability
    have hwstrip : ContinuousOn (fun p : ℝ × ℝ => (Spaces.w p.1) ^ 2)
        (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
      simp only [Spaces.w]
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt (lt_trans hδ hp.1.1))
    have hFstrip : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      hcont.mono (fun p hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩)
    have hswstrip : ContinuousOn (fun p : ℝ × ℝ => ((Real.sin (2 * p.2)) ^ Spaces.eta)⁻¹)
        (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
      refine ContinuousOn.inv₀ ?_ ?_
      · have hc : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) :=
          Real.continuous_sin.comp
            (continuous_const.mul continuous_snd : Continuous fun p : ℝ × ℝ => (2 : ℝ) * p.2)
        exact ((Real.continuous_rpow_const hη0.le).comp hc).continuousOn
      · intro p hp
        exact ne_of_gt (Real.rpow_pos_of_pos
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
            (by linarith [hp.2.2, Real.pi_pos])) _)
    have hswstrip' : ContinuousOn (fun p : ℝ × ℝ => sw p.2)
        (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
      refine hswstrip.congr ?_
      intro p hp
      simp only [sw]
      exact Real.rpow_neg (sin_two_nonneg_Iθ_block ⟨hp.2.1.le, hp.2.2.le⟩) Spaces.eta
    have hstrip : ContinuousOn (fun p : ℝ × ℝ => (Spaces.w p.1) ^ 2 * (F p.1 p.2 * sw p.2))
        (Set.Ioo δ R ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      hwstrip.mul (hFstrip.mul hswstrip')
    have hAESM : AEStronglyMeasurable (fun p : ℝ × ℝ => (Spaces.w p.1) ^ 2 * (F p.1 p.2 * sw p.2))
        ((volume.restrict (Set.Icc δ R)).prod (volume.restrict Spaces.Iθ)) :=
      aesm_of_continuousOn_stripR _ hstrip
    refine Integrable.mono' hdom hAESM ?_
    rw [hμbox]
    refine MeasureTheory.ae_restrict_of_forall_mem hbox (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := hp
    have hsin0 : 0 ≤ Real.sin (2 * p.2) := sin_two_nonneg_Iθ_block hp2
    have hsw0 : 0 ≤ sw p.2 := by
      simp only [sw]
      exact Real.rpow_nonneg hsin0 _
    have hwK : ‖(Spaces.w p.1) ^ 2‖ ≤ K1 := hK1 p.1 hp1
    have hFK : ‖F p.1 p.2‖ ≤ K2 := hK2 p ⟨hp1, hp2⟩
    have hK1nn : 0 ≤ K1 := le_trans (norm_nonneg _) hwK
    have hK2nn : 0 ≤ K2 := le_trans (norm_nonneg _) hFK
    have hswmaj : sw p.2 ≤ (Real.pi / 4) ^ Spaces.eta
        * (p.2 ^ (-(Spaces.eta)) + (Real.pi / 2 - p.2) ^ (-(Spaces.eta))) := by
      simp only [sw]
      exact Spaces.sin_rpow_le_majorant Spaces.eta p.2 hη0 hp2
    have hnorm : ‖(Spaces.w p.1) ^ 2 * (F p.1 p.2 * sw p.2)‖
        = ‖(Spaces.w p.1) ^ 2‖ * ‖F p.1 p.2‖ * sw p.2 := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hsw0]
      ring
    rw [hnorm]
    calc ‖(Spaces.w p.1) ^ 2‖ * ‖F p.1 p.2‖ * sw p.2
        ≤ K1 * K2 * sw p.2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hwK hFK (norm_nonneg _) hK1nn) hsw0
      _ ≤ K1 * K2 * ((Real.pi / 4) ^ Spaces.eta
            * (p.2 ^ (-(Spaces.eta)) + (Real.pi / 2 - p.2) ^ (-(Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hswmaj (mul_nonneg hK1nn hK2nn)
      _ = Set.indicator (Set.Icc δ R) (fun _ : ℝ => K1 * K2) p.1
            * ((Real.pi / 4) ^ Spaces.eta
                * (p.2 ^ (-(Spaces.eta)) + (Real.pi / 2 - p.2) ^ (-(Spaces.eta)))) := by
          rw [Set.indicator_of_mem hp1 (fun _ : ℝ => K1 * K2)]
  -- ## Step 2: reduce the `z`-integral to the compact interval
  have step0 : (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, F z θ * sw θ))
      = ∫ z in Set.Icc δ R, ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * (F z θ * sw θ) := by
    have hmain := MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) (f := fun z => (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, F z θ * sw θ))
      (s := Set.Icc δ R) (t := Spaces.Iz) measurableSet_Ici
      (fun z hz => le_trans hδ.le hz.1) (fun z hz => by
        have hzero : (∫ θ in Spaces.Iθ, F z θ * sw θ) = 0 := by
          have : (fun θ => F z θ * sw θ) = fun _ => (0 : ℝ) := by
            funext θ
            rw [hsupp z hz.2 θ, zero_mul]
          rw [this, MeasureTheory.integral_zero]
        rw [hzero, mul_zero])
    rw [hmain]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  -- ## Step 3: Fubini
  have step1 : (∫ z in Set.Icc δ R, ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * (F z θ * sw θ))
      = ∫ θ in Spaces.Iθ, ∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * (F z θ * sw θ) :=
    MeasureTheory.integral_integral_swap hInt
  -- ## Step 4: pull the angular weight out of the inner integral
  have step2 : (∫ θ in Spaces.Iθ, ∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * (F z θ * sw θ))
      = ∫ θ in Spaces.Iθ, (∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * F z θ) * sw θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [← MeasureTheory.integral_mul_const (sw θ) (fun z => (Spaces.w z) ^ 2 * F z θ)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    ring
  -- ## Step 5: extend the inner `z`-integral back to `Iz`
  have step3 : ∀ θ : ℝ, (∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * F z θ)
      = ∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * F z θ := by
    intro θ
    exact (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) (f := fun z => (Spaces.w z) ^ 2 * F z θ)
      (s := Set.Icc δ R) (t := Spaces.Iz) measurableSet_Ici
        (fun z hz => le_trans hδ.le hz.1)
        (fun z hz => by rw [hsupp z hz.2 θ, mul_zero])).symm
  have step4 : (∫ θ in Spaces.Iθ, (∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * F z θ) * sw θ)
      = ∫ θ in Spaces.Iθ, (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * F z θ) * sw θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [step3 θ]
  calc (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, F z θ * sw θ))
      = ∫ z in Set.Icc δ R, ∫ θ in Spaces.Iθ, (Spaces.w z) ^ 2 * (F z θ * sw θ) := step0
    _ = ∫ θ in Spaces.Iθ, ∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * (F z θ * sw θ) := step1
    _ = ∫ θ in Spaces.Iθ, (∫ z in Set.Icc δ R, (Spaces.w z) ^ 2 * F z θ) * sw θ := step2
    _ = ∫ θ in Spaces.Iθ, (∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * F z θ) * sw θ := step4

end Work.Blocks
