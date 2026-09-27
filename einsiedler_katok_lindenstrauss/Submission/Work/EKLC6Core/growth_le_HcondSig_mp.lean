import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.coboundary_integral
import Submission.Work.EKLC6Core.aemeasurable_atomInfo
import Submission.Work.EKLC6Core.lintegral_atomInfo_le_nocov
import Submission.Work.EKLC6Core.growth_le_atomInfo_mp

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open Work.EKLContract

/-! ## The one-step covariance from the single-parameter hypothesis -/

theorem preimage_conj_eq (t : Fin 3 → ℝ) (D : Set SL3) :
    (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' D = conjBy (-t) D := by
  have hp : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) =
      (fun g : SL3 => aDiag (-(-t)) * g * (aDiag (-(-t)))⁻¹) := by simp only [neg_neg]
  rw [hp, preimage_conj_neg (-t) D]

theorem covstep_single {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' : Set X3} {t : Fin 3 → ℝ} (hL : IsLeafwise μ U ν X')
    {x : X3} (hxX' : x ∈ X') (haxX' : aDiag t • x ∈ X')
    (hc : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
    (hBox1 : MeasurableSet (Box1 U)) {C : Set SL3} (hC : MeasurableSet C) :
    ν x C * ν (aDiag t • x) (conjBox U t) = ν (aDiag t • x) (conjBy t C) := by
  obtain ⟨c, hc0, hctop, hceq⟩ := hc
  have hmap : Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) := measurable_conj t
  have hkey : ∀ {D : Set SL3}, MeasurableSet D →
      ν (aDiag t • x) D = c * ν x (conjBy (-t) D) := by
    intro D hD
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hmap hD,
      preimage_conj_eq t D]
  have hconj1 : conjBy (-t) (conjBox U t) = Box1 U := by
    rw [conjBox, ← conjBy_add]
    have h0 : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
    rw [h0, conjBy_zero]
  have hconj2 : conjBy (-t) (conjBy t C) = C := by
    rw [← conjBy_add]
    have h0 : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
    rw [h0, conjBy_zero]
  have hboxmeas : MeasurableSet (conjBox U t) := by
    rw [conjBox, ← preimage_conj_neg t (Box1 U)]
    exact hBox1.preimage (measurable_conj (-t))
  have hCconj : MeasurableSet (conjBy t C) := by
    rw [← preimage_conj_neg t C]
    exact hC.preimage (measurable_conj (-t))
  have hc_eq : c = ν (aDiag t • x) (conjBox U t) := by
    have h1 := hkey hboxmeas
    rw [hconj1, hL.normalised x hxX', mul_one] at h1
    exact h1.symm
  have hmain : ν (aDiag t • x) (conjBy t C) = c * ν x C := by
    have h1 := hkey hCconj
    rw [hconj2] at h1
    exact h1
  rw [hmain, hc_eq]
  ring

theorem atomInfo_ae_eq_single_alt {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} {t : Fin 3 → ℝ}
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    (hcov : ∃ N : Set X3, μ N = 0 ∧ ∀ x : X3, x ∉ N → x ∈ X' → aDiag t • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
    {A : MeasurableSpace X3} {Z : Set X3}
    (hplaq : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, atomInfo A U ν t x =
      Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) -
        Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t (aDiag t • x) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨N, hN, hcovN⟩ := hcov
  have hqmp : Measure.QuasiMeasurePreserving (fun x : X3 => aDiag t • x) μ μ :=
    hmp.quasiMeasurePreserving
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [ae_iff]; exact hL.conull
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
  have hNae : ∀ᵐ x ∂μ, x ∉ N := by
    have hset : {x : X3 | ¬ x ∉ N} = N := by ext x; simp
    rw [ae_iff, hset]; exact hN
  filter_upwards [hX', hZae, hNae, hqmp.ae hX', hqmp.ae hZae]
    with x hxX' hxZ hxN haxX' haxZ
  set S : Set SL3 := shape A U (aDiag t • x) with hSdef
  obtain ⟨O, hOopen, hOeq⟩ := (hplaq.2.2.2 (aDiag t • x) haxZ).2.2.1
  have hSmeas : MeasurableSet S := by
    rw [hSdef, hOeq]
    exact hOopen.measurableSet.inter hU.1.measurableSet
  have hCmeas : MeasurableSet (conjBy (-t) S) := by
    rw [← preimage_conj_neg (-t) S]
    exact hSmeas.preimage (measurable_conj (-(-t)))
  have hconj : conjBy t (conjBy (-t) S) = S := by
    rw [← conjBy_add]
    have h0 : t + (-t) = (0 : Fin 3 → ℝ) := by funext i; simp
    rw [h0, conjBy_zero]
  have hstep := covstep_single (μ := μ) (U := U) (ν := ν) (t := t) hL hxX' haxX'
    (hcovN x hxN hxX' haxX') (measurableSet_box1 hU) (C := conjBy (-t) S) hCmeas
  rw [hconj] at hstep
  have hW : shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x = conjBy (-t) S := by
    rw [hSdef]; exact shape_comap_conj hU t x
  have hstep' : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) *
      ν (aDiag t • x) (conjBox U t) = ν (aDiag t • x) S := by
    rw [hW]; exact hstep
  obtain ⟨hposV, hltV⟩ := shape_mass_pos hL hplaq hxX' hxZ
  obtain ⟨hposVax, hltVax⟩ := shape_mass_pos hL hplaq haxX' haxZ
  obtain ⟨hposBox, hltBox⟩ := conjBox_mass_pos hL hU t haxX'
  have hne0 : ν (aDiag t • x) (conjBox U t) ≠ 0 := ne_of_gt hposBox
  have hnetop : ν (aDiag t • x) (conjBox U t) ≠ ⊤ := ne_of_lt hltBox
  have hWmass : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) =
      ν (aDiag t • x) S / ν (aDiag t • x) (conjBox U t) := by
    rw [ENNReal.eq_div_iff hne0 hnetop]
    rw [mul_comm]
    exact hstep'
  have hWne0 : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) ≠ 0 := by
    rw [hWmass]; exact ne_of_gt (ENNReal.div_pos (ne_of_gt hposVax) hnetop)
  have hWnetop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) ≠ ⊤ := by
    rw [hWmass]; exact ENNReal.div_ne_top (ne_of_lt hltVax) hne0
  have hWtoReal :
      (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal =
      (ν (aDiag t • x) S).toReal / (ν (aDiag t • x) (conjBox U t)).toReal := by
    rw [hWmass, ENNReal.toReal_div]
  have hz_ne : (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hWne0 hWnetop)
  have hy_ne : (ν x (shape A U x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposV) (ne_of_lt hltV))
  have hv_ne : (ν (aDiag t • x) S).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposVax) (ne_of_lt hltVax))
  have hc_ne : (ν (aDiag t • x) (conjBox U t)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hne0 hnetop)
  have hlogz : Real.log ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)
      = Real.log ((ν (aDiag t • x) S).toReal) -
        Real.log ((ν (aDiag t • x) (conjBox U t)).toReal) := by
    rw [hWtoReal]; exact Real.log_div hv_ne hc_ne
  have hlogmain : Real.log (((ν x (shape A U x)).toReal) /
      ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)) =
      Real.log ((ν x (shape A U x)).toReal) - Real.log ((ν (aDiag t • x) S).toReal) +
        Real.log ((ν (aDiag t • x) (conjBox U t)).toReal) := by
    rw [Real.log_div hy_ne hz_ne, hlogz]
    ring
  rw [atomInfo, hlogmain]
  simp only [growthFun]
  ring
/-! ## A.e. measurability of the two shape masses -/

theorem aemeasurable_shape_mass_two {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} {ν : X3 → Measure SL3} {X' : Set X3} (t : Fin 3 → ℝ)
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U)
    {A : MeasurableSpace X3} {Z : Set X3} (hplaq : IsPlaqueAlgebra U Z A) :
    AEMeasurable (fun x => (ν x (shape A U x)).toReal) μ ∧
      AEMeasurable (fun x => (ν x (shape
        (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal) μ := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨E, hEmeas, hAgen⟩ := exists_generating_sequence hplaq.1 hplaq.2.1
  have hV : @AEMeasurable X3 ℝ≥0∞ _ (borel X3) (fun x => ν x (shape A U x)) μ := by
    have h := aemeasurable_shape_mass_of_seq (μ := μ) (U := U) hU.1 hL hEmeas
    rwa [← hAgen] at h
  have hA'le : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ borel X3 :=
    comap_le_borel_of_le hplaq.1 t
  have hcount' : ∃ b' : Set (Set X3), b'.Countable ∧
      MeasurableSpace.comap (fun y : X3 => aDiag t • y) A =
        MeasurableSpace.generateFrom b' := by
    obtain ⟨b, hbc, hbA⟩ := hplaq.2.1
    exact ⟨Set.preimage (fun y : X3 => aDiag t • y) '' b, hbc.image _, by
      rw [hbA, MeasurableSpace.comap_generateFrom]⟩
  obtain ⟨E', hE'meas, hA'gen⟩ := exists_generating_sequence hA'le hcount'
  have hW : @AEMeasurable X3 ℝ≥0∞ _ (borel X3)
      (fun x => ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)) μ := by
    have h := aemeasurable_shape_mass_of_seq (μ := μ) (U := U) hU.1 hL hE'meas
    rwa [← hA'gen] at h
  exact ⟨hV.ennreal_toReal, hW.ennreal_toReal⟩

/-! ## Pointwise nonnegativity of `atomInfo` for a descending plaque algebra -/

theorem atomInfo_nonneg_mp {U : Subgroup SL3} {ν : X3 → Measure SL3} {t : Fin 3 → ℝ}
    {A : MeasurableSpace X3}
    (hdec : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) (x : X3) :
    0 ≤ atomInfo A U ν t x := by
  have hatom : atom A x ⊆ atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x :=
    Set.sInter_mono (fun s hs => ⟨hdec s hs.1, hs.2⟩)
  have hsub : shape A U x ⊆ shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x :=
    fun u hu => ⟨hu.1, hatom hu.2⟩
  rw [show atomInfo A U ν t x = -Real.log ((ν x (shape A U x)).toReal /
      (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)
      from rfl, neg_nonneg]
  by_cases htop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) = ⊤
  · rw [htop, ENNReal.toReal_top]
    simp
  · have hle : (ν x (shape A U x)).toReal
        ≤ (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal :=
      ENNReal.toReal_mono htop (measure_mono hsub)
    have hden0 : (0 : ℝ) ≤ (ν x (shape (MeasurableSpace.comap
        (fun y : X3 => aDiag t • y) A) U x)).toReal := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hden0 with h0 | hpos
    · rw [h0.symm, div_zero, Real.log_zero]
    · exact Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg hden0)
        ((div_le_one hpos).mpr hle)

/-! ## The main theorem -/

theorem growth_le_HcondSig_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hcov : ∃ N : Set Work.EKLContract.X3, μ N = 0 ∧ ∀ x : Work.EKLContract.X3, x ∉ N →
      x ∈ X' → Work.EKLContract.aDiag t • x ∈ X' →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g : Work.EKLContract.SL3 =>
          Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹))
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A) :
    ENNReal.ofReal (@MeasureTheory.integral Work.EKLContract.X3 ℝ _ _
        Work.EKLContract.instMeasurableSpaceX3 μ
        (fun x => Work.EKLC6Core.growthFun U ν t x)) ≤
      @Work.EKLC6Core.HcondSig Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A) := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  obtain ⟨hmassV, hmassW⟩ := aemeasurable_shape_mass_two (t := t) hL hU hplq
  have hψ_meas : AEMeasurable (fun y : X3 => Real.log ((ν y (shape A U y)).toReal)) μ :=
    Real.measurable_log.comp_aemeasurable hmassV
  have hAI_meas : AEMeasurable (fun x : X3 => atomInfo A U ν t x) μ := by
    show AEMeasurable (fun x : X3 => -Real.log ((ν x (shape A U x)).toReal /
      (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)) μ
    exact (((hmassV.div hmassW).log)).neg
  have hAI_aesm : AEStronglyMeasurable (fun x : X3 => atomInfo A U ν t x) μ :=
    hAI_meas.aestronglyMeasurable
  have hAI_nonneg_ae : 0 ≤ᵐ[μ] (fun x : X3 => atomInfo A U ν t x) :=
    Filter.Eventually.of_forall (fun x => atomInfo_nonneg_mp (U := U) (ν := ν) (t := t) hdec x)
  have hid : ∀ᵐ x ∂μ, atomInfo A U ν t x =
      Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) -
        Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t (aDiag t • x) :=
    atomInfo_ae_eq_single_alt (t := t) hL hU hmp hcov hplq hZ
  have hlin : (∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ) ≤
      @Work.EKLC6Core.HcondSig X3 instMeasurableSpaceX3 μ A
        (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) :=
    lintegral_atomInfo_le_nocov (t := t) hL hU hmp hplq hdec hZ
  by_cases hf : Integrable (fun x : X3 => growthFun U ν t x) μ
  · by_cases htop : (∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ) = ⊤
    · exact le_trans le_top (htop ▸ hlin)
    · have hAI_int : Integrable (fun x : X3 => atomInfo A U ν t x) μ :=
        (lintegral_ofReal_ne_top_iff_integrable hAI_aesm hAI_nonneg_ae).mp htop
      have hgT_int : Integrable (fun x : X3 => growthFun U ν t (aDiag t • x)) μ :=
        (hmp.integrable_comp (g := fun x : X3 => growthFun U ν t x)
          hf.aestronglyMeasurable).mpr hf
      set φ : X3 → ℝ := fun x => Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) -
          Real.log ((ν x (shape A U x)).toReal) with hφdef
      have hAI_eq : (fun x : X3 => atomInfo A U ν t x) =ᵐ[μ]
          (fun x : X3 => φ x + growthFun U ν t (aDiag t • x)) := by
        filter_upwards [hid] with x hx
        simpa only [hφdef] using hx
      have hφ_int : Integrable φ μ :=
        (hAI_int.sub hgT_int).congr (hAI_eq.mono (fun x hx => by
          simp only [Pi.sub_apply] at hx ⊢
          rw [hx]; ring))
      have hφ0 : ∫ x, φ x ∂μ = 0 := by
        refine coboundary_integral (φ := fun x : X3 => aDiag t • x) hmp
          hψ_meas.aestronglyMeasurable hφ_int ?_
        filter_upwards with x
        simp only [hφdef]
      have hgT_eq : ∫ x, growthFun U ν t (aDiag t • x) ∂μ = ∫ x, growthFun U ν t x ∂μ := by
        have h1 : ∫ y, growthFun U ν t y ∂(Measure.map (fun x : X3 => aDiag t • x) μ)
            = ∫ x, growthFun U ν t (aDiag t • x) ∂μ :=
          integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
        rw [← h1, hmp.map_eq]
      have hIntEq : ∫ x, growthFun U ν t x ∂μ = ∫ x, atomInfo A U ν t x ∂μ := by
        have h1 : ∫ x, atomInfo A U ν t x ∂μ =
            ∫ x, φ x + growthFun U ν t (aDiag t • x) ∂μ := integral_congr_ae hAI_eq
        have h2 : ∫ x, φ x + growthFun U ν t (aDiag t • x) ∂μ =
            ∫ x, φ x ∂μ + ∫ x, growthFun U ν t (aDiag t • x) ∂μ :=
          integral_add hφ_int hgT_int
        rw [h1, h2, hφ0, zero_add, hgT_eq]
      calc ENNReal.ofReal (∫ x, growthFun U ν t x ∂μ)
          = ENNReal.ofReal (∫ x, atomInfo A U ν t x ∂μ) := by rw [hIntEq]
        _ = ∫⁻ x, ENNReal.ofReal (atomInfo A U ν t x) ∂μ :=
            ofReal_integral_eq_lintegral_ofReal hAI_int hAI_nonneg_ae
        _ ≤ @Work.EKLC6Core.HcondSig X3 instMeasurableSpaceX3 μ A
              (MeasurableSpace.comap (fun x : X3 => aDiag t • x) A) := hlin
  · rw [integral_undef hf]
    simp

end

end Work.EKLC6Core
