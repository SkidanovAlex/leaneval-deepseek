import Mathlib
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.structAtH
import Submission.Work.EKLRelProduct.psiEqNuU
import Submission.Work.EKLRelProduct.leafFacts
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLProd.prodFlower_T_slice
import Submission.Work.EKLProd.ProdFlowerDefs

open MeasureTheory
open Work.EKLContract Work.EKLProd
open scoped ENNReal

noncomputable section

namespace Work.EKLRelProduct

set_option linter.unusedVariables false

/-- The geometric content of the two source sets: an element of `T · U` lies in the shape iff its
two factors do. -/
theorem mem_shape_iff_factor {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ) {y : X3}
    (hy : y ∈ hf.Z n) :
    ∀ t' ∈ T, ∀ u' ∈ U,
      t' * u' ∈ shape (hf.mH n) H y ↔ t' ∈ S_T hf n y ∧ u' ∈ S_U hf n y := by
  have hcoH : hf.co n y ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n y hy)
  obtain ⟨t₀, ht₀, u₀, hu₀, hdec⟩ := hf.co_mem n y hy
  have htu : hT T U (hf.co n y) * hU T U (hf.co n y) = hf.co n y :=
    hT_mul_hU ⟨t₀, ht₀.2, u₀, hu₀.2, hdec.symm⟩
  have hty : hT T U (hf.co n y) ∈ T := hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, hdec.symm⟩
  have huy : hU T U (hf.co n y) ∈ U := hU_mem ⟨t₀, ht₀.2, u₀, hu₀.2, hdec.symm⟩
  have htV : hT T U (hf.co n y) ∈ V hf.R := by
    rw [hT_eq_of_factor hcop hdisj hcoH ht₀.2 hu₀.2 hdec]; exact ht₀.1
  have huV : hU T U (hf.co n y) ∈ V hf.R := by
    rw [hU_eq_of_factor hdisj ht₀.2 hu₀.2 hdec]; exact hu₀.1
  have hkey : ∀ t' u', (t' * u') * hf.co n y
      = (t' * hT T U (hf.co n y)) * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) u' := by
    intro t' u'
    conv_lhs => rw [← htu]
    simp only [shiftMap]
    group
  have hUkey : ∀ u', shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) u' ∈ U ↔ u' ∈ U :=
    fun u' => shiftMap_mem_U_iff hnorm hty huy u'
  intro t' ht' u' hu'
  constructor
  · intro hmem
    rw [hf.shapeH n y hy] at hmem
    have hmem' : (t' * u') * hf.co n y ∈ prodBox T U hf.R := hmem.2
    rw [hkey t' u'] at hmem'
    have hTmem : t' * hT T U (hf.co n y) ∈ T := T.mul_mem ht' hty
    have hUmem : shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) u' ∈ U :=
      (hUkey u').mpr hu'
    have hV := (prodBox_mem_iff_of_decomp hdisj hTmem hUmem rfl).mp hmem'
    exact ⟨⟨hV.1, hTmem⟩, ⟨hV.2, hUmem⟩⟩
  · rintro ⟨⟨ht'V, ht'T⟩, ⟨hu'V, hu'U⟩⟩
    rw [hf.shapeH n y hy]
    refine ⟨H.mul_mem (hTH ht') (hUH hu'), ?_⟩
    rw [hkey t' u']
    exact (prodBox_mem_iff_of_decomp hdisj (T.mul_mem ht' hty)
      ((hUkey u').mpr hu') rfl).mpr ⟨ht'V, hu'V⟩



set_option linter.unusedVariables false

/-- Integrating over `μ ↾ s` equals integrating over `μ` when the integrand vanishes a.e. off `s`. -/
theorem integral_restrict_eq_of_ae_eq_zero {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {s : Set α} (hs : MeasurableSet s) (g : α → ℝ)
    (h : ∀ᵐ x ∂(μ.restrict sᶜ), g x = 0) :
    ∫ x, g x ∂(μ.restrict s) = ∫ x, g x ∂μ := by
  rw [MeasureTheory.ae_restrict_iff' hs.compl] at h
  exact MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero h



set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem locStruct_core {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {νH : X3 → MeasureTheory.Measure SL3} {XH : Set X3} (hνH : IsLeafwise μ H νH XH)
    {νT : X3 → MeasureTheory.Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    {νU : X3 → MeasureTheory.Measure SL3} {XU : Set X3} (hνU : IsLeafwise μ U νU XU)
    (hmeas : Measurable (fun w : SL3 => (hT T U w, hU T U w)))
    {y : X3} (hyZ : y ∈ hf.Z n)
    (hR : ∀ {A' B' : Set SL3}, MeasurableSet A' → MeasurableSet B' →
       ((νH y).restrict (shape (hf.mH n) H y)) {w | hT T U w ∈ A' ∧ hU T U w ∈ B'} =
       etaT hf νT n y A' * psi hf νH n y B')
    (hP : ∃ cU : ENNReal, 0 < cU ∧ cU ≠ ⊤ ∧ psi hf νH n y = cU • (νU y).restrict (S_U hf n y))
    (hyXT : y ∈ XT) (hyXU : y ∈ XU)
    (hST0 : 0 < (νT y) (S_T hf n y)) (hSTt : (νT y) (S_T hf n y) < ⊤)
    (hSH0 : 0 < (νH y) (shape (hf.mH n) H y)) (hSHt : (νH y) (shape (hf.mH n) H y) < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Function.support (fun z => f z) ⊆ shape (hf.mH n) H y →
      (∫ z, f z ∂(νH y)) = c * ∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂(νT y) := by
  obtain ⟨cU, hcU0, hcUt, hPeq⟩ := hP
  -- finiteness of the `U`-shape mass, from `hPeq` and finiteness of `psi`
  have hUmeas : Measurable (fun w : SL3 => hU T U w) := measurable_snd.comp hmeas
  have hpsifin : psi hf νH n y Set.univ < ⊤ := by
    rw [psi, MeasureTheory.Measure.map_apply_of_aemeasurable hUmeas.aemeasurable
      MeasurableSet.univ]
    simp only [Set.preimage_univ, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    exact hSHt
  have hSUt : (νU y) (S_U hf n y) < ⊤ := by
    have h1 : cU * ((νU y) (S_U hf n y)) < ⊤ := by
      have := hpsifin
      rw [hPeq, MeasureTheory.Measure.smul_apply] at this
      rwa [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at this
    rcases (ENNReal.mul_lt_top_iff.mp h1) with ⟨-, h2⟩ | h2 | h2
    · simpa using h2
    · exact absurd h2 hcU0.ne'
    · exact h2 ▸ (by simp)
  haveI hpsiInst : IsFiniteMeasure (psi hf νH n y) := ⟨hpsifin⟩
  haveI hfinT : IsFiniteMeasure ((νT y).restrict (S_T hf n y)) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hSTt.ne
  haveI hfinU : IsFiniteMeasure ((νU y).restrict (S_U hf n y)) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hSUt.ne
  haveI hfinPU : IsFiniteMeasure
      (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y))) := inferInstance
  -- measurability of the two source sets and of the shape
  have hVRopen : IsOpen (V hf.R) :=
    (Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1
  have hBmeas : MeasurableSet (V hf.R ∩ (T : Set SL3)) :=
    hVRopen.measurableSet.inter hTc.measurableSet
  have hCmeas : MeasurableSet (V hf.R ∩ (U : Set SL3)) :=
    hVRopen.measurableSet.inter hUc.measurableSet
  have hSTmeas : MeasurableSet (S_T hf n y) :=
    hBmeas.preimage (measurable_mul_const _)
  have hSUmeas : MeasurableSet (S_U hf n y) :=
    hCmeas.preimage (by unfold shiftMap; fun_prop)
  have hSymeas : MeasurableSet (shape (hf.mH n) H y) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 y hyZ).2.2.1
    rw [hOsh]; exact hOo.measurableSet.inter hHc.measurableSet
  -- the geometric fact
  have hfac := mem_shape_iff_factor hTH hUH hnorm hcop hdisj hf n hyZ
  have htyT : hT T U (hf.co n y) ∈ T := by
    obtain ⟨a, ha, b, hb, hab⟩ := hf.co_mem n y hyZ
    exact hT_mem ⟨a, ha.2, b, hb.2, hab.symm⟩
  have hUae : ∀ᵐ u ∂(νU y), u ∈ U := by
    rw [MeasureTheory.ae_iff]; exact hνU.carried y hyXU
  have hTae : ∀ᵐ t' ∂(νT y), t' ∈ T := by
    rw [MeasureTheory.ae_iff]; exact hνT.carried y hyXT
  refine ⟨(cU * ((νT y) (S_T hf n y))⁻¹).toReal, ?_, ?_⟩
  · rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
    exact mul_pos (ENNReal.toReal_pos hcU0.ne' hcUt)
      (inv_pos.mpr (ENNReal.toReal_pos hST0.ne' hSTt.ne))
  · intro f hfs
    set κ : MeasureTheory.Measure (SL3 × SL3) :=
      ((νH y).restrict (shape (hf.mH n) H y)).map (fun w : SL3 => (hT T U w, hU T U w)) with hκdef
    haveI hfinR : IsFiniteMeasure ((νH y).restrict (shape (hf.mH n) H y)) :=
      MeasureTheory.isFiniteMeasure_restrict.2 hSHt.ne
    haveI hκfin : IsFiniteMeasure κ := hκdef ▸ MeasureTheory.Measure.isFiniteMeasure_map _ _
    have hκeq : κ = (etaT hf νT n y).prod (psi hf νH n y) := by
      refine MeasureTheory.Measure.ext_prod (fun {A' B'} hA' hB' => ?_)
      rw [hκdef, MeasureTheory.Measure.map_apply hmeas (hA'.prod hB')]
      rw [show (fun w : SL3 => (hT T U w, hU T U w)) ⁻¹' (A' ×ˢ B')
          = {w : SL3 | hT T U w ∈ A' ∧ hU T U w ∈ B'} from rfl]
      rw [MeasureTheory.Measure.prod_prod]
      exact hR hA' hB'
    have hI1 : (∫ z, f z ∂(νH y)) =
        ∫ z, f z ∂((νH y).restrict (shape (hf.mH n) H y)) := by
      refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := shape (hf.mH n) H y) (f := fun z => f z) (fun z hz => ?_)).symm
      by_contra hne
      exact hz (hfs hne)
    have hI2 : (∫ z, f z ∂((νH y).restrict (shape (hf.mH n) H y))) =
        ∫ p : SL3 × SL3, f (p.1 * p.2) ∂κ := by
      rw [hκdef, MeasureTheory.integral_map_of_stronglyMeasurable hmeas]
      · refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem hSymeas] with z hz
        have hzH : z ∈ H := (by rw [hf.shapeH n y hyZ] at hz; exact hz.1)
        rw [show f z = f (hT T U z * hU T U z) from by rw [hT_mul_hU (hcop z hzH)]]
      · exact ((map_continuous f).comp (continuous_fst.mul continuous_snd)).stronglyMeasurable
    have hI5 : (∫ p : SL3 × SL3, f (p.1 * p.2) ∂((etaT hf νT n y).prod (psi hf νH n y))) =
        (cU * ((νT y) (S_T hf n y))⁻¹).toReal
          * ∫ p : SL3 × SL3, f (p.1 * p.2) ∂
              (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y))) := by
      have hI4 : (etaT hf νT n y).prod (psi hf νH n y)
          = (cU * ((νT y) (S_T hf n y))⁻¹) •
              (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y))) := by
        rw [etaT, hPeq, MeasureTheory.Measure.prod_smul_left,
          MeasureTheory.Measure.prod_smul_right, smul_smul, mul_comm]
      rw [hI4, MeasureTheory.integral_smul_measure, smul_eq_mul]
    have hInt6 : Integrable (fun p : SL3 × SL3 => f (p.1 * p.2))
        (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y))) := by
      refine Integrable.of_bound
        ((map_continuous f).comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable
        ‖f.toBoundedContinuousFunction‖ ?_
      filter_upwards with p
      exact (f.toBoundedContinuousFunction).norm_coe_le_norm (p.1 * p.2)
    have hI6 : (∫ p : SL3 × SL3, f (p.1 * p.2) ∂
          (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y)))) =
        ∫ t', (∫ u, f (t' * u) ∂((νU y).restrict (S_U hf n y)))
          ∂((νT y).restrict (S_T hf n y)) :=
      MeasureTheory.integral_prod _ hInt6
    have hG1 : (∫ t', (∫ u, f (t' * u) ∂((νU y).restrict (S_U hf n y)))
          ∂((νT y).restrict (S_T hf n y))) =
        ∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂((νT y).restrict (S_T hf n y)) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hSTmeas] with t' ht'ST
      have ht'T : t' ∈ T := by
        have := T.mul_mem ht'ST.2 (T.inv_mem htyT)
        rwa [show t' * hT T U (hf.co n y) * (hT T U (hf.co n y))⁻¹ = t' from by group] at this
      refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
      filter_upwards [hUae] with u huU hnuSU
      by_contra hne
      exact hnuSU ((hfac t' ht'T u huU).mp (hfs hne)).2
    have hG2 : (∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂((νT y).restrict (S_T hf n y))) =
        ∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂(νT y) := by
      refine MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero ?_
      filter_upwards [hTae] with t' ht'T hntST
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hUae] with u huU
      by_contra hne
      exact hntST ((hfac t' ht'T u huU).mp (hfs hne)).1
    calc (∫ z, f z ∂(νH y))
        = ∫ p : SL3 × SL3, f (p.1 * p.2) ∂κ := hI1.trans hI2
      _ = ∫ p : SL3 × SL3, f (p.1 * p.2) ∂((etaT hf νT n y).prod (psi hf νH n y)) := by rw [hκeq]
      _ = (cU * ((νT y) (S_T hf n y))⁻¹).toReal
            * ∫ p : SL3 × SL3, f (p.1 * p.2) ∂
                (((νT y).restrict (S_T hf n y)).prod ((νU y).restrict (S_U hf n y))) := hI5
      _ = (cU * ((νT y) (S_T hf n y))⁻¹).toReal
            * ∫ t', (∫ u, f (t' * u) ∂((νU y).restrict (S_U hf n y)))
                ∂((νT y).restrict (S_T hf n y)) := by rw [hI6]
      _ = (cU * ((νT y) (S_T hf n y))⁻¹).toReal
            * ∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂((νT y).restrict (S_T hf n y)) := by rw [hG1]
      _ = (cU * ((νT y) (S_T hf n y))⁻¹).toReal
            * ∫ t', (∫ u, f (t' * u) ∂(νU y)) ∂(νT y) := by rw [hG2]


theorem locStruct {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H T U : Subgroup Work.EKLContract.SL3} (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hmu : Work.EKLContract.IsAInvariant μ) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)), ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ, Function.support (fun z => f z) ⊆ Work.EKLContract.shape (hf.mH n) H (h • x) → (∫ z, f z ∂(νH (h • x))) = c * ∫ t', (∫ u, f (t' * u) ∂(νU (h • x))) ∂(νT (h • x)) := by
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hmeas : Measurable (fun w : Work.EKLContract.SL3 =>
      (Work.EKLProd.hT T U w, Work.EKLProd.hU T U w)) :=
    measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hH.1 hT.1 hU.1
  filter_upwards [structAtH hX3 hLeaf hBirk hH hT hUH hTH hnorm hcop hdisj hmu hf n hνH hνT t hcent hcontr,
                  psiEqNuU hX3 hLeaf hBirk hH hT hU hTH hUH hnorm hcop hdisj hmu hf n hνH hνT hνU t hcent hcontr,
                  leafFacts hX3 hLeaf hBirk hH hT hU hTH hUH hnorm hcop hdisj hmu hf n hνH hνT hνU,
                  MeasureTheory.ae_restrict_mem hZmeas] with x hst hps hl hxZ
  have hSxmeas : MeasurableSet (Work.EKLContract.shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOsh]; exact hOo.measurableSet.inter hH.1.measurableSet
  filter_upwards [hst, hps, hl, MeasureTheory.ae_restrict_mem hSxmeas] with h hst' hps' hl' hhshape
  obtain ⟨⟨hXH, hXT, hXU⟩, ⟨hST0, hSTt⟩, ⟨hSH0, hSHt⟩⟩ := hl'
  have hyZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hhshape.2
  exact locStruct_core hTH hUH hnorm hcop hdisj hH.1 hT.1 hU.1 hf n hνH hνT hνU hmeas hyZ
    hst' hps' hXT hXU hST0 hSTt hSH0 hSHt

end Work.EKLRelProduct
