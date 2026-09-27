import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLRelProduct.uAvg_eq
import Submission.Work.EKLRelProduct.psiNu_uMargEqPsiMap
import Submission.Work.EKLRelProduct.psiEqNuU
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLRelProduct.psi_eq_smul_nuU_restrict_of_atomId
import Submission.Work.EKLProd.S_T_mass_pos_and_lt_top_of_P1
import Submission.Work.EKLProd.mul_prod_restrict_shape_eq
import Submission.Work.EKLRelCross.SL3famDefs
import Submission.Work.EKLRelCross.Instances

/-!
# `Work.EKLProd.atomId_derives_target`

At the base point `x` of a product-box flower, the `(8.12c)` identification `Work.EKLProd.atomId`
(the translate of the `U`-leafwise measure is proportional to the `U`-marginal of the plaque
measure) together with the product structure `hP1` of the plaque coordinate law implies the
atom-level product structure

  `(νH x) ↾ shape (mH n) H x = c • (mul_*((νT x) ⊗ (νU x))) ↾ shape (mH n) H x`,  `0 < c`.

Route.  The coordinate map `ϑ w = (hT T U w, hU T U w)` is injective on `H` with left inverse
`mul`; the substitution `t = t' * t_x`, `u = t_x⁻¹ * u' * t_x * u_x` (where `co n x = t_x * u_x`)
turns the `T`-`U`-coordinates of the translate `w * co n x` into the translate of `ϑ w`, so `hP1`
pushes back to the coordinate law at the base point (`Work.EKLProd.coordinateLaw_eq_prod`).  The
`(8.12c)` identification identifies the `U`-factor with `νU x ↾ S_U`
(`Work.EKLRelProduct.psi_eq_smul_nuU_restrict_of_atomId`), the geometry of the source sets `S_T`,
`S_U` gives the multiplication form of the right-hand side
(`Work.EKLProd.mul_prod_restrict_shape_eq`), and the normalising `T`-mass is positive and finite
by `Work.EKLProd.S_T_mass_pos_and_lt_top_of_P1`.
-/

open MeasureTheory
open scoped ENNReal

namespace Work.EKLProd

open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-- The two change-of-coordinate identities for the plaque coordinate of a point of the `H`-shape. -/
theorem mul_co_facts_of_mem_shape {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {x : X3} (hxZ : x ∈ hf.Z n) {w : SL3} (hw : w ∈ shape (hf.mH n) H x) :
    hT T U (w * hf.co n x) = hT T U w * hT T U (hf.co n x) ∧
      hU T U (w * hf.co n x)
        = Work.EKLRelProduct.shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x)) (hU T U w) := by
  have hw' := hw
  rw [hf.shapeH n x hxZ] at hw'
  obtain ⟨hwH, hwco⟩ := hw'
  obtain ⟨a₀, ha₀, b₀, hb₀, hdec₀⟩ := hf.co_mem n x hxZ
  have hexco : ∃ a ∈ T, ∃ b ∈ U, hf.co n x = a * b := ⟨a₀, ha₀.2, b₀, hb₀.2, hdec₀.symm⟩
  have hdec : hT T U (hf.co n x) * hU T U (hf.co n x) = hf.co n x := hT_mul_hU hexco
  have htT : hT T U (hf.co n x) ∈ T := hT_mem hexco
  have huU : hU T U (hf.co n x) ∈ U := hU_mem hexco
  have hexw : ∃ g ∈ T, ∃ u ∈ U, w = g * u := hcop w hwH
  have htw : hT T U w * hU T U w = w := hT_mul_hU hexw
  have htwT : hT T U w ∈ T := hT_mem hexw
  have huwU : hU T U w ∈ U := hU_mem hexw
  have hshiftU : Work.EKLRelProduct.shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x)) (hU T U w)
      ∈ U :=
    (Work.EKLRelProduct.shiftMap_mem_U_iff hnorm htT huU (hU T U w)).mpr huwU
  have hkey : (hT T U w * hT T U (hf.co n x))
        * Work.EKLRelProduct.shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))
            (hU T U w) = w * hf.co n x := by
    calc (hT T U w * hT T U (hf.co n x))
          * Work.EKLRelProduct.shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x)) (hU T U w)
        = hT T U w * (hT T U (hf.co n x)
            * Work.EKLRelProduct.shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))
                (hU T U w)) := by group
      _ = hT T U w * (hU T U w
            * (hT T U (hf.co n x) * hU T U (hf.co n x))) := by
          rw [← Work.EKLRelProduct.shiftMap_mul]
      _ = hT T U w * (hU T U w * hf.co n x) := by rw [hdec]
      _ = w * hf.co n x := by rw [← mul_assoc, htw]
  exact ⟨hT_eq_of_factor hcop hdisj (prodBox_subset_H hTH hUH hwco)
      (T.mul_mem htwT htT) hshiftU hkey,
    hU_eq_of_factor hdisj (T.mul_mem htwT htT) hshiftU hkey⟩

/-- **The coordinate law of the plaque measure at the base point is the product of the
`T`-factor `etaT` and the `U`-factor `psi`.** -/
theorem coordinateLaw_eq_prod {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νH νT : X3 → MeasureTheory.Measure SL3) {x : X3} (hxZ : x ∈ hf.Z n)
    (hSHt : (νH x) (shape (hf.mH n) H x) < ⊤)
    (hP1 : prodFlowerΛTP hf n νH x
        = (prodFlowerκ hf n νT x).prod ((prodFlowerΛTP hf n νH x).map Prod.snd)) :
    ((νH x).restrict (shape (hf.mH n) H x)).map (fun w => (hT T U w, hU T U w))
      = (Work.EKLRelProduct.etaT hf νT n x).prod (Work.EKLRelProduct.psi hf νH n x) := by
  classical
  set t : SL3 := hT T U (hf.co n x) with ht
  set u : SL3 := hU T U (hf.co n x) with hu
  set sM : SL3 → SL3 := Work.EKLRelProduct.shiftMap t u with hsM
  set sinv : SL3 → SL3 := fun q => t * q * u⁻¹ * t⁻¹ with hsinv
  set Φ : SL3 × SL3 → SL3 × SL3 := Prod.map (fun p => p * t) sM with hΦ
  set Ψ : SL3 × SL3 → SL3 × SL3 := Prod.map (fun p => p * t⁻¹) sinv with hΨ
  have hsMmeas : Measurable sM := by
    rw [hsM]; exact (Work.EKLRelProduct.measurableEmbedding_shiftMap t u).measurable
  have hsinvmeas : Measurable sinv := by rw [hsinv]; fun_prop
  have hΦmeas : Measurable Φ := by
    rw [hΦ]; exact ((continuous_mul_const t).measurable).prodMap hsMmeas
  have hΨmeas : Measurable Ψ := by
    rw [hΨ]; exact ((continuous_mul_const t⁻¹).measurable).prodMap hsinvmeas
  have hϑ : Measurable (fun w : SL3 => (hT T U w, hU T U w)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc
  have hco_meas : Measurable (fun w : SL3 => w * hf.co n x) := (continuous_mul_const _).measurable
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOsh]; exact hOo.measurableSet.inter hHc.measurableSet
  have hΛTP : prodFlowerΛTP hf n νH x
      = ((νH x).restrict (shape (hf.mH n) H x)).map
          (fun w : SL3 => (hT T U (w * hf.co n x), hU T U (w * hf.co n x))) := by
    rw [prodFlowerΛTP, prodFlowerΛ, Measure.map_map hϑ hco_meas]
    rfl
  have h2 : (((νH x).restrict (shape (hf.mH n) H x)).map
        (fun w : SL3 => (hT T U w, hU T U w))).map Φ = prodFlowerΛTP hf n νH x := by
    rw [hΛTP, Measure.map_map hΦmeas hϑ]
    refine Measure.map_congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with w hw
    obtain ⟨h1, h2'⟩ := mul_co_facts_of_mem_shape hTH hUH hnorm hcop hdisj hf n hxZ hw
    rw [← ht] at h1 h2'
    rw [← hu] at h2'
    simp only [Function.comp_apply, hΦ, Prod.map, hsM]
    exact Prod.ext h1.symm h2'.symm
  have hΨΦ : Ψ ∘ Φ = id := by
    funext p
    obtain ⟨p1, p2⟩ := p
    simp only [Function.comp_apply, hΦ, hΨ, Prod.map, hsM, hsinv,
      Work.EKLRelProduct.shiftMap, id_eq]
    exact Prod.ext (by group) (by group)
  have hback : ((((νH x).restrict (shape (hf.mH n) H x)).map
        (fun w : SL3 => (hT T U w, hU T U w))).map Φ).map Ψ
      = ((νH x).restrict (shape (hf.mH n) H x)).map (fun w : SL3 => (hT T U w, hU T U w)) := by
    rw [Measure.map_map hΨmeas hΦmeas, hΨΦ, Measure.map_id]
  haveI hfinM : IsFiniteMeasure ((νH x).restrict (shape (hf.mH n) H x)) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hSHt.ne
  haveI hfinΛ : IsFiniteMeasure (prodFlowerΛ hf n νH x) := by
    rw [prodFlowerΛ]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  haveI hfinΛTP : IsFiniteMeasure (prodFlowerΛTP hf n νH x) := by
    rw [prodFlowerΛTP]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  haveI hfinσ : IsFiniteMeasure ((prodFlowerΛTP hf n νH x).map Prod.snd) :=
    MeasureTheory.Measure.isFiniteMeasure_map _ _
  haveI hfinκ : IsFiniteMeasure (prodFlowerκ hf n νT x) := by
    refine ⟨?_⟩
    rw [prodFlowerκ, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) (by simp)
  have hM4 : ((prodFlowerκ hf n νT x).prod ((prodFlowerΛTP hf n νH x).map Prod.snd)).map Ψ
      = ((prodFlowerκ hf n νT x).map (fun p : SL3 => p * t⁻¹)).prod
          (((prodFlowerΛTP hf n νH x).map Prod.snd).map sinv) := by
    rw [hΨ, ← MeasureTheory.Measure.map_prod_map (prodFlowerκ hf n νT x)
      ((prodFlowerΛTP hf n νH x).map Prod.snd) ((continuous_mul_const t⁻¹).measurable) hsinvmeas]
  have hmapco : ((νT x).map (fun p : SL3 => p * t)) (V hf.R ∩ (T : Set SL3))
      = (νT x) (Work.EKLRelProduct.S_T hf n x) := by
    rw [Measure.map_apply (continuous_mul_const t).measurable
      (((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet.inter
        hTc.measurableSet)]
    congr 1
  have hM5 : (prodFlowerκ hf n νT x).map (fun p : SL3 => p * t⁻¹)
      = Work.EKLRelProduct.etaT hf νT n x := by
    rw [prodFlowerκ, Work.EKLRelProduct.etaT, Measure.map_smul, hmapco] <;> try fun_prop
    congr 1
    rw [Work.EKLRelProduct.measure_map_restrict (νT x) (continuous_mul_const t).measurable
      (((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet.inter
        hTc.measurableSet)]
    have hpre : (fun p : SL3 => p * t) ⁻¹' (V hf.R ∩ (T : Set SL3))
        = Work.EKLRelProduct.S_T hf n x := rfl
    have hcomp : (fun p : SL3 => p * t⁻¹) ∘ (fun p : SL3 => p * t) = id := by
      funext q
      simp only [Function.comp_apply, id_eq]
      group
    rw [hpre, Measure.map_map (continuous_mul_const t⁻¹).measurable
      (continuous_mul_const t).measurable, hcomp, Measure.map_id]
  have hσuMarg : (prodFlowerΛTP hf n νH x).map Prod.snd
      = Work.EKLRelProduct.uMarg hf νH n x := by
    rw [prodFlowerΛTP, prodFlowerΛ, Work.EKLRelProduct.uMarg,
      Measure.map_map measurable_snd hϑ,
      Measure.map_map (measurable_snd.comp hϑ) hco_meas]
    refine Measure.map_congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with w hw
    simp only [Function.comp_apply]
    rw [hf.co_smul n x hxZ w hw.1 hw.2]
  have hM6 : ((prodFlowerΛTP hf n νH x).map Prod.snd).map sinv
      = Work.EKLRelProduct.psi hf νH n x := by
    rw [hσuMarg, Work.EKLRelProduct.psiNu_uMargEqPsiMap hTH hUH hnorm hcop hdisj hHc hTc hUc
      hf n νH hxZ]
    have hcomp : sinv ∘ sM = id := by
      funext q
      simp only [Function.comp_apply, id_eq, hsM, hsinv, Work.EKLRelProduct.shiftMap]
      group
    rw [Measure.map_map hsinvmeas hsMmeas, hcomp, Measure.map_id]
  rw [← hback, h2, hP1, hM4, hM5, hM6]


theorem atomId_derives_target {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : Work.EKLContract.X3} (hxZ : x ∈ hf.Z n)
    (hcarT : (νT x) (T : Set Work.EKLContract.SL3)ᶜ = 0)
    (hcarU : (νU x) (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (hfinT : MeasureTheory.IsFiniteMeasureOnCompacts (νT x))
    (hfinU : MeasureTheory.IsFiniteMeasureOnCompacts (νU x))
    (hP1 : Work.EKLProd.prodFlowerΛTP hf n νH x =
      (Work.EKLProd.prodFlowerκ hf n νT x).prod
        ((Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd))
    (hmass : 0 < (νH x) (Work.EKLContract.shape (hf.mH n) H x) ∧
      (νH x) (Work.EKLContract.shape (hf.mH n) H x) < ⊤)
    (hId : Work.EKLProd.atomId hf n νH νU x) :
    ∃ c : ℝ, 0 < c ∧ (νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)
      = ENNReal.ofReal c • ((((νT x).prod (νU x)).map
          (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2)).restrict
            (Work.EKLContract.shape (hf.mH n) H x)) := by
  classical
  have hL1 := Work.EKLRelProduct.psi_eq_smul_nuU_restrict_of_atomId hTH hUH hnorm hcop hdisj
    hHc hTc hUc hf n hxZ hId
  have hL3 := Work.EKLProd.S_T_mass_pos_and_lt_top_of_P1 hTH hUH hnorm hcop hdisj hHc hTc hUc
    hf n hxZ hmass hP1
  have hL4 := Work.EKLProd.mul_prod_restrict_shape_eq hTH hUH hnorm hcop hdisj hHc hTc hUc
    hf n hxZ hfinT hfinU hcarT hcarU
  obtain ⟨cU, hcU0, hcUt, hpsi⟩ := hL1
  obtain ⟨hd0, hdt⟩ := hL3
  have hL2 := coordinateLaw_eq_prod hTH hUH hnorm hcop hdisj hHc hTc hUc hf n νH νT hxZ hmass.2 hP1
  have hϑ : Measurable (fun w : SL3 => (hT T U w, hU T U w)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc
  have hmulmeas : Measurable (fun p : SL3 × SL3 => p.1 * p.2) :=
    (continuous_fst.mul continuous_snd).measurable
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOsh]; exact hOo.measurableSet.inter hHc.measurableSet
  have hcomp : (fun p : SL3 × SL3 => p.1 * p.2) ∘ (fun w : SL3 => (hT T U w, hU T U w))
      =ᵐ[(νH x).restrict (shape (hf.mH n) H x)] id := by
    filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with w hw
    have hw' := hw
    rw [hf.shapeH n x hxZ] at hw'
    show hT T U w * hU T U w = w
    exact hT_mul_hU (hcop w hw'.1)
  have hstep1 : (((νH x).restrict (shape (hf.mH n) H x)).map
        (fun w : SL3 => (hT T U w, hU T U w))).map
        (fun p : SL3 × SL3 => p.1 * p.2)
      = (νH x).restrict (shape (hf.mH n) H x) := by
    rw [Measure.map_map hmulmeas hϑ, Measure.map_congr hcomp, Measure.map_id]
  haveI hsfU : SFinite ((νU x).restrict (Work.EKLRelProduct.S_U hf n x)) := by
    haveI : SigmaFinite (νU x) := MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts (νU x)
    infer_instance
  have hprod : (Work.EKLRelProduct.etaT hf νT n x).prod (Work.EKLRelProduct.psi hf νH n x)
      = (cU * ((νT x) (Work.EKLRelProduct.S_T hf n x))⁻¹) •
          (((νT x).restrict (Work.EKLRelProduct.S_T hf n x)).prod
            ((νU x).restrict (Work.EKLRelProduct.S_U hf n x))) := by
    rw [Work.EKLRelProduct.etaT, hpsi, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul, mul_comm]
  have hfinal : (νH x).restrict (shape (hf.mH n) H x)
      = (cU * ((νT x) (Work.EKLRelProduct.S_T hf n x))⁻¹) •
          ((((νT x).prod (νU x)).map
            (fun p : SL3 × SL3 => p.1 * p.2)).restrict (shape (hf.mH n) H x)) := by
    rw [← hstep1, hL2, hprod, Measure.map_smul, hL4] <;> try fun_prop
  have hcc0 : cU * ((νT x) (Work.EKLRelProduct.S_T hf n x))⁻¹ ≠ 0 :=
    mul_ne_zero hcU0.ne' (ENNReal.inv_ne_zero.mpr hdt.ne)
  have hcct : cU * ((νT x) (Work.EKLRelProduct.S_T hf n x))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hcUt (ENNReal.inv_ne_top.mpr hd0.ne')
  refine ⟨(cU * ((νT x) (Work.EKLRelProduct.S_T hf n x))⁻¹).toReal,
    ENNReal.toReal_pos hcc0 hcct, ?_⟩
  rw [ENNReal.ofReal_toReal hcct]
  exact hfinal
end Work.EKLProd
