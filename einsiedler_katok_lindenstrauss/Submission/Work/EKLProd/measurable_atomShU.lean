import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLC6Core.measurable_apply_section
import Submission.Work.EKLContract.Lemmas.V_open_one

namespace Work.EKLProd

open MeasureTheory

/-- `atomShU` written with the conjugation of `uShift` spelled out:
`(uShift hf νU n y) ↾ (V R ∩ U)` is the push-forward of `νU y` under
`u ↦ (hT T U (co n y))⁻¹ * u * (hT T U (co n y)) * (hU T U (co n y))`, restricted to
`V hf.R ∩ U`. -/
private lemma atomShU_eq_map_conj {H T U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (y : Work.EKLContract.X3) :
    atomShU hf n νU y = ((νU y).map (fun u : Work.EKLContract.SL3 =>
      (hT T U (hf.co n y))⁻¹ * u * (hT T U (hf.co n y)) *
        (hU T U (hf.co n y)))).restrict
        (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)) := by
  have hfun : (fun u : Work.EKLContract.SL3 =>
        Work.EKLRelProduct.gconj (hT T U (hf.co n y))⁻¹ u * (hU T U (hf.co n y)))
      = (fun u : Work.EKLContract.SL3 =>
          (hT T U (hf.co n y))⁻¹ * u * (hT T U (hf.co n y)) * (hU T U (hf.co n y))) := by
    funext u
    simp only [Work.EKLRelProduct.gconj]
    rw [inv_inv]
  rw [atomShU, Work.EKLRelProduct.uShift, hfun]

theorem measurable_atomShU {H T U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {κ : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    (hmeas : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      Measurable fun y => ∫ g, f g ∂(κ y))
    (hfin : ∀ y, MeasureTheory.IsFiniteMeasureOnCompacts (κ y))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {S : Set Work.EKLContract.SL3} (hS : MeasurableSet S) :
    Measurable fun y => Work.EKLProd.atomShU hf n κ y S := by
  classical
  -- ## the target set (the `U`-ball) is measurable
  have hR : 0 < hf.R := lt_of_lt_of_le zero_lt_one hf.one_le_R
  have hVmeas : MeasurableSet (Work.EKLContract.V hf.R) :=
    (Work.EKLContract.Lemmas.V_open_one hf.R hR).1.measurableSet
  have hUmeas : MeasurableSet (U : Set Work.EKLContract.SL3) := hUc.measurableSet
  have hS'meas : MeasurableSet
      (S ∩ (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))) :=
    hS.inter (hVmeas.inter hUmeas)
  -- ## joint measurability of the conjugated coordinate map
  have ha : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
      hT T U (hf.co n p.1) := (hf.meas_tp n).comp measurable_fst
  have hb : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
      hU T U (hf.co n p.1) := (hf.meas_up n).comp measurable_fst
  have hcoord : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
      (hT T U (hf.co n p.1))⁻¹ * p.2 * (hT T U (hf.co n p.1)) * (hU T U (hf.co n p.1)) :=
    ((ha.inv.mul measurable_snd).mul ha).mul hb
  -- ## the "graph" of the conjugated coordinate map
  have hTset : MeasurableSet {p : Work.EKLContract.X3 × Work.EKLContract.SL3 |
      (hT T U (hf.co n p.1))⁻¹ * p.2 * (hT T U (hf.co n p.1)) * (hU T U (hf.co n p.1)) ∈
        S ∩ (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))} :=
    hcoord hS'meas
  -- ## section measurability of the weakly measurable, locally finite family `κ`
  have hsec := Work.EKLC6Core.measurable_apply_section (τ := Work.EKLContract.X3)
    hmeas hfin hTset
  -- ## identify `atomShU` with the section of that graph
  have hgoal : (fun y : Work.EKLContract.X3 => Work.EKLProd.atomShU hf n κ y S) =
      fun y : Work.EKLContract.X3 => κ y (Prod.mk y ⁻¹'
        {p : Work.EKLContract.X3 × Work.EKLContract.SL3 |
          (hT T U (hf.co n p.1))⁻¹ * p.2 * (hT T U (hf.co n p.1)) *
            (hU T U (hf.co n p.1)) ∈
              S ∩ (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))}) := by
    funext y
    rw [atomShU_eq_map_conj hf n κ y,
      MeasureTheory.Measure.restrict_apply (s := Work.EKLContract.V hf.R ∩
        (U : Set Work.EKLContract.SL3)) (t := S) hS,
      MeasureTheory.Measure.map_apply (s := S ∩ (Work.EKLContract.V hf.R ∩
        (U : Set Work.EKLContract.SL3)))
        (f := fun u : Work.EKLContract.SL3 =>
          (hT T U (hf.co n y))⁻¹ * u * (hT T U (hf.co n y)) * (hU T U (hf.co n y)))
        (((measurable_const.mul measurable_id).mul measurable_const).mul measurable_const)
        hS'meas]
    congr 1
  rw [hgoal]
  exact hsec

end Work.EKLProd
