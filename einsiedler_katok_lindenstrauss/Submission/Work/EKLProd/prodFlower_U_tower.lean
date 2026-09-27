import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.prodFlower_slice_avg
import Submission.Work.EKLProd.slicing_identity_gen
import Submission.Work.EKLProd.atomUnion_measurable
import Submission.Work.EKLComp.flower_piece_borel
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable

/-!
# `Work.EKLProd.prodFlower_U_tower`

The **`U`-side tower identity** of C5b: the slicing identity of Pisa Lemma 8.10
(`Work.EKLProd.slicing_identity_gen`) for the pair of *aligned* plaque algebras `(mH n, mU n)` of a
product-box flower, tested with

* `f := 1_B ∘ (hU T U ∘ co n)` (the `U`-part of the plaque coordinate),
* `g := 1_A ∘ (hT T U ∘ co n)` (the `T`-part),

cut down to the flower domain `Z n`.  Unlike the `T`-side (`Work.EKLProd.prodFlower_T_slice`,
where the `νT`-slice average is replaced by a *constant* via the fibre-independence
`Work.EKLProd.prodFlower_slice_avg`), no fibre-independence is needed here: the conclusion keeps
the `νU`-slice average of `f` inside the `νH x`-integral.

The one point that is not a direct instantiation is the measurability hypothesis of the tower
identity: the test function `g = 1_A ∘ (hT T U ∘ co n)` must be `mU n`-measurable, i.e. constant
on the `U`-strips of the flower.  This is the `T`-part analogue of
`Work.EKLProd.hU_co_constant_on_atom`: the `U`-strip of `x ∈ Z n` is an orbit `(U-shape) • x`, along
which the coordinate changes by left multiplication by a `U`-element, and the `T`-part of a
`U`-left-multiple coincides with the `T`-part of the coordinate
(`Work.EKLProd.hT_mul_right_U`).
-/

namespace Work.EKLProd

open MeasureTheory Work.EKLContract
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## Helpers -/

/-- The indicator (of value `1`) of a set is bounded by `1`. -/
private theorem abs_indicator_one_le_one {α : Type*} (s : Set α) (a : α) :
    |s.indicator (fun _ => (1 : ℝ)) a| ≤ 1 := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

/-- **The `T`-part of the coordinate is constant on the atoms of the `U`-strip algebra**: the
`U`-atom of a point `x ∈ Z n` is the orbit `(U-shape) • x`, along which the coordinate changes by
left multiplication with a `U`-element, and the `T`-part of a `U`-left-multiple coincides with the
`T`-part of the coordinate (`Work.EKLProd.hT_mul_right_U`). -/
theorem hT_co_constant_on_atom {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ)
    (n : ℕ) {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) {y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom (hf.mU n) x) :
    Work.EKLProd.hT T U (hf.co n y) = Work.EKLProd.hT T U (hf.co n x) := by
  have hsub : atom (hf.mU n) x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) :=
    ((hf.plaqU n).2.2.2 x hx).2.1
  obtain ⟨u, huU, hux⟩ := hsub hy
  have hux' : u • x = y := hux
  have huH : u ∈ H := hUH huU
  have huxH : u • x ∈ atom (hf.mH n) x := by
    rw [hux']
    exact atom_subset (hf.alignU n) x hy
  have hco : hf.co n y = u * hf.co n x := by
    rw [← hux']
    exact hf.co_smul n x hx u huH huxH
  rw [hco]
  exact hT_mul_right_U hnorm hcop hdisj hUH huU
    (prodBox_subset_H hTH hUH (hf.co_mem n x hx))

/-- The Borel set `Z n ∩ {y | hT T U (co n y) ∈ A}` is a union of `mU n`-atoms, hence
`mU n`-measurable; consequently its indicator (the cut-down `T`-part test function) is
`mU n`-measurable. -/
theorem measurable_mU_indicator_hT_co [PolishSpace Work.EKLContract.X3]
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {A : Set Work.EKLContract.SL3}
    (hA : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) A) :
    @Measurable Work.EKLContract.X3 ℝ (hf.mU n) (borel ℝ)
      ((hf.Z n ∩ {y : Work.EKLContract.X3 | Work.EKLProd.hT T U (hf.co n y) ∈ A}).indicator
        (fun _ => (1 : ℝ))) := by
  obtain ⟨hm_le, ⟨b, hbc, hbm⟩, hZmeas, hatom⟩ := hf.plaqU n
  set S : Set Work.EKLContract.X3 :=
    hf.Z n ∩ {y : Work.EKLContract.X3 | Work.EKLProd.hT T U (hf.co n y) ∈ A} with hSdef
  -- ## `S` is Borel
  have hZ_borel : @MeasurableSet Work.EKLContract.X3 (borel Work.EKLContract.X3) (hf.Z n) :=
    MeasurableSpace.le_def.mp hm_le (hf.Z n) hZmeas
  have hA_borel : @MeasurableSet Work.EKLContract.X3 (borel Work.EKLContract.X3)
      {y : Work.EKLContract.X3 | Work.EKLProd.hT T U (hf.co n y) ∈ A} :=
    hf.meas_tp n hA
  have hS_borel : @MeasurableSet Work.EKLContract.X3 (borel Work.EKLContract.X3) S := by
    rw [hSdef]
    exact hZ_borel.inter hA_borel
  -- ## `S` is a union of `mU n`-atoms
  have hsat : ∀ x ∈ S, Work.EKLContract.atom (hf.mU n) x ⊆ S := by
    intro x hx y hy
    rw [hSdef] at hx ⊢
    refine ⟨(hatom x hx.1).1 hy, ?_⟩
    show Work.EKLProd.hT T U (hf.co n y) ∈ A
    rw [Work.EKLProd.hT_co_constant_on_atom hTH hUH hnorm hcop hdisj hf n hx.1 hy]
    simpa using hx.2
  have hgen : @MeasurableSpace.CountablyGenerated Work.EKLContract.X3 (hf.mU n) := by
    letI : MeasurableSpace Work.EKLContract.X3 := hf.mU n
    exact ⟨b, hbc, hbm⟩
  have hS : @MeasurableSet Work.EKLContract.X3 (hf.mU n) S :=
    Work.EKLC6Core.borel_atom_saturated_measurable (m := hf.mU n) hm_le hgen hS_borel hsat
  exact @Measurable.indicator Work.EKLContract.X3 ℝ S (fun _ => (1 : ℝ)) (hf.mU n) (borel ℝ)
    (inferInstance : Zero ℝ)
    (@measurable_const ℝ Work.EKLContract.X3 (borel ℝ) (hf.mU n) (1 : ℝ)) hS

/-! ## The main theorem -/

theorem prodFlower_U_tower (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) (n : ℕ) {A B : Set Work.EKLContract.SL3} (hA : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) A) (hB : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) B) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), (∫ h in Work.EKLContract.shape (hf.mH n) H x, A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) * B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x)) = (∫ h in Work.EKLContract.shape (hf.mH n) H x, A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) * ((∫ u in Work.EKLContract.shape (hf.mU n) U (h • x), B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (u • (h • x)))) ∂(νU (h • x))) / ((νU (h • x)) (Work.EKLContract.shape (hf.mU n) U (h • x))).toReal) ∂(νH x)) := by
  haveI hPol : PolishSpace X3 := hX3.2.1
  classical
  -- ## The three test functions
  let FA : X3 → ℝ := fun y =>
    A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n y))
  let GB : X3 → ℝ := fun y =>
    B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n y))
  -- the `T`-part test function cut down to the flower domain, which is `mU n`-measurable
  let FA' : X3 → ℝ := fun y =>
    (hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}).indicator
      (fun _ => (1 : ℝ)) y
  -- the `mU n`-slice average of the `U`-part test function
  let Ug : X3 → ℝ := fun y =>
    (∫ u in shape (hf.mU n) U y, GB (u • y) ∂(νU y))
      / ((νU y) (shape (hf.mU n) U y)).toReal
  show ∀ᵐ x ∂(μ.restrict (hf.Z n)),
    (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, FA (h • x) * Ug (h • x) ∂(νH x))
  -- ## Measurability and boundedness
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hSm : MeasurableSet (hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}) :=
    hZmeas.inter ((hf.meas_tp n) hA)
  have hFA_meas : Measurable FA := by
    show Measurable ((fun a : SL3 => A.indicator (fun _ => (1 : ℝ)) a)
      ∘ (fun y : X3 => Work.EKLProd.hT T U (hf.co n y)))
    exact (Measurable.indicator measurable_const hA).comp (hf.meas_tp n)
  have hGB_meas : Measurable GB := by
    show Measurable ((fun a : SL3 => B.indicator (fun _ => (1 : ℝ)) a)
      ∘ (fun y : X3 => Work.EKLProd.hU T U (hf.co n y)))
    exact (Measurable.indicator measurable_const hB).comp (hf.meas_up n)
  have hFA_bdd : ∃ C, ∀ y, |FA y| ≤ C := ⟨1, fun y => by
    show |A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n y))| ≤ 1
    exact abs_indicator_one_le_one _ _⟩
  have hGB_bdd : ∃ C, ∀ y, |GB y| ≤ C := ⟨1, fun y => by
    show |B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n y))| ≤ 1
    exact abs_indicator_one_le_one _ _⟩
  have hFA'_meas : Measurable FA' := by
    show Measurable ((hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}).indicator
      (fun _ => (1 : ℝ)))
    exact Measurable.indicator measurable_const hSm
  have hFA'_bdd : ∃ C, ∀ y, |FA' y| ≤ C := ⟨1, fun y => by
    show |(hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}).indicator
      (fun _ => (1 : ℝ)) y| ≤ 1
    exact abs_indicator_one_le_one _ _⟩
  have hFA'_measU : @Measurable X3 ℝ (hf.mU n) (borel ℝ) FA' := by
    show @Measurable X3 ℝ (hf.mU n) (borel ℝ)
      ((hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}).indicator
        (fun _ => (1 : ℝ)))
    exact measurable_mU_indicator_hT_co hTH hUH hnorm hcop hdisj hf n hA
  -- ## The tower identity of Pisa Lemma 8.10 for the aligned pair `(mH n, mU n)`
  have htower := slicing_identity_gen (μ := μ) hνH hνU (hf.mH n) (hf.mU n) (hf.plaqH n)
    (hf.plaqU n) (hf.alignU n) (prodFlower_shape_mass hf hνH n) GB FA'
    hGB_meas hGB_bdd hFA'_meas hFA'_measU hFA'_bdd
  filter_upwards [htower, prodFlower_shape_mass hf hνH n, MeasureTheory.ae_restrict_mem hZmeas]
    with x htow hmass hxZ
  -- ## The shape of `mH n` at `x` is a measurable set of group elements
  have hShmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]
    exact hOo.measurableSet.inter hH.1.measurableSet
  have hM0 : ((νH x) (shape (hf.mH n) H x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hmass.1.ne' (ne_of_lt hmass.2))
  -- ## On the shape, the cut-down `T`-part test function agrees with `FA`
  have hagree : ∀ h ∈ shape (hf.mH n) H x, FA' (h • x) = FA (h • x) := by
    intro h hh
    have hz : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hh.2
    show (hf.Z n ∩ {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A}).indicator
        (fun _ => (1 : ℝ)) (h • x)
      = A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
    by_cases hb : Work.EKLProd.hT T U (hf.co n (h • x)) ∈ A
    · rw [Set.indicator_of_mem (show h • x ∈ hf.Z n ∩
          {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A} from ⟨hz, hb⟩),
        Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem (show h • x ∉ hf.Z n ∩
          {z : X3 | Work.EKLProd.hT T U (hf.co n z) ∈ A} from fun hmem => hb hmem.2),
        Set.indicator_of_notMem hb]
  have h1 : (∫ h in shape (hf.mH n) H x, FA' (h • x) * GB (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x)) :=
    MeasureTheory.setIntegral_congr_fun hShmeas
      (fun h hh => congrArg (fun z : ℝ => z * GB (h • x)) (hagree h hh))
  have h2 : (∫ h in shape (hf.mH n) H x, FA' (h • x) * Ug (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, FA (h • x) * Ug (h • x) ∂(νH x)) :=
    MeasureTheory.setIntegral_congr_fun hShmeas
      (fun h hh => congrArg (fun z : ℝ => z * Ug (h • x)) (hagree h hh))
  -- ## Cancel the (non-zero) shape mass
  have h3 : (∫ h in shape (hf.mH n) H x, FA' (h • x) * GB (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, FA' (h • x) * Ug (h • x) ∂(νH x)) :=
    mul_right_cancel₀ hM0 ((div_eq_div_iff hM0 hM0).mp htow)
  rw [h1, h2] at h3
  exact h3

end

end Work.EKLProd
