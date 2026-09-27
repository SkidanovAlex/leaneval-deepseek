import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.prodFlower_slice_avg
import Submission.Work.EKLProd.slicing_identity_gen
import Submission.Work.EKLProd.atomUnion_measurable
import Submission.Work.EKLProd.hU_co_constant_on_atom

/-!
# `Work.EKLProd.prodFlower_T_slice`

The `T`-side slicing of C5b: the tower identity `Work.EKLProd.slicing_identity_gen`
(Pisa Lemma 8.10) for the pair `(mH n, mT n)` of a product-box flower, tested with the two
*fixed* Borel test functions

* `f := 1_A ∘ (hT T U ∘ co n)` (the `T`-part of the plaque coordinate),
* `g := 1_B ∘ (hU T U ∘ co n)` (the `U`-part),

after the `νT`-slice average of `f` has been shown fibre-independent by
`Work.EKLProd.prodFlower_slice_avg`.

The one point that is not immediate is that `g` is `mT n`-measurable: it is Borel and constant
on the `mT n`-atoms (which are the `T`-strips of the flower), and a Borel union of atoms of a
countably generated sub-`σ`-algebra of `borel X₃` is `mT n`-measurable.  Because all the
integrals live on `hf.Z n`, it is enough to use the `mT n`-measurable modification
`1_A ∘ (hT T U ∘ co n)` cut down to `hf.Z n` (see `measurable_mT_indicator_hU_co`).
-/

namespace Work.EKLProd

open MeasureTheory Work.EKLContract
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

/-- The indicator of a set, with value `1` on the set, is bounded by `1`. -/
private theorem abs_indicator_one_le_one {α : Type*} (s : Set α) (a : α) :
    |s.indicator (fun _ => (1 : ℝ)) a| ≤ 1 := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h]
    norm_num
  · rw [Set.indicator_of_notMem h]
    norm_num

/-- Measurability of `1_A ∘ φ` for a measurable `φ` and a measurable `A`. -/
private theorem measurable_indicator_one_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set β} (hs : MeasurableSet s) {φ : α → β} (hφ : Measurable φ) :
    Measurable (fun a => s.indicator (fun _ => (1 : ℝ)) (φ a)) :=
  (Measurable.indicator measurable_const hs).comp hφ

theorem prodFlower_T_slice (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) (n : ℕ) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) {A B : Set Work.EKLContract.SL3} (hA : MeasurableSet A) (hB : MeasurableSet B) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), (∫ h in Work.EKLContract.shape (hf.mH n) H x, A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) * B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x)) = (((νT x).map (fun g : Work.EKLContract.SL3 => g * (Work.EKLProd.hT T U (hf.co n x)))) (A ∩ (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3)))).toReal / (((νT x).map (fun g : Work.EKLContract.SL3 => g * (Work.EKLProd.hT T U (hf.co n x)))) (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3))).toReal * (∫ h in Work.EKLContract.shape (hf.mH n) H x, B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x)) := by
  haveI hPol : PolishSpace X3 := hX3.2.1
  classical
  -- ## Abbreviations
  let FA : X3 → ℝ := fun y => A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n y))
  let GB : X3 → ℝ := fun y => B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n y))
  let GB' : X3 → ℝ := fun y =>
    (hf.Z n ∩ {z : X3 | Work.EKLProd.hU T U (hf.co n z) ∈ B}).indicator (fun _ => (1 : ℝ)) y
  let CAx : X3 → ℝ := fun x =>
    (((νT x).map (fun g : SL3 => g * (Work.EKLProd.hT T U (hf.co n x))))
        (A ∩ (V hf.R ∩ (T : Set SL3)))).toReal
      / (((νT x).map (fun g : SL3 => g * (Work.EKLProd.hT T U (hf.co n x))))
        (V hf.R ∩ (T : Set SL3))).toReal
  show ∀ᵐ x ∂(μ.restrict (hf.Z n)),
    (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x))
      = CAx x * ∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)
  -- ## Measurability and boundedness of the three test functions
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hSm : MeasurableSet (hf.Z n ∩ {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B}) :=
    hZmeas.inter ((hf.meas_up n) hB)
  have hFA_meas : Measurable FA := measurable_indicator_one_comp hA (hf.meas_tp n)
  have hFA_bdd : ∃ C, ∀ y, |FA y| ≤ C := by
    refine ⟨1, fun y => ?_⟩
    show |(A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n y)))| ≤ 1
    exact abs_indicator_one_le_one _ _
  have hGB'_meas : Measurable GB' := Measurable.indicator measurable_const hSm
  -- `GB'` is `mT n`-measurable: it is the indicator of a Borel, atom-saturated set.
  have hS_mT : @MeasurableSet X3 (hf.mT n)
      (hf.Z n ∩ {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B}) := by
    have hcg : @MeasurableSpace.CountablyGenerated X3 (hf.mT n) :=
      @MeasurableSpace.CountablyGenerated.mk X3 (hf.mT n) (hf.plaqT n).2.1
    have hgen : ∃ b : ℕ → Set X3, hf.mT n = MeasurableSpace.generateFrom (Set.range b) :=
      ⟨@MeasurableSpace.natGeneratingSequence X3 (hf.mT n) hcg,
       (@MeasurableSpace.generateFrom_natGeneratingSequence X3 (hf.mT n) hcg).symm⟩
    refine atomUnion_measurable (m := hf.mT n) (hf.plaqT n).1 hgen hSm ?_
    intro y hy z hz
    have hyZ : y ∈ hf.Z n := hy.1
    refine ⟨((hf.plaqT n).2.2.2 y hyZ).1 hz, ?_⟩
    show Work.EKLProd.hU T U (hf.co n z) ∈ B
    rw [hU_co_constant_on_atom hTH hUH hcop hdisj hf n hyZ hz]
    exact hy.2
  have hGB'_measT : @Measurable X3 ℝ (hf.mT n) (borel ℝ) GB' :=
    Measurable.indicator (f := fun _ => (1 : ℝ)) (m := hf.mT n) (mβ := borel ℝ)
      measurable_const hS_mT
  have hGB'_bdd : ∃ C, ∀ y, |GB' y| ≤ C := by
    refine ⟨1, fun y => ?_⟩
    show |(hf.Z n ∩ {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B}).indicator
      (fun _ => (1 : ℝ)) y| ≤ 1
    exact abs_indicator_one_le_one _ _
  -- ## The tower identity (Pisa Lemma 8.10) and the fibre-independence of the slice average
  have htower := slicing_identity_gen (μ := μ) hνH hνT (hf.mH n) (hf.mT n) (hf.plaqH n)
    (hf.plaqT n) (hf.alignT n) (prodFlower_shape_mass hf hνH n) FA GB'
    hFA_meas hFA_bdd hGB'_meas hGB'_measT hGB'_bdd
  have hslice := prodFlower_slice_avg hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj hf hνH hνT
    n t hcent hcontr hA
  filter_upwards [htower, hslice, prodFlower_shape_mass hf hνH n,
    MeasureTheory.ae_restrict_mem hZmeas] with x htow hsli hmass hxZ
  -- ## The shape of `mH n` is a measurable set of group elements
  have hShmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]
    exact hOo.measurableSet.inter hH.1.measurableSet
  have hM0 : ((νH x) (shape (hf.mH n) H x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hmass.1.ne' (ne_of_lt hmass.2))
  -- ## On the shape, the cut-down `U`-indicator agrees with the original one
  have hagree : ∀ h ∈ shape (hf.mH n) H x, GB' (h • x) = GB (h • x) := by
    intro h hh
    have hz : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hh.2
    show (hf.Z n ∩ {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B}).indicator
        (fun _ => (1 : ℝ)) (h • x)
      = B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x)))
    by_cases hb : Work.EKLProd.hU T U (hf.co n (h • x)) ∈ B
    · rw [Set.indicator_of_mem (show h • x ∈ hf.Z n ∩
          {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B} from ⟨hz, hb⟩),
        Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem (show h • x ∉ hf.Z n ∩
          {y : X3 | Work.EKLProd.hU T U (hf.co n y) ∈ B} from fun hmem => hb hmem.2),
        Set.indicator_of_notMem hb]
  -- ## The slice average is the constant `CAx x`
  have hsliceFA : ∀ᵐ h ∂(νH x).restrict (shape (hf.mH n) H x),
      (∫ t in shape (hf.mT n) T (h • x), FA (t • (h • x)) ∂(νT (h • x)))
        / ((νT (h • x)) (shape (hf.mT n) T (h • x))).toReal = CAx x :=
    hsli.mono (fun _ hh => hh)
  have hptGB : ∀ᵐ h ∂(νH x).restrict (shape (hf.mH n) H x), GB' (h • x) = GB (h • x) :=
    (MeasureTheory.ae_restrict_iff' hShmeas).mpr (Filter.Eventually.of_forall hagree)
  have hptL : ∀ᵐ h ∂(νH x).restrict (shape (hf.mH n) H x),
      GB' (h • x) * FA (h • x) = FA (h • x) * GB (h • x) := by
    rw [MeasureTheory.ae_restrict_iff' hShmeas]
    exact Filter.Eventually.of_forall (fun h hh => by
      show GB' (h • x) * FA (h • x) = FA (h • x) * GB (h • x)
      rw [hagree h hh, mul_comm])
  have hptR : ∀ᵐ h ∂(νH x).restrict (shape (hf.mH n) H x),
      GB' (h • x) * ((∫ t in shape (hf.mT n) T (h • x), FA (t • (h • x)) ∂(νT (h • x)))
          / ((νT (h • x)) (shape (hf.mT n) T (h • x))).toReal)
        = GB' (h • x) * CAx x :=
    hsliceFA.mono (fun h hh => congrArg (fun z : ℝ => GB' (h • x) * z) hh)
  have hGB'_eq : (∫ h in shape (hf.mH n) H x, GB' (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)) :=
    MeasureTheory.integral_congr_ae hptGB
  have hL : (∫ h in shape (hf.mH n) H x, GB' (h • x) * FA (h • x) ∂(νH x))
      = (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x)) :=
    MeasureTheory.integral_congr_ae hptL
  have hR : (∫ h in shape (hf.mH n) H x, GB' (h • x)
        * ((∫ t in shape (hf.mT n) T (h • x), FA (t • (h • x)) ∂(νT (h • x)))
            / ((νT (h • x)) (shape (hf.mT n) T (h • x))).toReal) ∂(νH x))
      = CAx x * (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)) := by
    calc (∫ h in shape (hf.mH n) H x, GB' (h • x)
          * ((∫ t in shape (hf.mT n) T (h • x), FA (t • (h • x)) ∂(νT (h • x)))
              / ((νT (h • x)) (shape (hf.mT n) T (h • x))).toReal) ∂(νH x))
        = (∫ h in shape (hf.mH n) H x, GB' (h • x) * CAx x ∂(νH x)) :=
          MeasureTheory.integral_congr_ae hptR
      _ = (∫ h in shape (hf.mH n) H x, GB' (h • x) ∂(νH x)) * CAx x :=
          MeasureTheory.integral_mul_const _ _
      _ = (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)) * CAx x := by rw [hGB'_eq]
      _ = CAx x * (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)) := mul_comm _ _
  -- ## Cancel the (nonzero) shape mass
  have hdiv : (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x))
        / ((νH x) (shape (hf.mH n) H x)).toReal
      = (CAx x * (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)))
        / ((νH x) (shape (hf.mH n) H x)).toReal := by
    rw [← hL, htow, hR]
  have hfin : (∫ h in shape (hf.mH n) H x, FA (h • x) * GB (h • x) ∂(νH x))
      = CAx x * (∫ h in shape (hf.mH n) H x, GB (h • x) ∂(νH x)) := by
    have h := (div_eq_div_iff hM0 hM0).mp hdiv
    exact mul_right_cancel₀ hM0 h
  exact hfin

end

end Work.EKLProd
