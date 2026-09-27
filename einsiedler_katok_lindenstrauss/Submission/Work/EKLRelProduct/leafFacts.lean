import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLC6Core.shape_mass_pos

namespace Work.EKLRelProduct

open MeasureTheory Work.EKLContract Work.EKLProd

set_option linter.unusedVariables false

/-- The source set `S_T` of the `T`-factor is the `T`-shape of the `T`-strip algebra: both are
the set of `T`-directions `g` with `g * hT T U (co n z) ∈ V R ∩ T`. -/
lemma S_T_eq_shape_of_mem_Z {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {z : X3} (hz : z ∈ hf.Z n) :
    S_T hf n z = shape (hf.mT n) T z := by
  rw [Work.EKLProd.prodFlower_shapeT_eq hTH hUH hcop hdisj hf n hz]
  unfold S_T
  rw [Set.image_mul_right]
  simp only [inv_inv]
  rfl


theorem leafFacts {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff)
    (hHoroH : Work.EKLContract.IsHoro H) (hHoroT : Work.EKLContract.IsHoro T) (hHoroU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hmu : Work.EKLContract.IsAInvariant μ) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      (h • x ∈ XH ∧ h • x ∈ XT ∧ h • x ∈ XU) ∧
      (0 < (νT (h • x)) (Work.EKLRelProduct.S_T hf n (h • x)) ∧ (νT (h • x)) (Work.EKLRelProduct.S_T hf n (h • x)) < ⊤) ∧
      (0 < (νH (h • x)) (Work.EKLContract.shape (hf.mH n) H (h • x)) ∧
        (νH (h • x)) (Work.EKLContract.shape (hf.mH n) H (h • x)) < ⊤)  := by
  -- ## The shape mass of the `H`-plaque is finite and positive a.e.
  have hmass := Work.EKLProd.prodFlower_shape_mass hf hνH n
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  -- ## The three co-null domains have zero measure for the restricted measure
  have hnullH : (μ.restrict (hf.Z n)) XHᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hνH.meas_dom.compl]
    exact measure_mono_null Set.inter_subset_left hνH.conull
  have hnullT : (μ.restrict (hf.Z n)) XTᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hνT.meas_dom.compl]
    exact measure_mono_null Set.inter_subset_left hνT.conull
  have hnullU : (μ.restrict (hf.Z n)) XUᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hνU.meas_dom.compl]
    exact measure_mono_null Set.inter_subset_left hνU.conull
  -- ## Leafwise null transfer: `νH` with the plaque algebra `mH n` of the `n`-th flower
  have h1 := Work.EKLProd.leafwise_null_transfer_gen hνH (hf.plaqH n) hmass hnullH
  have h2 := Work.EKLProd.leafwise_null_transfer_gen hνH (hf.plaqH n) hmass hnullT
  have h3 := Work.EKLProd.leafwise_null_transfer_gen hνH (hf.plaqH n) hmass hnullU
  filter_upwards [hmass, h1, h2, h3, MeasureTheory.ae_restrict_mem hZmeas]
    with x hmassx h1x h2x h3x hxZ
  -- ## The shape is measurable, so the a.e. statement over it is a statement over `νH x`
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOopen, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]
    exact hOopen.measurableSet.inter hHoroH.1.measurableSet
  rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
  -- ## Only the three translate-null sets can prevent the conclusions
  refine measure_mono_null ?_ (measure_union_null (measure_union_null h1x h2x) h3x)
  intro h hh
  obtain ⟨hhs, hhQ⟩ := Classical.not_imp.mp hh
  have hxZ' : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hhs.2
  rcases em (h • x ∈ XH) with hXH | hXH
  · rcases em (h • x ∈ XT) with hXT | hXT
    · rcases em (h • x ∈ XU) with hXU | hXU
      · -- the three memberships hold: the two shape masses are finite and positive
        exfalso
        refine hhQ ⟨⟨hXH, hXT, hXU⟩, ?_, ?_⟩
        · have hST : S_T hf n (h • x) = shape (hf.mT n) T (h • x) :=
            S_T_eq_shape_of_mem_Z hTH hUH hcop hdisj hf n hxZ'
          rw [hST]
          exact Work.EKLC6Core.shape_mass_pos hνT (hf.plaqT n) hXT hxZ'
        · exact Work.EKLC6Core.shape_mass_pos hνH (hf.plaqH n) hXH hxZ'
      · exact Or.inr ⟨hhs, hXU⟩
    · exact Or.inl (Or.inr ⟨hhs, hXT⟩)
  · exact Or.inl (Or.inl ⟨hhs, hXH⟩)

end Work.EKLRelProduct
