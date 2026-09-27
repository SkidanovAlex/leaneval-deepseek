import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.hT_atom_determines_mU

namespace Work.EKLRelProduct

theorem uAvg_factors_hT {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3}
    (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3}
    (hνU : Work.EKLContract.IsLeafwise μ U νU XU)
    {B : Set Work.EKLContract.SL3} (hB : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) B) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      ∃ G : Work.EKLContract.SL3 → ℝ, Measurable G ∧
        ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
          Work.EKLRelProduct.uAvg hf νU n (h • x) B = G (Work.EKLProd.hT T U (hf.co n (h • x))) := by
  classical
  -- ## The test function whose leafwise average is `uAvg`, and its conditional expectation
  set f : Work.EKLContract.X3 → ℝ :=
    fun y => B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n y)) with hf_def
  have hf_meas : @Measurable Work.EKLContract.X3 ℝ Work.EKLContract.instMeasurableSpaceX3 (borel ℝ) f := by
    rw [hf_def]
    exact (Measurable.indicator measurable_const hB).comp (hf.meas_up n)
  have hf_bdd : ∃ C, ∀ y, |f y| ≤ C := by
    refine ⟨1, fun y => ?_⟩
    simp only [hf_def]
    by_cases hy : Work.EKLProd.hU T U (hf.co n y) ∈ B
    · rw [Set.indicator_of_mem hy]; norm_num
    · rw [Set.indicator_of_notMem hy]; norm_num
  set F : Work.EKLContract.X3 → ℝ :=
    MeasureTheory.condExp (hf.mU n) (μ.restrict (hf.Z n)) f with hF_def
  have hF_mU : @Measurable Work.EKLContract.X3 ℝ (hf.mU n) (borel ℝ) F := by
    rw [hF_def]
    exact (MeasureTheory.stronglyMeasurable_condExp
      (μ := μ.restrict (hf.Z n)) (m := hf.mU n) (f := f)).measurable
  have hF_borel :
      @Measurable Work.EKLContract.X3 ℝ Work.EKLContract.instMeasurableSpaceX3 (borel ℝ) F :=
    hF_mU.mono (hf.plaqU n).1 le_rfl
  -- ## `uAvg` agrees with `F` almost everywhere: the `condexp` axiom of the `U`-leafwise system
  have hae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), Work.EKLRelProduct.uAvg hf νU n x B = F x := by
    have h := hνU.condexp (hf.Z n) (hf.mU n) (hf.plaqU n) f hf_meas hf_bdd
    filter_upwards [h] with x hx
    rw [hF_def, hx]
    simp only [Work.EKLRelProduct.uAvg, hf_def]
  -- ## The exceptional set and its transfer to the `H`-leafwise slices
  set N : Set Work.EKLContract.X3 :=
    {y | Work.EKLRelProduct.uAvg hf νU n y B ≠ F y} with hN_def
  have hNnull : (μ.restrict (hf.Z n)) N = 0 := by
    rw [hN_def]
    exact MeasureTheory.ae_iff.mp hae
  have hNT : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      νH x {u | u ∈ Work.EKLContract.shape (hf.mH n) H x ∧ u • x ∈ N} = 0 :=
    Work.EKLProd.leafwise_null_transfer_gen (μ := μ) (U := H) (ν := νH) (X' := XH) hνH
      (Z := hf.Z n) (m := hf.mH n) (hf.plaqH n)
      (Work.EKLProd.prodFlower_shape_mass hf hνH n) (N := N) hNnull
  have hXH_ae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XH :=
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.ae_iff.mpr hνH.conull)
  have hZmeas : MeasurableSet (hf.Z n) :=
    (MeasurableSpace.le_def.mp (hf.plaqH n).1) (hf.Z n) (hf.plaqH n).2.2.1
  have hZ_ae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ hf.Z n :=
    MeasureTheory.ae_restrict_mem hZmeas
  filter_upwards [hNT, hXH_ae, hZ_ae] with x hNTx hXHx hZx
  -- ## The measurable function `G` at the base point `x`
  refine ⟨fun w : Work.EKLContract.SL3 => F ((w * (hf.co n x)⁻¹) • x), ?_, ?_⟩
  · exact hF_borel.comp (((continuous_id.mul continuous_const).smul continuous_const).measurable)
  · -- `shape (mH n) H x` is null-measurable for `νH x` (it is `O ∩ H` up to a null set)
    have hHnull : (νH x) ((H : Set Work.EKLContract.SL3)ᶜ) = 0 := hνH.carried x hXHx
    obtain ⟨O, hO, hOeq⟩ := ((hf.plaqH n).2.2.2 x hZx).2.2.1
    have hHnm : MeasureTheory.NullMeasurableSet (H : Set Work.EKLContract.SL3) (νH x) := by
      simpa using (MeasureTheory.NullMeasurableSet.of_null hHnull).compl
    have hSep : MeasureTheory.NullMeasurableSet (Work.EKLContract.shape (hf.mH n) H x) (νH x) := by
      rw [hOeq]
      exact (hO.measurableSet.nullMeasurableSet).inter hHnm
    have hbad : ∀ᵐ h ∂(νH x), h ∈ Work.EKLContract.shape (hf.mH n) H x → h • x ∉ N := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_ hNTx
      intro h hmem
      exact ⟨by by_contra hc; exact hmem (fun hh => absurd hh hc),
        by by_contra hc; exact hmem (fun _ => hc)⟩
    rw [MeasureTheory.ae_restrict_iff'₀ hSep]
    filter_upwards [hbad] with h hh
    intro hS
    have hNnot : h • x ∉ N := hh hS
    have hy_eq : Work.EKLRelProduct.uAvg hf νU n (h • x) B = F (h • x) := by
      by_contra hc
      exact hNnot (by rw [hN_def]; exact hc)
    rw [hy_eq]
    show F (h • x) = F ((Work.EKLProd.hT T U (hf.co n (h • x)) * (hf.co n x)⁻¹) • x)
    -- ## Algebraic facts about the point `a = hT(co(h•x)) * (co x)⁻¹`
    have hy_atom : h • x ∈ Work.EKLContract.atom (hf.mH n) x := hS.2
    have hyZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hZx).1 hS.2
    obtain ⟨t₀, ht₀, u₀, hu₀, ht₀u₀⟩ := hf.co_mem n (h • x) hyZ
    have hcoH : hf.co n (h • x) ∈ (H : Set Work.EKLContract.SL3) :=
      Work.EKLProd.prodBox_subset_H hTH hUH (hf.co_mem n (h • x) hyZ)
    have ht_eq : Work.EKLProd.hT T U (hf.co n (h • x)) = t₀ :=
      Work.EKLProd.hT_eq_of_factor hcop hdisj hcoH ht₀.2 hu₀.2 ht₀u₀
    have htT : Work.EKLProd.hT T U (hf.co n (h • x)) ∈ T :=
      Work.EKLProd.hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
    have htV : Work.EKLProd.hT T U (hf.co n (h • x)) ∈ Work.EKLContract.V hf.R := by
      rw [ht_eq]; exact ht₀.1
    have hRpos : (0 : ℝ) < hf.R := lt_of_lt_of_le zero_lt_one hf.one_le_R
    have honeV : (1 : Work.EKLContract.SL3) ∈ Work.EKLContract.V hf.R := by
      simp only [Work.EKLContract.V, Set.mem_ofPred_eq]
      intro i j
      have hz : |(1 : Work.EKLContract.SL3) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| = 0 := by
        simp [Matrix.SpecialLinearGroup.coe_one]
      rw [hz]
      exact hRpos
    have hone : (1 : Work.EKLContract.SL3)
        ∈ Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3) := ⟨honeV, U.one_mem⟩
    have ht_prod : Work.EKLProd.hT T U (hf.co n (h • x))
        ∈ Work.EKLProd.prodBox T U hf.R :=
      ⟨_, ⟨htV, htT⟩, 1, hone, mul_one _⟩
    set a : Work.EKLContract.SL3 :=
      Work.EKLProd.hT T U (hf.co n (h • x)) * (hf.co n x)⁻¹ with ha_def
    have ha_H : a ∈ H := by
      rw [ha_def]
      exact H.mul_mem (hTH htT)
        (H.inv_mem (Work.EKLProd.prodBox_subset_H hTH hUH (hf.co_mem n x hZx)))
    have ha_cox : a * hf.co n x = Work.EKLProd.hT T U (hf.co n (h • x)) := by
      rw [ha_def]; group
    have ha_shape : a ∈ Work.EKLContract.shape (hf.mH n) H x := by
      rw [hf.shapeH n x hZx]
      exact ⟨ha_H, by rw [ha_cox]; exact ht_prod⟩
    have ha_atom : a • x ∈ Work.EKLContract.atom (hf.mH n) x := ha_shape.2
    have hTid : Work.EKLProd.hT T U (Work.EKLProd.hT T U (hf.co n (h • x)))
        = Work.EKLProd.hT T U (hf.co n (h • x)) :=
      Work.EKLProd.hT_eq_of_factor hcop hdisj (hTH htT) htT U.one_mem (mul_one _)
    have ha_t : Work.EKLProd.hT T U (hf.co n (h • x))
        = Work.EKLProd.hT T U (hf.co n (a • x)) := by
      have hco_a : hf.co n (a • x) = a * hf.co n x := hf.co_smul n x hZx a ha_H ha_atom
      rw [hco_a, ha_cox]
      exact hTid.symm
    have hatomU : a • x ∈ Work.EKLContract.atom (hf.mU n) (h • x) :=
      hT_atom_determines_mU hTH hUH hnorm hcop hdisj hf n hZx hy_atom ha_atom ha_t
    -- ## `F` is constant on the `mU n`-atoms
    have hF_const : ∀ {z z' : Work.EKLContract.X3},
        z' ∈ Work.EKLContract.atom (hf.mU n) z → F z' = F z := by
      intro z z' hz
      have hmeas : @MeasurableSet Work.EKLContract.X3 (hf.mU n) (F ⁻¹' {F z}) :=
        hF_mU (measurableSet_singleton (F z))
      have hzmem : z ∈ F ⁻¹' {F z} := rfl
      have hsub : Work.EKLContract.atom (hf.mU n) z ⊆ F ⁻¹' {F z} :=
        Set.sInter_subset_of_mem
          (show F ⁻¹' {F z} ∈ {s | @MeasurableSet Work.EKLContract.X3 (hf.mU n) s ∧ z ∈ s} from
            ⟨hmeas, hzmem⟩)
      exact hsub hz
    exact (hF_const hatomU).symm

end Work.EKLRelProduct
