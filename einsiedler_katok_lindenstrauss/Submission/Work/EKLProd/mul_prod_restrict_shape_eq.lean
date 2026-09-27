import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.locStruct
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLRelProduct.uAvg_eq

namespace Work.EKLProd

open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- Auxiliary: the two restricted measures `(νT x ⊗ νU x)|_{mul⁻¹ shape}` and
`(νT x ⊗ νU x)|_{S_T ×ˢ S_U}` coincide. -/
lemma restrict_mul_preimage_eq {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : Work.EKLContract.X3} (hxZ : x ∈ hf.Z n)
    [MeasureTheory.SFinite (νU x)]
    (hcarT : (νT x) (T : Set Work.EKLContract.SL3)ᶜ = 0)
    (hcarU : (νU x) (U : Set Work.EKLContract.SL3)ᶜ = 0) :
    (((νT x).prod (νU x)).restrict
        ((fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2) ⁻¹'
          Work.EKLContract.shape (hf.mH n) H x))
      = ((νT x).prod (νU x)).restrict
          (Work.EKLRelProduct.S_T hf n x ×ˢ Work.EKLRelProduct.S_U hf n x) := by
  have hMD : (νT x).prod (νU x)
      (((T : Set Work.EKLContract.SL3) ×ˢ (U : Set Work.EKLContract.SL3))ᶜ) = 0 := by
    rw [Set.compl_prod_eq_union]
    refine le_antisymm ?_ bot_le
    calc (νT x).prod (νU x)
            (((T : Set Work.EKLContract.SL3)ᶜ ×ˢ (Set.univ : Set Work.EKLContract.SL3)) ∪
              ((Set.univ : Set Work.EKLContract.SL3) ×ˢ (U : Set Work.EKLContract.SL3)ᶜ))
        ≤ (νT x).prod (νU x)
            ((T : Set Work.EKLContract.SL3)ᶜ ×ˢ (Set.univ : Set Work.EKLContract.SL3))
          + (νT x).prod (νU x)
            ((Set.univ : Set Work.EKLContract.SL3) ×ˢ (U : Set Work.EKLContract.SL3)ᶜ) :=
          MeasureTheory.measure_union_le _ _
      _ ≤ (νT x) (T : Set Work.EKLContract.SL3)ᶜ * (νU x) (Set.univ : Set Work.EKLContract.SL3)
          + (νT x) (Set.univ : Set Work.EKLContract.SL3) * (νU x) (U : Set Work.EKLContract.SL3)ᶜ :=
          add_le_add (MeasureTheory.Measure.prod_prod_le _ _)
            (MeasureTheory.Measure.prod_prod_le _ _)
      _ = 0 := by rw [hcarT, hcarU]; simp
  apply MeasureTheory.Measure.restrict_congr_set
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.measure_mono_null ?_ hMD
    intro p hp
    rw [Set.mem_sdiff, Set.mem_preimage, Set.mem_prod] at hp
    obtain ⟨hpA, hpB⟩ := hp
    rw [Set.mem_compl_iff, Set.mem_prod]
    rintro ⟨hp1T, hp2U⟩
    exact hpB ((Work.EKLRelProduct.mem_shape_iff_factor hTH hUH hnorm hcop hdisj hf n hxZ
      p.1 hp1T p.2 hp2U).mp hpA)
  · refine MeasureTheory.measure_mono_null ?_ hMD
    intro p hp
    rw [Set.mem_sdiff, Set.mem_preimage, Set.mem_prod] at hp
    obtain ⟨hpB, hpA⟩ := hp
    rw [Set.mem_compl_iff, Set.mem_prod]
    rintro ⟨hp1T, hp2U⟩
    exact hpA ((Work.EKLRelProduct.mem_shape_iff_factor hTH hUH hnorm hcop hdisj hf n hxZ
      p.1 hp1T p.2 hp2U).mpr hpB)

theorem mul_prod_restrict_shape_eq {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : Work.EKLContract.X3} (hxZ : x ∈ hf.Z n)
    (hfinT : MeasureTheory.IsFiniteMeasureOnCompacts (νT x))
    (hfinU : MeasureTheory.IsFiniteMeasureOnCompacts (νU x))
    (hcarT : (νT x) (T : Set Work.EKLContract.SL3)ᶜ = 0)
    (hcarU : (νU x) (U : Set Work.EKLContract.SL3)ᶜ = 0) :
    (((νT x).prod (νU x)).map
        (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2)).restrict
      (Work.EKLContract.shape (hf.mH n) H x)
    = (((νT x).restrict (Work.EKLRelProduct.S_T hf n x)).prod
        ((νU x).restrict (Work.EKLRelProduct.S_U hf n x))).map
      (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2) := by
  haveI hfinT' : MeasureTheory.IsFiniteMeasureOnCompacts (νT x) := hfinT
  haveI hfinU' : MeasureTheory.IsFiniteMeasureOnCompacts (νU x) := hfinU
  haveI hsigT : MeasureTheory.SigmaFinite (νT x) :=
    MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts (νT x)
  haveI hsigU : MeasureTheory.SigmaFinite (νU x) :=
    MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts (νU x)
  have hmul_meas : Measurable
      (fun p : Work.EKLContract.SL3 × Work.EKLContract.SL3 => p.1 * p.2) :=
    continuous_mul.measurable
  have hshmeas : MeasurableSet (Work.EKLContract.shape (hf.mH n) H x) := by
    obtain ⟨O, hO, hEq⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hEq]
    exact hO.measurableSet.inter hHc.measurableSet
  rw [Work.EKLRelProduct.measure_map_restrict _ hmul_meas hshmeas]
  rw [MeasureTheory.Measure.prod_restrict]
  rw [restrict_mul_preimage_eq hTH hUH hnorm hcop hdisj hf n hxZ hcarT hcarU]

end Work.EKLProd
