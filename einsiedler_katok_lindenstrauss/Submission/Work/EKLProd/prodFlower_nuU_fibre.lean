import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.uShift_den_pos
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLRelCross.SL3famDefs

/-!
# `Work.EKLProd.prodFlower_nuU_fibre`

The ball-level identification of the `U`-leafwise measure with the `U`-fibre `ν_r'` of the
plaquette measure (the second half of Pisa (8.12c), the step `P5` of
`EKLComp/ProductPlan.md` §11.2): for a.e. base point `x` of the `n`-th flower and `νH x`-a.e. `h`
in the `H`-shape, the (8.12c)-translated leafwise measure `uShift hf νU n (h • x)` restricted to
the `U`-ball `V R ∩ U` is proportional to the `U`-marginal `uMarg hf νH n x` of the plaquette
measure `Λ'' = prodFlowerΛTP hf n νH x` restricted to the same ball.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The `U`-marginal of the joint `(T,U)`-law `prodFlowerΛTP` is the pushforward of the shape
measure under the `U`-part of the coordinate, i.e. the `uMarg` of the U-side development.

This is `Measure.map_map` plus the identity `hU (co n (h • x)) = hU (h * co n x)` on the shape,
which is `ProdFlowerFam.co_smul`. -/
private theorem prodFlowerΛTP_map_snd_eq_uMarg {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}
    (hHh : IsHoro H) (hTh : IsHoro T) (hUh : IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : ProdFlowerFam H T U μ) (n : ℕ) (νH : X3 → MeasureTheory.Measure SL3)
    {x : X3} (hx : x ∈ hf.Z n) :
    (prodFlowerΛTP hf n νH x).map Prod.snd = Work.EKLRelProduct.uMarg hf νH n x := by
  have hpair : Measurable (fun g : SL3 => (hT T U g, hU T U g)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHh.1 hTh.1 hUh.1
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) :=
    Work.EKLRelProduct.uSide_measurableSet_shape hHh hf n hx
  have hae : ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)),
      hU T U (h * hf.co n x) = hU T U (hf.co n (h • x)) := by
    rw [MeasureTheory.ae_restrict_iff' hSmeas]
    exact Filter.Eventually.of_forall fun h hh => by
      rw [hf.co_smul n x hx h hh.1 hh.2]
  have hφ : Measurable (fun h : SL3 => (hT T U (h * hf.co n x), hU T U (h * hf.co n x))) :=
    hpair.comp (measurable_mul_const _)
  have hunfold : prodFlowerΛTP hf n νH x
      = ((νH x).restrict (shape (hf.mH n) H x)).map
          (fun h : SL3 => (hT T U (h * hf.co n x), hU T U (h * hf.co n x))) := by
    rw [prodFlowerΛTP, prodFlowerΛ,
      Measure.map_map (g := fun g : SL3 => (hT T U g, hU T U g))
        (f := fun h : SL3 => h * hf.co n x) hpair (measurable_mul_const (hf.co n x))]
    rfl
  rw [hunfold, Work.EKLRelProduct.uMarg,
    Measure.map_map (g := Prod.snd)
      (f := fun h : SL3 => (hT T U (h * hf.co n x), hU T U (h * hf.co n x))) measurable_snd hφ]
  exact MeasureTheory.Measure.map_congr hae


theorem prodFlower_nuU_fibre (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) (n : ℕ) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)), ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ((νU (h • x)).map (fun u : Work.EKLContract.SL3 => (Work.EKLProd.hT T U (hf.co n (h • x)))⁻¹ * u * (Work.EKLProd.hT T U (hf.co n (h • x))) * (Work.EKLProd.hU T U (hf.co n (h • x))))).restrict (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)) = c • (((Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd).restrict (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))) := by
  classical
  set B_U : Set SL3 := V hf.R ∩ (U : Set SL3) with hBU
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hSmeas : MeasurableSet B_U := by
    rw [hBU]
    exact ((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1.measurableSet).inter
      hU.1.measurableSet
  -- ## the three a.e. inputs
  have hratio := Work.EKLRelProduct.uSide hX3 hLeaf hBirk hH hT hU hTH hUH hnorm hcop hdisj hmu hf n
    hνH hνT hνU t hcent hcontr
  have hden := Work.EKLRelProduct.uShift_den_pos hTH hUH hnorm hcop hdisj hf n hνH hνU
  have hmass := prodFlower_shape_mass hf hνH n
  filter_upwards [hratio, hden, hmass, MeasureTheory.ae_restrict_mem hZmeas] with x hr hd hm hxZ
  -- ## pointwise (in `x`) facts
  have hmap := prodFlowerΛTP_map_snd_eq_uMarg hH hT hU hTH hUH hnorm hcop hdisj hf n νH hxZ
  have hshapeM := Work.EKLRelProduct.uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ
    (by rw [← hBU]; exact hSmeas)
  have hcarried := Work.EKLRelProduct.uSide_uMarg_carried hTH hUH hcop hdisj hf νH n hxZ
    (by rw [← hBU]; exact hSmeas)
  filter_upwards [hr, hd] with h hrh hdh
  -- ## abbreviations
  set M : ENNReal := (νH x) (shape (hf.mH n) H x) with hM
  set lam : MeasureTheory.Measure SL3 := Work.EKLRelProduct.uShift hf νU n (h • x) with hlam
  set nu : MeasureTheory.Measure SL3 := Work.EKLRelProduct.uMarg hf νH n x with hnu
  have hM0 : M ≠ 0 := by rw [hM]; exact hm.1.ne'
  have hMt : M ≠ ⊤ := by rw [hM]; exact ne_of_lt hm.2
  have hlam0 : lam B_U ≠ 0 := by rw [hlam, hBU]; exact hdh.1.ne'
  have hlamt : lam B_U < ⊤ := by rw [hlam, hBU]; exact hdh.2
  have hnuBU : nu B_U = M := by rw [hnu, hM, hBU]; exact hshapeM
  have hrh' : ∀ {B : Set SL3}, MeasurableSet B →
      (lam (B ∩ B_U)).toReal / (lam B_U).toReal = (nu B).toReal / (nu B_U).toReal := by
    intro B hB
    rw [hlam, hnu, hBU]
    exact hrh hB
  have hcarried' : nu B_Uᶜ = 0 := by rw [hnu, hBU]; exact hcarried
  -- ## `nu` is carried by the ball
  have hnu_inter : ∀ B : Set SL3, MeasurableSet B → nu (B ∩ B_U) = nu B := by
    intro B hB
    have hcompl : nu (B ∩ B_Uᶜ) = 0 :=
      MeasureTheory.measure_mono_null Set.inter_subset_right hcarried'
    have hunion : B = (B ∩ B_U) ∪ (B ∩ B_Uᶜ) := by
      ext g
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    have hBunion : nu B = nu (B ∩ B_U) := by
      conv_lhs => rw [hunion]
      rw [MeasureTheory.measure_union (Set.disjoint_left.mpr fun a ha hb => hb.2 ha.2)
        (hB.inter hSmeas.compl), hcompl, add_zero]
    exact hBunion.symm
  -- ## the ENNReal identity on all Borel sets
  have key : ∀ B : Set SL3, MeasurableSet B → lam (B ∩ B_U) = (lam B_U / M) * nu B := by
    intro B hB
    have hr := hrh' hB
    rw [hnuBU] at hr
    have hlamBU_toReal_ne : (lam B_U).toReal ≠ 0 :=
      (ENNReal.toReal_pos hlam0 (ne_of_lt hlamt)).ne'
    have hleft_ne : lam (B ∩ B_U) ≠ ⊤ :=
      ne_top_of_le_ne_top (ne_of_lt hlamt) (MeasureTheory.measure_mono Set.inter_subset_right)
    have hright_ne : (lam B_U / M) * nu B ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ne_of_lt hlamt) ?_
      calc (lam B_U / M) * nu B = (lam B_U / M) * nu (B ∩ B_U) := by rw [hnu_inter B hB]
        _ ≤ (lam B_U / M) * nu B_U :=
              mul_le_mul' le_rfl (MeasureTheory.measure_mono Set.inter_subset_right)
        _ = (lam B_U / M) * M := by rw [hnuBU]
        _ = lam B_U := ENNReal.div_mul_cancel hM0 hMt
    refine (ENNReal.toReal_eq_toReal_iff' hleft_ne hright_ne).mp ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_div]
    rw [div_eq_iff hlamBU_toReal_ne] at hr
    rw [hr]
    ring
  -- ## extension from the countable π-system `SL3fam`
  have heq : lam.restrict B_U = (lam B_U / M) • (nu.restrict B_U) := by
    have hCgen : (inferInstance : MeasurableSpace SL3)
        = MeasurableSpace.generateFrom (Set.range Work.EKLRelCross.SL3fam) :=
      (Work.EKLRelCross.generateFrom_SL3fam).symm
    have hCpi : IsPiSystem (Set.range Work.EKLRelCross.SL3fam) :=
      Work.EKLRelCross.isPiSystem_SL3fam
    have hBspan : (⋃ i : ℕ, Work.EKLRelCross.SL3fam (i, ∅)) = Set.univ :=
      Work.EKLRelCross.iUnion_SL3fam_empty
    have hBmem : ∀ i : ℕ, Work.EKLRelCross.SL3fam (i, ∅)
        ∈ Set.range Work.EKLRelCross.SL3fam := fun i => Set.mem_range_self _
    have hBfin : ∀ i : ℕ, (lam.restrict B_U) (Work.EKLRelCross.SL3fam (i, ∅)) ≠ ⊤ := by
      intro i
      refine ne_top_of_le_ne_top (ne_of_lt hlamt) ?_
      rw [MeasureTheory.Measure.restrict_apply (Work.EKLRelCross.measurableSet_SL3fam (i, ∅))]
      exact MeasureTheory.measure_mono Set.inter_subset_right
    have hreg : ∀ s ∈ Set.range Work.EKLRelCross.SL3fam,
        (lam.restrict B_U) s = ((lam B_U / M) • (nu.restrict B_U)) s := by
      rintro s ⟨p, rfl⟩
      rw [MeasureTheory.Measure.restrict_apply (Work.EKLRelCross.measurableSet_SL3fam p),
        MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply
          (Work.EKLRelCross.measurableSet_SL3fam p), smul_eq_mul]
      rw [hnu_inter (Work.EKLRelCross.SL3fam p) (Work.EKLRelCross.measurableSet_SL3fam p)]
      exact key (Work.EKLRelCross.SL3fam p) (Work.EKLRelCross.measurableSet_SL3fam p)
    exact MeasureTheory.Measure.ext_of_generateFrom_of_iUnion (Set.range Work.EKLRelCross.SL3fam)
      (fun i => Work.EKLRelCross.SL3fam (i, ∅)) hCgen hCpi hBspan hBmem hBfin hreg
  -- ## the target
  refine ⟨lam B_U / M, ?_, ?_, ?_⟩
  · rw [ENNReal.div_ne_zero]
    exact ⟨hlam0, hMt⟩
  · exact ENNReal.div_ne_top (ne_of_lt hlamt) hM0
  · rw [show (fun u : SL3 => (Work.EKLProd.hT T U (hf.co n (h • x)))⁻¹ * u
            * (Work.EKLProd.hT T U (hf.co n (h • x))) * (Work.EKLProd.hU T U (hf.co n (h • x))))
        = (fun u : SL3 => Work.EKLRelProduct.gconj (Work.EKLProd.hT T U (hf.co n (h • x)))⁻¹ u
            * (Work.EKLProd.hU T U (hf.co n (h • x)))) from by
      funext u
      simp only [Work.EKLRelProduct.gconj, inv_inv]]
    rw [hmap]
    change lam.restrict B_U = (lam B_U / M) • (nu.restrict B_U)
    exact heq

end Work.EKLProd
