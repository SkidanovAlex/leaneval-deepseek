import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.prodFlower_T_slice
import Submission.Work.EKLRelCross.SL3famDefs
import Submission.Work.EKLProd.prodFlowerKappa_toReal
import Submission.Work.EKLProd.prodFlowerLTP_apply

/-!
# The product structure of the joint `(T,U)`-law `prodFlowerΛTP`

This module proves `Work.EKLProd.prodFlower_Lambda_prod`, the `π`-`λ` step (3) of the
product-structure derivation of C5b (`EKLComp/ProductPlan.md` §10.3): for `μ`-a.e. base point
`x ∈ hf.Z n` the joint law of the `(T,U)`-coordinates of the `H`-plaque atom,

`prodFlowerΛTP hf n νH x = (prodFlowerΛ hf n νH x).map (g ↦ (hT T U g, hU T U g))`

is the **product** of its normalised `T`-marginal `prodFlowerκ hf n νT x` and its `U`-marginal
`(prodFlowerΛTP hf n νH x).map Prod.snd`.

The `T`-slice tower identity `Work.EKLProd.prodFlower_T_slice` (Pisa Lemma 8.10 for the pair
`(mH n, mT n)` of strip algebras) gives, for all Borel `A B` and at a.e. `x`,

`∫_{shape (mH n) H x} 1_A∘tpart · 1_B∘upart ∂(νH x) = c_A(x) * ∫_{shape (mH n) H x} 1_B∘upart ∂(νH x)`

with the fibre-independent constant `c_A(x) = (νT x)·hT(·)`-mass ratio, i.e.
`c_A(x) = (prodFlowerκ hf n νT x A).toReal`.  Converting the two integrals into the measures of
the corresponding sets (`prodFlower_slice_integral_meas`, the shape-mass measurability needed for
the set integral being supplied by `IsHoro H`), evaluating the pushforwards on rectangles
(`prodFlowerLTP_apply`) and inserting the `toReal` computation of `prodFlowerκ`
(`prodFlowerKappa_toReal`) yields `ΛTP (A ×ˢ B) = κ A * σ B` for all rectangles `A ×ˢ B` of a
countable π-system generating the Borel σ-algebra of `SL₃ × SL₃`; extensionality for finite
measures (`Measure.ext_of_generateFrom_of_iUnion`) then gives the identity of measures.

The coordinate map `g ↦ (hT T U g, hU T U g)` is only a.e.-measurable in general (`hT`, `hU` are
defined by `Classical.choose`); since `Measure.map` is *defined* to be `0` for a map that is not
a.e.-measurable, the proof splits into the case where the coordinate map is a.e.-measurable with
respect to `prodFlowerΛ hf n νH x` (where the mathematics above applies, with a measurable
surrogate `ψ` of the coordinate map) and the degenerate case (where both sides are `0`).
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.EKLProd
open Work.EKLContract

private theorem prodFlower_slice_integral_meas {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}
    (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νH : X3 → MeasureTheory.Measure SL3) {x : X3} (hxZ : x ∈ hf.Z n)
    (hSmeas : MeasurableSet (shape (hf.mH n) H x))
    {ψ : SL3 → SL3 × SL3} (hψ : Measurable ψ)
    (hψae : ψ =ᵐ[prodFlowerΛ hf n νH x] (fun g : SL3 => (hT T U g, hU T U g)))
    {A B : Set SL3} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ h in shape (hf.mH n) H x,
        A.indicator (fun _ => (1:ℝ)) (hT T U (hf.co n (h • x)))
          * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x))) ∂(νH x))
      = ((νH x) (shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B})).toReal := by
  classical
  have hWmeas : MeasurableSet (shape (hf.mH n) H x ∩
      {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}) := by
    refine hSmeas.inter ?_
    exact (hψ.comp (continuous_mul_const (hf.co n x)).measurable) (hA.prod hB)
  -- the set where `ψ` differs from the coordinate map is null for the restricted measure
  have hrel : ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)),
      ψ (h * hf.co n x) = (hT T U (h * hf.co n x), hU T U (h * hf.co n x)) := by
    rw [MeasureTheory.ae_iff]
    refine le_antisymm ?_ bot_le
    have h0 : prodFlowerΛ hf n νH x {g : SL3 | ¬ (ψ g = (hT T U g, hU T U g))} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hψae
    calc ((νH x).restrict (shape (hf.mH n) H x))
          {h : SL3 | ¬ (ψ (h * hf.co n x) = (hT T U (h * hf.co n x), hU T U (h * hf.co n x)))}
        = ((νH x).restrict (shape (hf.mH n) H x))
          ((fun h : SL3 => h * hf.co n x) ⁻¹' {g : SL3 | ¬ (ψ g = (hT T U g, hU T U g))}) := rfl
      _ ≤ (Measure.map (fun h : SL3 => h * hf.co n x)
            ((νH x).restrict (shape (hf.mH n) H x)))
          {g : SL3 | ¬ (ψ g = (hT T U g, hU T U g))} :=
          Measure.le_map_apply (((continuous_mul_const (hf.co n x)).measurable).aemeasurable) _
      _ = prodFlowerΛ hf n νH x {g : SL3 | ¬ (ψ g = (hT T U g, hU T U g))} := rfl
      _ = 0 := h0
  have hae' : ∀ᵐ h ∂(νH x), h ∈ shape (hf.mH n) H x →
      ψ (h * hf.co n x) = (hT T U (h * hf.co n x), hU T U (h * hf.co n x)) :=
    (MeasureTheory.ae_restrict_iff' hSmeas).mp hrel
  -- pointwise: on the region where the two agree, the two indicators coincide
  have hpt : ∀ h, (h ∈ shape (hf.mH n) H x →
        ψ (h * hf.co n x) = (hT T U (h * hf.co n x), hU T U (h * hf.co n x))) →
      (shape (hf.mH n) H x).indicator (fun h => A.indicator (fun _ => (1:ℝ))
            (hT T U (hf.co n (h • x)))
          * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x)))) h
        = (shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}).indicator
            (fun _ => (1:ℝ)) h := by
    intro h hh
    by_cases hS : h ∈ shape (hf.mH n) H x
    · have hcoe : hf.co n (h • x) = h * hf.co n x := hf.co_smul n x hxZ h hS.1 hS.2
      rw [Set.indicator_of_mem hS]
      have hL : A.indicator (fun _ => (1:ℝ)) (hT T U (hf.co n (h • x)))
            * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x)))
          = (A ×ˢ B).indicator (fun _ => (1:ℝ))
              (hT T U (h * hf.co n x), hU T U (h * hf.co n x)) := by
        rw [hcoe]
        by_cases ha : hT T U (h * hf.co n x) ∈ A <;>
          by_cases hb : hU T U (h * hf.co n x) ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, ha, hb, Set.mem_prod]
      rw [hL, ← hh hS]
      by_cases hmem : ψ (h * hf.co n x) ∈ A ×ˢ B
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show h ∈ shape (hf.mH n) H x ∩
            {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B} from ⟨hS, hmem⟩)]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show h ∉ shape (hf.mH n) H x ∩
            {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B} from fun hW => hmem hW.2)]
    · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem
        (show h ∉ shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}
          from fun hW => hS hW.1)]
  have hae : (shape (hf.mH n) H x).indicator (fun h => A.indicator (fun _ => (1:ℝ))
        (hT T U (hf.co n (h • x)))
      * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x))))
      =ᵐ[νH x] (shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}).indicator
          (fun _ => (1:ℝ)) :=
    hae'.mono (fun h hh => hpt h hh)
  calc (∫ h in shape (hf.mH n) H x, A.indicator (fun _ => (1:ℝ)) (hT T U (hf.co n (h • x)))
      * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x))) ∂(νH x))
      = ∫ h, (shape (hf.mH n) H x).indicator (fun h => A.indicator (fun _ => (1:ℝ))
          (hT T U (hf.co n (h • x)))
        * B.indicator (fun _ => (1:ℝ)) (hU T U (hf.co n (h • x)))) h ∂(νH x) :=
        (MeasureTheory.integral_indicator hSmeas).symm
    _ = ∫ h, (shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B}).indicator
          (fun _ => (1:ℝ)) h ∂(νH x) := MeasureTheory.integral_congr_ae hae
    _ = ((νH x) (shape (hf.mH n) H x ∩ {h : SL3 | ψ (h * hf.co n x) ∈ A ×ˢ B})).toReal := by
        rw [MeasureTheory.integral_indicator_const (μ := νH x) (1:ℝ) hWmeas]
        simp [MeasureTheory.Measure.real]


theorem prodFlower_Lambda_prod (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) (n : ℕ) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), MeasureTheory.IsFiniteMeasure (Work.EKLProd.prodFlowerΛTP hf n νH x) ∧ Work.EKLProd.prodFlowerΛTP hf n νH x = (Work.EKLProd.prodFlowerκ hf n νT x).prod ((Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd) := by
  classical
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  let Tow : X3 → Set SL3 → Set SL3 → Prop := fun x A B =>
    (∫ h in shape (hf.mH n) H x,
        A.indicator (fun _ => (1:ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
          * B.indicator (fun _ => (1:ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x))
      = (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (A ∩ (V hf.R ∩ (T : Set SL3)))).toReal
          / (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (V hf.R ∩ (T : Set SL3))).toReal
        * (∫ h in shape (hf.mH n) H x,
            B.indicator (fun _ => (1:ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x))
  have htower1 : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ pq : (ℕ × Finset ℕ) × (ℕ × Finset ℕ),
      Tow x (Work.EKLRelCross.SL3fam pq.1) (Work.EKLRelCross.SL3fam pq.2) := by
    refine MeasureTheory.ae_all_iff.mpr (fun pq => ?_)
    exact prodFlower_T_slice hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj hf hνH hνT n t hcent
      hcontr (Work.EKLRelCross.measurableSet_SL3fam pq.1) (Work.EKLRelCross.measurableSet_SL3fam pq.2)
  filter_upwards [prodFlower_shape_mass hf hνH n, htower1, MeasureTheory.ae_restrict_mem hZmeas]
    with x hmassHx htower1x hxZ
  by_cases hTP : AEMeasurable (fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) (prodFlowerΛ hf n νH x)
  · obtain ⟨ψ, hψmeas, hψae⟩ : ∃ ψ : SL3 → SL3 × SL3, Measurable ψ ∧
        ψ =ᵐ[prodFlowerΛ hf n νH x] (fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) :=
      ⟨AEMeasurable.mk (fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) hTP, AEMeasurable.measurable_mk hTP,
        (AEMeasurable.ae_eq_mk hTP).symm⟩
    have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
      obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
      rw [hOshape]
      exact hOo.measurableSet.inter hH.1.measurableSet
    have hrect : ∀ (A B : Set SL3), MeasurableSet A → MeasurableSet B → Tow x A B →
        prodFlowerΛTP hf n νH x (A ×ˢ B)
          = prodFlowerκ hf n νT x A * (prodFlowerΛTP hf n νH x).map Prod.snd B := by
      intro A B hA hB htw
      have hL := prodFlowerLTP_apply (A := A) (B := B) hf n νH x hψmeas hψae hA hB
      have hI1 := prodFlower_slice_integral_meas (A := A) (B := B) hf n νH hxZ hSmeas hψmeas hψae hA hB
      have hI2u := prodFlower_slice_integral_meas (A := Set.univ) (B := B) hf n νH hxZ hSmeas hψmeas
        hψae MeasurableSet.univ hB
      have hD2u := prodFlowerLTP_apply (A := Set.univ) (B := B) hf n νH x hψmeas hψae
        MeasurableSet.univ hB
      have hK := prodFlowerKappa_toReal (A := A) hf n νT x hA
      have hI2 : (∫ h in shape (hf.mH n) H x,
            B.indicator (fun _ => (1:ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x))
          = ((νH x) (shape (hf.mH n) H x ∩
              {h : SL3 | ψ (h * hf.co n x) ∈ (Set.univ : Set SL3) ×ˢ B})).toReal := by
        rw [← hI2u]
        congr 1
        ext h
        simp
      have hσ : (prodFlowerΛTP hf n νH x).map Prod.snd B
          = (νH x) (shape (hf.mH n) H x ∩
              {h : SL3 | ψ (h * hf.co n x) ∈ (Set.univ : Set SL3) ×ˢ B}) := by
        rw [Measure.map_apply measurable_snd hB]
        have hpre : Prod.snd ⁻¹' B = (Set.univ : Set SL3) ×ˢ B := by
          ext z; simp
        rw [hpre, hD2u]
      have hneσ : (prodFlowerΛTP hf n νH x).map Prod.snd B ≠ ⊤ := by
        rw [hσ]
        exact ne_top_of_le_ne_top (ne_top_of_lt hmassHx.2) (measure_mono Set.inter_subset_left)
      have hneκ : prodFlowerκ hf n νT x A ≠ ⊤ := by
        have key : ∀ a m : ENNReal, m ≤ a → a⁻¹ * m ≤ 1 := by
          intro a m hm
          rcases eq_or_ne a 0 with h | h
          · subst h
            have hm0 : m = 0 := le_bot_iff.mp hm
            simp [hm0]
          · rcases eq_or_ne a ⊤ with h' | h'
            · subst h'; simp
            · calc a⁻¹ * m ≤ a⁻¹ * a := by gcongr
                _ ≤ 1 := by simp [ENNReal.inv_mul_cancel h h']
        have hstep : prodFlowerκ hf n νT x A
            = (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
                (V hf.R ∩ (T : Set SL3)))⁻¹
              * (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
                (A ∩ (V hf.R ∩ (T : Set SL3)))) := by
          rw [prodFlowerκ, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
        have hle : prodFlowerκ hf n νT x A ≤ 1 := by
          rw [hstep]
          exact key _ _ (measure_mono Set.inter_subset_right)
        exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have htoReal : (prodFlowerΛTP hf n νH x (A ×ˢ B)).toReal
          = (prodFlowerκ hf n νT x A * (prodFlowerΛTP hf n νH x).map Prod.snd B).toReal := by
        rw [hL, ← hI1, htw, hI2, ← hK, ← hσ, ENNReal.toReal_mul]
      have hneL : prodFlowerΛTP hf n νH x (A ×ˢ B) ≠ ⊤ := by
        rw [hL]
        exact ne_top_of_le_ne_top (ne_top_of_lt hmassHx.2) (measure_mono Set.inter_subset_left)
      have hneR : prodFlowerκ hf n νT x A * (prodFlowerΛTP hf n νH x).map Prod.snd B ≠ ⊤ :=
        ENNReal.mul_ne_top hneκ hneσ
      exact (ENNReal.toReal_eq_toReal_iff' hneL hneR).mp htoReal
    have hfin : IsFiniteMeasure (prodFlowerΛTP hf n νH x) := by
      refine ⟨?_⟩
      have h := prodFlowerLTP_apply (A := Set.univ) (B := Set.univ) hf n νH x hψmeas hψae
        MeasurableSet.univ MeasurableSet.univ
      rw [← Set.univ_prod_univ, h]
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hmassHx.2
    refine ⟨hfin, ?_⟩
    let P : Set (Set SL3) := Set.range Work.EKLRelCross.SL3fam
    let C : Set (Set (SL3 × SL3)) := Set.image2 (fun a b : Set SL3 => a ×ˢ b) P P
    have hPcount : P.Countable := Set.countable_range _
    have hPpi : IsPiSystem P := Work.EKLRelCross.isPiSystem_SL3fam
    have hPgen : MeasurableSpace.generateFrom P = (inferInstance : MeasurableSpace SL3) :=
      Work.EKLRelCross.generateFrom_SL3fam
    have hPspan : IsCountablySpanning P := ⟨fun k => Work.EKLRelCross.SL3fam (k, ∅),
      fun k => Set.mem_range_self _, Work.EKLRelCross.iUnion_SL3fam_empty⟩
    have hCcount : C.Countable := by
      refine Set.Countable.mono ?_ ((hPcount.prod hPcount).image (fun p : Set SL3 × Set SL3 => p.1 ×ˢ p.2))
      rintro s ⟨A, hA, B, hB, rfl⟩
      exact ⟨(A, B), ⟨hA, hB⟩, rfl⟩
    have hCpi : IsPiSystem C := hPpi.prod hPpi
    have hCgen : (inferInstance : MeasurableSpace (SL3 × SL3)) = MeasurableSpace.generateFrom C :=
      (generateFrom_eq_prod hPgen hPgen hPspan hPspan).symm
    let Bseq : ℕ → Set (SL3 × SL3) := fun i =>
      Work.EKLRelCross.SL3fam (i, ∅) ×ˢ Work.EKLRelCross.SL3fam (i, ∅)
    have hBspan : (⋃ i, Bseq i) = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      obtain ⟨i, hi⟩ := exists_mem_compactCovering z.1
      obtain ⟨j, hj⟩ := exists_mem_compactCovering z.2
      refine Set.mem_iUnion.2 ⟨max i j, ?_⟩
      have hSi : Work.EKLRelCross.SL3fam (max i j, (∅ : Finset ℕ)) = compactCovering SL3 (max i j) := by
        simp [Work.EKLRelCross.SL3fam]
      show z ∈ Work.EKLRelCross.SL3fam (max i j, ∅) ×ˢ Work.EKLRelCross.SL3fam (max i j, ∅)
      rw [hSi]
      exact ⟨compactCovering_subset SL3 (le_max_left i j) hi, compactCovering_subset SL3 (le_max_right i j) hj⟩
    have hBmem : ∀ i, Bseq i ∈ C := fun i =>
      Set.mem_image2_of_mem (Set.mem_range_self (i, ∅)) (Set.mem_range_self (i, ∅))
    have hBfin : ∀ i, prodFlowerΛTP hf n νH x (Bseq i) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top hfin.measure_univ_lt_top.ne (measure_mono (Set.subset_univ _))
    have heq : ∀ s ∈ C, prodFlowerΛTP hf n νH x s
        = (prodFlowerκ hf n νT x).prod ((prodFlowerΛTP hf n νH x).map Prod.snd) s := by
      rintro s ⟨A, hA, B, hB, rfl⟩
      obtain ⟨p, rfl⟩ := hA
      obtain ⟨q, rfl⟩ := hB
      rw [hrect (Work.EKLRelCross.SL3fam p) (Work.EKLRelCross.SL3fam q)
          (Work.EKLRelCross.measurableSet_SL3fam p) (Work.EKLRelCross.measurableSet_SL3fam q)
          (htower1x (p, q)), Measure.prod_prod]
    exact Measure.ext_of_generateFrom_of_iUnion C Bseq hCgen hCpi hBspan hBmem hBfin heq
  · -- v4.34: `Measure.map` of a non-a.e.-measurable map is no longer `0`; instead show that
    -- this branch is impossible (the coordinate pair is a.e.-measurable on the plaque).
    exfalso
    apply hTP
    have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
      obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
      rw [hOshape]; exact hOo.measurableSet.inter hH.1.measurableSet
    have hmeas2 : Measurable (fun h : SL3 =>
        (Work.EKLProd.hT T U (hf.co n (h • x)), Work.EKLProd.hU T U (hf.co n (h • x)))) :=
      ((hf.meas_tp n).comp (continuous_id.smul continuous_const).measurable).prodMk
        ((hf.meas_up n).comp (continuous_id.smul continuous_const).measurable)
    have hae : (fun h : SL3 =>
        (Work.EKLProd.hT T U (hf.co n (h • x)), Work.EKLProd.hU T U (hf.co n (h • x))))
        =ᵐ[(νH x).restrict (shape (hf.mH n) H x)]
        ((fun g : SL3 => (Work.EKLProd.hT T U g, Work.EKLProd.hU T U g)) ∘
          (MeasurableEquiv.mulRight (hf.co n x))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with h hh
      simp only [Function.comp_apply, MeasurableEquiv.coe_mulRight]
      rw [hf.co_smul n x hxZ h hh.1 hh.2]
    have key := (aemeasurable_map_equiv_iff (MeasurableEquiv.mulRight (hf.co n x))).mpr
      (hmeas2.aemeasurable.congr hae)
    unfold prodFlowerΛ
    exact key

end Work.EKLProd
