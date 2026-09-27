import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.uShift_den_pos
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLRelProduct.uAvg_eq
import Submission.Work.EKLRelProduct.inv_smul_restrict_ne_top
import Submission.Work.EKLRelProduct.toReal_inv_smul_restrict_apply
import Submission.Work.EKLRelProduct.measure_ne_top_of_compl_eq_zero
import Submission.Work.EKLRelProduct.psiNu_uMargEqPsiMap
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.leafwise_null_transfer_gen

/-!
# `Work.EKLRelProduct.psiEqNuU`

The `U`-factor `psi` of the plaquette measure is, at the translate `h • x` of a point of the
`n`-th product-box flower, proportional to the `U`-leafwise measure restricted to the source set
`S_U` (with a positive finite constant).

Proof (the plan of the requester): `Work.EKLRelProduct.uSide` (Pisa 8.12c) identifies the
normalised `V R ∩ U`-ratio of `uShift hf νU n (h • x)` with the normalised ratio of
`uMarg hf νH n x`; the equivariance `Work.EKLRelProduct.psiNu_uMargShift` gives
`uMarg (h • x) ∝ uMarg x`, hence `uShift (h • x) ∝ uMarg (h • x)`; since (proved here)
`uShift y ↾ (V R ∩ U) = ((νU y) ↾ S_U y).map (shiftMap …)` and (delegated, proved)
`uMarg y = (psi y).map (shiftMap …)`, both sides are the `shiftMap`-pushforward of the two
measures, and `shiftMap` is a measurable embedding, so the proportionality descends.
-/

open MeasureTheory
open Work.EKLContract Work.EKLProd

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

/-- `uShift` restricted to `V R ∩ U` is the `shiftMap`-pushforward of `νU` restricted to the
source set `S_U` (which is *by definition* the `shiftMap`-preimage of `V R ∩ U`). -/
theorem uShift_restrict_eq_shiftMap {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}
    (hf : ProdFlowerFam H T U μ) (n : ℕ) (νU : X3 → MeasureTheory.Measure SL3) (y : X3) :
    (uShift hf νU n y).restrict (V hf.R ∩ (U : Set SL3))
      = ((νU y).restrict (S_U hf n y)).map
          (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y))) := by
  rw [uShift_eq_map hf νU n y,
    MeasurableEmbedding.restrict_map (measurableEmbedding_shiftMap _ _)]
  rfl

/-- **The ratio criterion for proportionality.**  If two measures `μ₁, μ₂` on `SL3` satisfy, for
every Borel `B`, the equality of normalised `D`-ratios
`(μ₁ (B ∩ D)).toReal / (μ₁ D).toReal = (μ₂ B).toReal / (μ₂ D).toReal`, and `μ₂` is carried by
`D`, and both `D`-masses are nonzero and finite, then `μ₁ ↾ D` is a scalar multiple of `μ₂`
(namely by `μ₁ D * (μ₂ D)⁻¹`).

The proof passes to the normalised restricted measures `(μ D)⁻¹ • (μ ↾ D)`, whose `.toReal` on a
Borel `B` is the ratio by `toReal_inv_smul_restrict_apply`; they agree on Borel sets and are finite
(`inv_smul_restrict_ne_top`), hence are equal. -/
theorem restrict_eq_smul_of_ratio {μ₁ μ₂ : MeasureTheory.Measure SL3} {D : Set SL3}
    (hD : MeasurableSet D) (hcar : μ₂ Dᶜ = 0) (h₁0 : μ₁ D ≠ 0) (h₁t : μ₁ D ≠ ⊤)
    (h₂0 : μ₂ D ≠ 0) (h₂t : μ₂ D ≠ ⊤)
    (hratio : ∀ B, MeasurableSet B →
      (μ₁ (B ∩ D)).toReal / (μ₁ D).toReal = (μ₂ B).toReal / (μ₂ D).toReal) :
    μ₁.restrict D = (μ₁ D * (μ₂ D)⁻¹) • μ₂ := by
  have hres2 : μ₂.restrict D = μ₂ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hcar)
  have hνeq : ((μ₁ D)⁻¹ • μ₁.restrict D) = ((μ₂ D)⁻¹ • μ₂.restrict D) := by
    refine Measure.ext (fun B hB => ?_)
    refine (ENNReal.toReal_eq_toReal_iff'
      (inv_smul_restrict_ne_top h₁0 h₁t B) (inv_smul_restrict_ne_top h₂0 h₂t B)).mp ?_
    rw [toReal_inv_smul_restrict_apply μ₁ hD B, toReal_inv_smul_restrict_apply μ₂ hD B]
    have hnum : μ₂ (B ∩ D) = μ₂ B := by
      rw [← Measure.restrict_apply' hD, hres2]
    rw [hnum]
    exact hratio B hB
  calc μ₁.restrict D = (1:ENNReal) • μ₁.restrict D := (one_smul ENNReal _).symm
    _ = (μ₁ D * (μ₁ D)⁻¹) • μ₁.restrict D := by rw [ENNReal.mul_inv_cancel h₁0 h₁t]
    _ = μ₁ D • ((μ₁ D)⁻¹ • μ₁.restrict D) := (smul_smul _ _ _).symm
    _ = μ₁ D • ((μ₂ D)⁻¹ • μ₂.restrict D) := by rw [hνeq]
    _ = μ₁ D • ((μ₂ D)⁻¹ • μ₂) := by rw [hres2]
    _ = (μ₁ D * (μ₂ D)⁻¹) • μ₂ := smul_smul _ _ _


/-- The general restriction/pushforward identity `(μ.map f)|_s = (μ|_{f⁻¹ s}).map f` for a
measurable `f` and a measurable `s` (proved via `Measure.map_apply` on measurable sets; the
measurability of `s` is needed since `μ.map f` is only tested on measurable sets). -/
theorem measure_map_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) {f : α → β} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) :
    (MeasureTheory.Measure.map f μ).restrict s
      = MeasureTheory.Measure.map f (μ.restrict (f ⁻¹' s)) := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.Measure.restrict_apply' hs,
    MeasureTheory.Measure.map_apply hf (hA.inter hs),
    MeasureTheory.Measure.map_apply hf hA,
    MeasureTheory.Measure.restrict_apply' (hs.preimage hf), Set.preimage_inter]

/-- **Equivariance of the `U`-marginal along the `H`-orbit.**  For a.e. base point `x` of the
`n`-th flower and `(νH x)|_{shape}`-a.e. leaf element `h`, the `U`-marginal at the translate
`h • x` is proportional to the `U`-marginal at `x`.  The constant is the inverse of the
`equivariant` constant of `hνH` at `(x, h)`. -/
theorem uMarg_eq_smul_translate {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3))
    (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {νH : X3 → MeasureTheory.Measure SL3} {XH : Set X3} (hνH : IsLeafwise μ H νH XH) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)),
      ∃ d : ENNReal, d ≠ 0 ∧ d ≠ ⊤ ∧
        uMarg hf νH n (h • x) = d • uMarg hf νH n x := by
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hXHae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XH := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (hνH.conull ▸ MeasureTheory.Measure.restrict_apply_le (hf.Z n) XHᶜ) bot_le
  have hN0 : (μ.restrict (hf.Z n)) XHᶜ = 0 :=
    le_antisymm (hνH.conull ▸ MeasureTheory.Measure.restrict_apply_le (hf.Z n) XHᶜ) bot_le
  have htrans := Work.EKLProd.leafwise_null_transfer_gen (N := XHᶜ) hνH (hf.plaqH n)
    (prodFlower_shape_mass hf hνH n) hN0
  filter_upwards [hXHae, htrans, MeasureTheory.ae_restrict_mem hZmeas] with x hxXH hxTrans hxZ
  have hShmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]; exact hOo.measurableSet.inter hHc.measurableSet
  have htrans' : ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)), h • x ∈ XH := by
    rw [MeasureTheory.ae_restrict_iff' hShmeas, MeasureTheory.ae_iff]
    refine le_antisymm (le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hxTrans)) bot_le
    intro h hh
    refine ⟨?_, ?_⟩
    · by_contra hcon; exact hh (fun hhs => absurd hhs hcon)
    · intro hQ; exact hh (fun _ => hQ)
  filter_upwards [htrans', MeasureTheory.ae_restrict_mem hShmeas] with h hhXH hhshape
  have hyZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hhshape.2
  have hhH : h ∈ H := hhshape.1
  obtain ⟨c, hc0, hct, hcEq⟩ := hνH.equivariant x hxXH h hhH hhXH
  have hco : hf.co n (h • x) = h * hf.co n x := hf.co_smul n x hxZ h hhH hhshape.2
  have hshape_shift : (fun w : SL3 => w * h) ⁻¹' (shape (hf.mH n) H x)
      = shape (hf.mH n) H (h • x) := by
    rw [hf.shapeH n x hxZ, hf.shapeH n (h • x) hyZ, hco]
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hwh, hwP⟩
      refine ⟨?_, by simpa only [mul_assoc] using hwP⟩
      have : w = (w * h) * h⁻¹ := by group
      rw [this]; exact H.mul_mem hwh (H.inv_mem hhH)
    · rintro ⟨hwH, hwP⟩
      exact ⟨H.mul_mem hwH hhH, by simpa only [mul_assoc] using hwP⟩
  have hMx_eq : (νH x).restrict (shape (hf.mH n) H x)
      = c • (((νH (h • x)).restrict (shape (hf.mH n) H (h • x))).map (fun w : SL3 => w * h)) := by
    rw [hcEq, MeasureTheory.Measure.restrict_smul,
      measure_map_restrict (νH (h • x)) (continuous_mul_const h).measurable hShmeas,
      hshape_shift]
  have hmeasψ : Measurable (fun w : SL3 => hU T U (hf.co n (w • x))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  have hShmeas_y : MeasurableSet (shape (hf.mH n) H (h • x)) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 (h • x) hyZ).2.2.1
    rw [hOshape]; exact hOo.measurableSet.inter hHc.measurableSet
  have hcomp : (fun w : SL3 => hU T U (hf.co n (w • x))) ∘ (fun w : SL3 => w * h)
      =ᵐ[((νH (h • x)).restrict (shape (hf.mH n) H (h • x)))]
      (fun w : SL3 => hU T U (hf.co n (w • (h • x)))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hShmeas_y] with w _
    simp only [Function.comp_apply]
    rw [mul_smul]
  have hMx : uMarg hf νH n x = c • (uMarg hf νH n (h • x)) := by
    rw [uMarg, hMx_eq, uMarg, MeasureTheory.Measure.map_smul _ hmeasψ.aemeasurable,
      MeasureTheory.Measure.map_map hmeasψ (continuous_mul_const h).measurable]
    rw [MeasureTheory.Measure.map_congr hcomp]
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  rw [hMx, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

theorem psiEqNuU {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff)
    (hHoroH : Work.EKLContract.IsHoro H) (hHoroT : Work.EKLContract.IsHoro T) (hHoroU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hmu : Work.EKLContract.IsAInvariant μ) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧
        Work.EKLRelProduct.psi hf νH n (h • x) = c • (νU (h • x)).restrict (Work.EKLRelProduct.S_U hf n (h • x)) := by
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hSmeas : MeasurableSet (V hf.R ∩ (U : Set SL3)) :=
    (((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet).inter
      hHoroU.1.measurableSet
  filter_upwards [uSide hX3 hLeaf hBirk hHoroH hHoroT hHoroU hTH hUH hnorm hcop hdisj hmu hf n hνH hνT hνU t hcent hcontr,
      uMarg_eq_smul_translate hTH hUH hcop hdisj hHoroH.1 hf n hνH,
      uShift_den_pos hTH hUH hnorm hcop hdisj hf n hνH hνU,
      prodFlower_shape_mass hf hνH n,
      MeasureTheory.ae_restrict_mem hZmeas]
    with x hSide hShift hDen hMass hxZ
  have hShmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOshape]; exact hOo.measurableSet.inter hHoroH.1.measurableSet
  filter_upwards [hSide, hShift, hDen, MeasureTheory.ae_restrict_mem hShmeas]
    with h hSide' hShift' hDen' hhshape
  obtain ⟨d, hd0, hdt, hShiftEq⟩ := hShift'
  -- masses and carrier of `uMarg x` on `V R ∩ U`
  have hMxV : (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) = (νH x) (shape (hf.mH n) H x) :=
    uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hSmeas
  have hcar : (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3))ᶜ = 0 :=
    uSide_uMarg_carried hTH hUH hcop hdisj hf νH n hxZ hSmeas
  have hMx0 : (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) ≠ 0 := by rw [hMxV]; exact hMass.1.ne'
  have hMxt : (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) ≠ ⊤ := by rw [hMxV]; exact hMass.2.ne
  have hUy0 : (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3)) ≠ 0 := hDen'.1.ne'
  have hUyt : (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3)) ≠ ⊤ := hDen'.2.ne
  -- the proportionality `uShift (h•x) ↾ V R ∩ U ∝ uMarg x`
  have hprop : (uShift hf νU n (h • x)).restrict (V hf.R ∩ (U : Set SL3))
      = ((uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
          * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹) • (uMarg hf νH n x) :=
    restrict_eq_smul_of_ratio hSmeas hcar hUy0 hUyt hMx0 hMxt (fun B hB => hSide' hB)
  set C : ENNReal := (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
      * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹ * d⁻¹ with hC_def
  have hc0 : C ≠ 0 := by
    rw [hC_def]
    exact mul_ne_zero (mul_ne_zero hUy0 (ENNReal.inv_ne_zero.mpr hMxt))
      (ENNReal.inv_ne_zero.mpr hdt)
  have hct : C ≠ ⊤ := by
    rw [hC_def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hUyt (ENNReal.inv_ne_top.mpr hMx0))
      (ENNReal.inv_ne_top.mpr hd0)
  have hkey : ((uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
        * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹ * d⁻¹) * d
      = (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
        * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹ := by
    calc ((uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
            * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹ * d⁻¹) * d
        = ((uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
            * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹) * (d⁻¹ * d) :=
          mul_assoc _ _ _
      _ = ((uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
            * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹) * 1 := by
          rw [ENNReal.inv_mul_cancel hd0 hdt]
      _ = (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
            * ((uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)))⁻¹ := mul_one _
  have hprop2 : (uShift hf νU n (h • x)).restrict (V hf.R ∩ (U : Set SL3))
      = C • (uMarg hf νH n (h • x)) := by
    rw [hprop, hC_def, hShiftEq, smul_smul, hkey]
  have hyZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hhshape.2
  have hE := uShift_restrict_eq_shiftMap hf n νU (h • x)
  have hD := psiNu_uMargEqPsiMap hTH hUH hnorm hcop hdisj hHoroH.1 hHoroT.1 hHoroU.1 hf n νH hyZ
  have hφinj : Function.Injective
      (MeasureTheory.Measure.map
        (shiftMap (hT T U (hf.co n (h • x))) (hU T U (hf.co n (h • x))))) :=
    (measurableEmbedding_shiftMap _ _).map_injective
  have hmap : ((νU (h • x)).restrict (S_U hf n (h • x))).map
        (shiftMap (hT T U (hf.co n (h • x))) (hU T U (hf.co n (h • x))))
      = (C • psi hf νH n (h • x)).map
        (shiftMap (hT T U (hf.co n (h • x))) (hU T U (hf.co n (h • x)))) := by
    rw [← hE, hprop2, hD,
      MeasureTheory.Measure.map_smul _ (measurableEmbedding_shiftMap _ _).measurable.aemeasurable]
  have hfinal : (νU (h • x)).restrict (S_U hf n (h • x)) = C • psi hf νH n (h • x) :=
    hφinj hmap
  refine ⟨C⁻¹, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne zero_le (Ne.symm (ENNReal.inv_ne_zero.mpr hct))
  · exact ENNReal.inv_ne_top.mpr hc0
  · rw [hfinal, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

end Work.EKLRelProduct
