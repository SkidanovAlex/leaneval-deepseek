import Mathlib
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.uAvg_eq
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.prodFlower_T_slice
import Submission.Work.EKLProd.prodFlower_U_tower
import Submission.Work.EKLProd.prodFlower_slice_avg
import Submission.Work.EKLProd.slicing_identity_gen
import Submission.Work.EKLProd.hU_co_constant_on_atom
import Submission.Work.EKLProd.atomUnion_measurable
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.setIntegral_indicator_comp_eq_toReal
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLRelProduct.piSystem_borel_sl3
import Submission.Work.EKLRelProduct.hT_atom_determines_mU
import Submission.Work.EKLRelProduct.uAvg_factors_hT
import Submission.Work.EKLRelProduct.uShift_den_pos
import Submission.Work.EKLRelProduct.ae_eq_zero_of_preimage_integral
import Submission.Work.EKLRelProduct.ratio_ext_of_piSystem

/-!
# `Work.EKLRelProduct.uSide`  (Pisa 8.12c, the `U`-side of the product structure)

See `USIDE_PLAN.md`.  The proof decomposes as follows.

* `uSide_integral`: the `U`-side tower identity (`EKLProd/prodFlower_U_tower`) combined with the
  `T`-side one (`EKLProd/prodFlower_T_slice`) yields, for every Borel `A B` and a.e. `x`,
  `∫_{shape (mH n) H x} 1_A(hT∘co) · uAvg(h•x,B) ∂(νH x) = ρ_A(x) · (uMarg x B)`.
* `uAvg_factors_hT`: `uAvg(·,B)` depends only on `hT ∘ co` (the `mU n`-atoms cut out the level
  sets of `hT ∘ co`).
* `ae_eq_zero_of_preimage_integral`: the `π`-`λ` step turning the integral identity into
  `uAvg(h•x,B) = c(x,B)` for `(νH x)|shape`-a.e. `h`, using the factorization.
* `uShift_den_pos` + `ratio_ext_of_piSystem`: the passage from the countable `π`-system to *all*
  Borel `B`, and the identification of the `uAvg` ratio with the `uShift`/`uMarg` ratio
  (`uAvg_eq`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open MeasureTheory

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract Work.EKLProd

variable {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}

/-! ## Elementary bounds and the `uMarg`-integral identities -/

/-- The normalised `U`-shape average of an indicator takes values in `[0,1]`. -/
theorem uSide_uAvg_abs_le_one (hf : ProdFlowerFam H T U μ) (νU : X3 → Measure SL3) (n : ℕ) (y : X3)
    {B : Set SL3} (hB : @MeasurableSet SL3 (borel SL3) B) : |uAvg hf νU n y B| ≤ 1 := by
  classical
  have hmeas : Measurable (fun u : SL3 => Work.EKLProd.hU T U (hf.co n (u • y))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  rw [uAvg]
  have hnum : (∫ u in shape (hf.mU n) U y, B.indicator (fun _ => (1 : ℝ))
        (Work.EKLProd.hU T U (hf.co n (u • y))) ∂(νU y))
      = ((νU y) (shape (hf.mU n) U y
          ∩ (fun u : SL3 => Work.EKLProd.hU T U (hf.co n (u • y))) ⁻¹' B)).toReal :=
    setIntegral_indicator_comp_eq_toReal hmeas hB _
  rw [hnum]
  by_cases hM : ((νU y) (shape (hf.mU n) U y)).toReal = 0
  · rw [hM, div_zero, abs_zero]; norm_num
  · have hMpos : 0 < ((νU y) (shape (hf.mU n) U y)).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
    have hMtop : (νU y) (shape (hf.mU n) U y) ≠ ⊤ := by
      intro h; rw [h, ENNReal.toReal_top] at hMpos; exact lt_irrefl _ hMpos
    have hle : ((νU y) (shape (hf.mU n) U y
        ∩ (fun u : SL3 => Work.EKLProd.hU T U (hf.co n (u • y))) ⁻¹' B)).toReal
        ≤ ((νU y) (shape (hf.mU n) U y)).toReal :=
      ENNReal.toReal_mono hMtop (measure_mono Set.inter_subset_left)
    rw [abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg (le_of_lt hMpos)),
      div_le_one hMpos]
    exact hle

/-- `(uMarg x B).toReal` is the `νH x`-integral over the `H`-shape of `1_B ∘ (hU ∘ co)`. -/
theorem uSide_uMarg_eq_setIntegral (hf : ProdFlowerFam H T U μ) (νH : X3 → Measure SL3) (n : ℕ)
    (x : X3) {B : Set SL3} (hB : @MeasurableSet SL3 (borel SL3) B) :
    ((uMarg hf νH n x) B).toReal
      = ∫ h in shape (hf.mH n) H x,
          B.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x) := by
  have hmeas : Measurable (fun h : SL3 => Work.EKLProd.hU T U (hf.co n (h • x))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  rw [setIntegral_indicator_comp_eq_toReal hmeas hB]
  rw [uMarg, Measure.map_apply hmeas hB, Measure.restrict_apply (hmeas hB)]
  exact congrArg ENNReal.toReal (congrArg (νH x) (Set.inter_comm _ _))

/-- The `H`-shape is measurable (it is `O ∩ H` for an open `O`). -/
theorem uSide_measurableSet_shape (hH : IsHoro H) (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {x : X3} (hx : x ∈ hf.Z n) : @MeasurableSet SL3 (borel SL3) (shape (hf.mH n) H x) := by
  obtain ⟨O, hOo, hOshape⟩ := ((hf.plaqH n).2.2.2 x hx).2.2.1
  rw [hOshape]
  exact hOo.measurableSet.inter hH.1.measurableSet

/-- On the `H`-shape the `U`-part of the coordinate lies in `V R ∩ U`. -/
theorem uSide_shape_subset (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : ProdFlowerFam H T U μ) (n : ℕ) {x : X3} (hx : x ∈ hf.Z n) :
    shape (hf.mH n) H x
      ⊆ (fun y : SL3 => Work.EKLProd.hU T U (hf.co n (y • x))) ⁻¹' (V hf.R ∩ (U : Set SL3)) := by
  intro y hy
  have hyZ : y • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hx).1 hy.2
  exact ⟨(co_decomp_facts hTH hUH hcop hdisj hf n hyZ).2.2.2.2,
    (co_decomp_facts hTH hUH hcop hdisj hf n hyZ).2.1⟩

/-- The total mass of the `U`-marginal of the `H`-shape is the mass of the shape. -/
theorem uSide_uMarg_shape (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : ProdFlowerFam H T U μ) (νH : X3 → Measure SL3) (n : ℕ) {x : X3} (hx : x ∈ hf.Z n)
    (hS : @MeasurableSet SL3 (borel SL3) (V hf.R ∩ (U : Set SL3))) :
    (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) = (νH x) (shape (hf.mH n) H x) := by
  have hmeas : Measurable (fun h : SL3 => Work.EKLProd.hU T U (hf.co n (h • x))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  have hsub := uSide_shape_subset hTH hUH hcop hdisj hf n hx
  rw [uMarg, Measure.map_apply hmeas hS, Measure.restrict_apply (hS.preimage hmeas)]
  congr 1
  apply Set.eq_of_subset_of_subset
  · exact Set.inter_subset_right
  · intro y hy; exact ⟨hsub hy, hy⟩

/-- The `U`-marginal of the `H`-shape is carried by `V R ∩ U`. -/
theorem uSide_uMarg_carried (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : ProdFlowerFam H T U μ) (νH : X3 → Measure SL3) (n : ℕ) {x : X3} (hx : x ∈ hf.Z n)
    (hS : @MeasurableSet SL3 (borel SL3) (V hf.R ∩ (U : Set SL3))) :
    (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3))ᶜ = 0 := by
  have hmeas : Measurable (fun h : SL3 => Work.EKLProd.hU T U (hf.co n (h • x))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  have hsub := uSide_shape_subset hTH hUH hcop hdisj hf n hx
  rw [uMarg, Measure.map_apply hmeas hS.compl,
    Measure.restrict_apply (hS.compl.preimage hmeas)]
  have hpre : (fun y : SL3 => Work.EKLProd.hU T U (hf.co n (y • x))) ⁻¹' (V hf.R ∩ (U : Set SL3))ᶜ
      ∩ shape (hf.mH n) H x = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact hy.1 (hsub hy.2)
  rw [hpre, measure_empty]

/-! ## The combined slicing identity -/

/-- **The integral identity of the `U`-side** (Pisa 8.12c, first half): for Borel `A B` and a.e.
`x`, the `νH x`-average over the `H`-shape of `1_A(hT∘co) · uAvg(·,B)` is `ρ_A(x) · (uMarg x B)`,
where `ρ_A(x)` is the normalised `T`-marginal of `A ∩ (V R ∩ T)`.

Proved by chaining the `U`-side tower `prodFlower_U_tower` (which replaces `uAvg` by the `U`-test
function) with the `T`-side tower `prodFlower_T_slice` (which evaluates the `U`-test function). -/
theorem uSide_integral (hX3 : P_X3) (hLeaf : P_Leafwise) (hBirk : P_Birkhoff)
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hHh : IsHoro H) (hTh : IsHoro T) (hUh : IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hmu : IsAInvariant μ) (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {νH : X3 → Measure SL3} {XH : Set X3} (hνH : IsLeafwise μ H νH XH)
    {νT : X3 → Measure SL3} {XT : Set X3} (hνT : IsLeafwise μ T νT XT)
    {νU : X3 → Measure SL3} {XU : Set X3} (hνU : IsLeafwise μ U νU XU)
    (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, aDiag t * g = g * aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => aDiag t ^ k * u * (aDiag t ^ k)⁻¹)
      Filter.atTop (nhds 1))
    {A B : Set SL3} (hA : @MeasurableSet SL3 (borel SL3) A)
    (hB : @MeasurableSet SL3 (borel SL3) B) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      (∫ h in shape (hf.mH n) H x,
          A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
            * uAvg hf νU n (h • x) B ∂(νH x))
      = ((((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (A ∩ (V hf.R ∩ (T : Set SL3)))).toReal
          / (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (V hf.R ∩ (T : Set SL3))).toReal)
        * ((uMarg hf νH n x) B).toReal := by
  classical
  filter_upwards [prodFlower_U_tower hX3 hLeaf hBirk hmu hHh hUh hTH hUH hnorm hcop hdisj
      hf hνH hνU n hA hB,
    prodFlower_T_slice hX3 hLeaf hBirk hmu hHh hTh hTH hUH hnorm hcop hdisj
      hf hνH hνT n t hcent hcontr hA hB] with x hUtow hTsl
  unfold Work.EKLRelProduct.uAvg
  rw [← hUtow, hTsl]
  congr 1
  exact (uSide_uMarg_eq_setIntegral hf νH n x hB).symm

/-! ## A general `φ`-preimage / shape-integral conversion -/

/-- If `μ` is carried by `s`, the integral of `g` over `φ ⁻¹' A` is the `s`-integral of
`1_A(φ) · g`. -/
theorem uSide_integral_preimage_eq {μ : MeasureTheory.Measure SL3} {s : Set SL3} (hμs : μ sᶜ = 0)
    (hs : @MeasurableSet SL3 (borel SL3) s) {φ : SL3 → SL3} (hφ : Measurable φ)
    {A : Set SL3} (hA : @MeasurableSet SL3 (borel SL3) A) (g : SL3 → ℝ) :
    ∫ h in φ ⁻¹' A, g h ∂μ = ∫ h in s, A.indicator (fun _ => (1 : ℝ)) (φ h) * g h ∂μ := by
  have hpre : @MeasurableSet SL3 (borel SL3) (φ ⁻¹' A) := hA.preimage hφ
  rw [← MeasureTheory.integral_indicator hpre]
  have h1 : (fun h : SL3 => (φ ⁻¹' A).indicator g h)
      =ᵐ[μ] (fun h : SL3 => s.indicator (fun h => (φ ⁻¹' A).indicator g h) h) := by
    filter_upwards [MeasureTheory.ae_iff.mpr hμs] with h hh
    rw [Set.indicator_of_mem hh]
  rw [MeasureTheory.integral_congr_ae h1, MeasureTheory.integral_indicator hs]
  apply MeasureTheory.setIntegral_congr_fun hs
  intro h _
  change (φ ⁻¹' A).indicator g h = A.indicator (fun _ => (1 : ℝ)) (φ h) * g h
  by_cases hc : φ h ∈ A
  · rw [Set.indicator_of_mem (s := φ ⁻¹' A) hc, Set.indicator_of_mem hc]
    ring
  · rw [Set.indicator_of_notMem (s := φ ⁻¹' A) (fun hh' => hc hh'), Set.indicator_of_notMem hc]
    ring

/-- **Pisa 8.12c, the `U`-side.**  Compare `USIDE_PLAN.md`. -/
theorem uSide {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H T U : Subgroup Work.EKLContract.SL3} (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hmu : Work.EKLContract.IsAInvariant μ) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)), ∀ {B : Set Work.EKLContract.SL3}, @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) B → ((Work.EKLRelProduct.uShift hf νU n (h • x)) (B ∩ (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)))).toReal / ((Work.EKLRelProduct.uShift hf νU n (h • x)) (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))).toReal = ((Work.EKLRelProduct.uMarg hf νH n x) B).toReal / ((Work.EKLRelProduct.uMarg hf νH n x) (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))).toReal := by
  classical
  obtain ⟨C, hCpi, hCgen, hCcount, hCuniv, Bs, hBs, hBsC⟩ := piSystem_borel_sl3
  haveI hCcount' : Countable {A : Set SL3 // A ∈ C} := hCcount.to_subtype
  have hCbore : ∀ A : Set SL3, A ∈ C → @MeasurableSet SL3 (borel SL3) A := by
    intro A hA
    rw [← hCgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have hSmeas : @MeasurableSet SL3 (borel SL3) (V hf.R ∩ (U : Set SL3)) :=
    (((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet).inter
      hU.1.measurableSet
  have hZmeas : @MeasurableSet X3 (borel X3) (hf.Z n) :=
    (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  -- ## the factorization (for all `B ∈ C`)
  have hfac : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ q : {B : Set SL3 // B ∈ C},
      ∃ G : SL3 → ℝ, Measurable G ∧
        ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)),
          uAvg hf νU n (h • x) q.1 = G (Work.EKLProd.hT T U (hf.co n (h • x))) := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    exact uAvg_factors_hT hTH hUH hnorm hcop hdisj hf n hνH hνU (hCbore q.1 q.2)
  -- ## the integral identity (for all pairs)
  have hone : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      ∀ p : {A : Set SL3 // A ∈ C} × {B : Set SL3 // B ∈ C},
      (∫ h in shape (hf.mH n) H x, p.1.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
          * uAvg hf νU n (h • x) p.2.1 ∂(νH x))
      = ((((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (p.1.1 ∩ (V hf.R ∩ (T : Set SL3)))).toReal
          / (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (V hf.R ∩ (T : Set SL3))).toReal)
        * ((uMarg hf νH n x) p.2.1).toReal := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    exact uSide_integral hX3 hLeaf hBirk hH hT hU hTH hUH hnorm hcop hdisj hmu hf n
      hνH hνT hνU t hcent hcontr (hCbore p.1.1 p.1.2) (hCbore p.2.1 p.2.2)
  -- ## the `T`-side with `B = V R ∩ U`
  have htwo : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ A : {A : Set SL3 // A ∈ C},
      (∫ h in shape (hf.mH n) H x,
          A.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) ∂(νH x))
      = ((((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (A.1 ∩ (V hf.R ∩ (T : Set SL3)))).toReal
          / (((νT x).map (fun g : SL3 => g * Work.EKLProd.hT T U (hf.co n x)))
            (V hf.R ∩ (T : Set SL3))).toReal)
        * ((νH x) (shape (hf.mH n) H x)).toReal := by
    rw [MeasureTheory.ae_all_iff]
    intro A
    filter_upwards [prodFlower_T_slice hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj hf
        hνH hνT n t hcent hcontr (hCbore A.1 A.2) hSmeas,
      MeasureTheory.ae_restrict_mem hZmeas] with x hsl hxZ
    have hEqInt : (∫ h in shape (hf.mH n) H x,
          A.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) ∂(νH x))
        = (∫ h in shape (hf.mH n) H x,
          A.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
            * (V hf.R ∩ (U : Set SL3)).indicator (fun _ => (1 : ℝ))
                (Work.EKLProd.hU T U (hf.co n (h • x))) ∂(νH x)) := by
      apply MeasureTheory.setIntegral_congr_fun (uSide_measurableSet_shape hH hf n hxZ)
      intro h hh
      show A.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
        = A.1.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
          * (V hf.R ∩ (U : Set SL3)).indicator (fun _ => (1 : ℝ))
              (Work.EKLProd.hU T U (hf.co n (h • x)))
      rw [Set.indicator_of_mem (s := V hf.R ∩ (U : Set SL3))
        (uSide_shape_subset hTH hUH hcop hdisj hf n hxZ hh), mul_one]
    rw [hEqInt, hsl]
    congr 1
    rw [← uSide_uMarg_eq_setIntegral hf νH n x hSmeas,
      uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hSmeas]
  -- ## main
  filter_upwards [hone, hfac, htwo, prodFlower_shape_mass hf hνH n,
      MeasureTheory.ae_restrict_mem hZmeas,
      uShift_den_pos hTH hUH hnorm hcop hdisj hf n hνH hνU]
    with x hInt hFac hTwo hMass hxZ hDen
  have hmain : ∀ᵐ h ∂((νH x).restrict (shape (hf.mH n) H x)),
      ∀ q : {B : Set SL3 // B ∈ C},
        uAvg hf νU n (h • x) q.1
          = ((uMarg hf νH n x) q.1).toReal / ((νH x) (shape (hf.mH n) H x)).toReal := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    obtain ⟨G, hGmeas, hGae⟩ := hFac q
    set c : ℝ := ((uMarg hf νH n x) q.1).toReal / ((νH x) (shape (hf.mH n) H x)).toReal
      with hcdef
    have hmassne : ((νH x) (shape (hf.mH n) H x)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hMass.1, ne_of_lt hMass.2⟩
    have hφmeas : Measurable (fun h : SL3 => Work.EKLProd.hT T U (hf.co n (h • x))) :=
      (hf.meas_tp n).comp (continuous_id.smul continuous_const).measurable
    set G' : SL3 → ℝ := fun t => max (-1) (min (G t) 1) - c with hG'def
    set ψ : SL3 → ℝ := fun h => G' (Work.EKLProd.hT T U (hf.co n (h • x))) with hψdef
    have hG'meas : Measurable G' :=
      (measurable_const.max (hGmeas.min measurable_const)).sub measurable_const
    have hψb : ∃ K, ∀ h, |ψ h| ≤ K := by
      refine ⟨1 + |c|, fun h => ?_⟩
      rw [hψdef, hG'def]
      have h1 : |max (-1) (min (G (Work.EKLProd.hT T U (hf.co n (h • x)))) 1)| ≤ 1 := by
        rw [abs_le]
        exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
      calc |max (-1) (min (G (Work.EKLProd.hT T U (hf.co n (h • x)))) 1) - c|
          ≤ |max (-1) (min (G (Work.EKLProd.hT T U (hf.co n (h • x)))) 1)| + |c| := abs_sub _ _
        _ ≤ 1 + |c| := by linarith
    -- the identity of integrals
    have hIdentity : ∀ A ∈ C,
        (∫ h in shape (hf.mH n) H x, A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
            * uAvg hf νU n (h • x) q.1 ∂(νH x))
        = c * (∫ h in shape (hf.mH n) H x,
            A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) ∂(νH x)) := by
      intro A hA
      rw [hInt (⟨A, hA⟩, q), hTwo ⟨A, hA⟩, hcdef]
      field_simp
    -- the π-λ hypothesis
    have hint : ∀ A ∈ C,
        ∫ h in (fun h : SL3 => Work.EKLProd.hT T U (hf.co n (h • x))) ⁻¹' A, ψ h
          ∂((νH x).restrict (shape (hf.mH n) H x)) = 0 := by
      intro A hA
      have hμs : (((νH x).restrict (shape (hf.mH n) H x))) (shape (hf.mH n) H x)ᶜ = 0 := by
        rw [MeasureTheory.Measure.restrict_apply' (uSide_measurableSet_shape hH hf n hxZ),
          Set.compl_inter_self, measure_empty]
      rw [uSide_integral_preimage_eq hμs (uSide_measurableSet_shape hH hf n hxZ) hφmeas (hCbore A hA) ψ]
      rw [MeasureTheory.Measure.restrict_restrict_of_subset (Set.Subset.refl (shape (hf.mH n) H x))]
      simp only [hψdef]
      have hstep : (∫ h in shape (hf.mH n) H x,
            A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
              * G' (Work.EKLProd.hT T U (hf.co n (h • x))) ∂(νH x))
          = (∫ h in shape (hf.mH n) H x,
            A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
              * (uAvg hf νU n (h • x) q.1 - c) ∂(νH x)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hGae] with h hh
        have hclamp : G' (Work.EKLProd.hT T U (hf.co n (h • x)))
            = uAvg hf νU n (h • x) q.1 - c := by
          rw [hG'def]
          change max (-1) (min (G (Work.EKLProd.hT T U (hf.co n (h • x)))) 1) - c
            = uAvg hf νU n (h • x) q.1 - c
          have hb : |G (Work.EKLProd.hT T U (hf.co n (h • x)))| ≤ 1 := by
            rw [← hh]; exact uSide_uAvg_abs_le_one hf νU n (h • x) (hCbore q.1 q.2)
          rw [min_eq_left (le_of_abs_le hb), max_eq_right (neg_le_of_abs_le hb), ← hh]
        rw [hclamp]
      rw [hstep]
      haveI hfin : IsFiniteMeasure ((νH x).restrict (shape (hf.mH n) H x)) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply (s := shape (hf.mH n) H x)
              (t := Set.univ) MeasurableSet.univ, Set.univ_inter]; exact hMass.2⟩
      have hind_le : ∀ h : SL3,
          A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) ≤ 1 := by
        intro h
        by_cases hc : Work.EKLProd.hT T U (hf.co n (h • x)) ∈ A
        · simp [Set.indicator_of_mem hc]
        · simp [Set.indicator_of_notMem hc]
      have hind_nn : ∀ h : SL3,
          0 ≤ A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) := by
        intro h
        by_cases hc : Work.EKLProd.hT T U (hf.co n (h • x)) ∈ A
        · simp [Set.indicator_of_mem hc]
        · simp [Set.indicator_of_notMem hc]
      have hI1 : Integrable (fun h : SL3 =>
          A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
            * uAvg hf νU n (h • x) q.1) ((νH x).restrict (shape (hf.mH n) H x)) := by
        have hab : AEStronglyMeasurable (fun h : SL3 =>
              A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
                * G (Work.EKLProd.hT T U (hf.co n (h • x)))) ((νH x).restrict (shape (hf.mH n) H x)) :=
          (((measurable_const.indicator (hCbore A hA)).comp hφmeas).mul
              (hGmeas.comp hφmeas)).aestronglyMeasurable
        have hcong : (fun h : SL3 =>
              A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
                * uAvg hf νU n (h • x) q.1)
            =ᵐ[((νH x).restrict (shape (hf.mH n) H x))] (fun h : SL3 =>
              A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
                * G (Work.EKLProd.hT T U (hf.co n (h • x)))) := by
          filter_upwards [hGae] with h hh
          rw [hh]
        refine Integrable.of_bound (hab.congr hcong.symm) 1 ?_
        filter_upwards with h
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hind_nn h)]
        exact le_trans (mul_le_mul (hind_le h) (uSide_uAvg_abs_le_one hf νU n (h • x) (hCbore q.1 q.2))
          (abs_nonneg _) zero_le_one) (le_of_eq (one_mul 1))
      have hI2 : Integrable (fun h : SL3 =>
          c * A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))))
          ((νH x).restrict (shape (hf.mH n) H x)) := by
        have hab : AEStronglyMeasurable (fun h : SL3 =>
              c * A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))))
            ((νH x).restrict (shape (hf.mH n) H x)) :=
          (measurable_const.mul ((measurable_const.indicator (hCbore A hA)).comp hφmeas)).aestronglyMeasurable
        refine Integrable.of_bound hab |c| ?_
        filter_upwards with h
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hind_nn h)]
        calc |c| * A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
            ≤ |c| * 1 := mul_le_mul_of_nonneg_left (hind_le h) (abs_nonneg c)
          _ = |c| := mul_one |c|
      have hsplit : (∫ h in shape (hf.mH n) H x,
            A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
              * (uAvg hf νU n (h • x) q.1 - c) ∂(νH x))
          = (∫ h in shape (hf.mH n) H x,
              A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x)))
                * uAvg hf νU n (h • x) q.1 ∂(νH x))
            - c * (∫ h in shape (hf.mH n) H x,
              A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (h • x))) ∂(νH x)) := by
        rw [← MeasureTheory.integral_const_mul]
        rw [← MeasureTheory.integral_sub hI1 hI2]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with h
        ring
      rw [hsplit, hIdentity A hA]
      ring
    have hres : ψ =ᵐ[((νH x).restrict (shape (hf.mH n) H x))] 0 :=
      ae_eq_zero_of_preimage_integral
        (by rw [MeasureTheory.Measure.restrict_apply (s := shape (hf.mH n) H x)
              (t := Set.univ) MeasurableSet.univ, Set.univ_inter]; exact ne_of_lt hMass.2)
        hφmeas hCpi hCgen hBs hBsC hψb hG'meas (fun h => rfl) hint
    filter_upwards [hres, hGae] with h hψ0 hGval
    change G' (Work.EKLProd.hT T U (hf.co n (h • x))) = 0 at hψ0
    have hb : |G (Work.EKLProd.hT T U (hf.co n (h • x)))| ≤ 1 := by
      rw [← hGval]; exact uSide_uAvg_abs_le_one hf νU n (h • x) (hCbore q.1 q.2)
    rw [hG'def] at hψ0
    change max (-1) (min (G (Work.EKLProd.hT T U (hf.co n (h • x)))) 1) - c = 0 at hψ0
    rw [min_eq_left (le_of_abs_le hb), max_eq_right (neg_le_of_abs_le hb)] at hψ0
    rw [hGval]
    linarith
  filter_upwards [hmain, hDen,
    MeasureTheory.ae_restrict_mem (uSide_measurableSet_shape hH hf n hxZ)] with h hη hden hsh
  intro B hB
  have hz : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hsh.2
  have hd2 : 0 < (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) := by
    rw [uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hSmeas]; exact hMass.1
  have hd2' : (uMarg hf νH n x) (V hf.R ∩ (U : Set SL3)) < ⊤ := by
    rw [uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hSmeas]; exact hMass.2
  refine ratio_ext_of_piSystem hSmeas hden.1 hden.2 hd2 hd2'
    (uSide_uMarg_carried hTH hUH hcop hdisj hf νH n hxZ hSmeas) hCpi hCgen hBs hBsC ?_ B hB
  intro B' hB'
  rw [← uAvg_eq hTH hUH hnorm hcop hdisj hf n νU (hCbore B' hB') hz, hη ⟨B', hB'⟩,
    uSide_uMarg_shape hTH hUH hcop hdisj hf νH n hxZ hSmeas]

end Work.EKLRelProduct
