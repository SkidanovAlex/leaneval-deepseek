import Mathlib
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.hU_co_constant_on_atom
import Submission.Work.EKLProd.setIntegral_indicator_comp_eq_toReal

/-!
# `Work.EKLRelProduct.uAvg_eq`

The change of variables behind Pisa (8.12c): the normalised `U`-shape average of the
`(mU n)`-slice algebra of a product-box flower is the `U`-ball average of the translated
leafwise measure `uShift`.

Concretely, if `t = hT T U (co n y)` and `u₀ = hU T U (co n y)` are the `T`- and `U`-parts of the
plaque coordinate of `y` (so that `co n y = t * u₀`), then

* the `U`-shape of the `n`-th flower at `y` is the preimage under `w ↦ t⁻¹ * w * t * u₀` of the
  ball `V R ∩ U` (`shapeU_eq_shift`),
* on that shape the `U`-part of the coordinate at `w • y` is exactly `t⁻¹ * w * t * u₀`
  (`hU_co_eq_shift`),

and `uShift` is the pushforward of `νU y` along this map (`uShift_eq_map`).  No closedness
hypothesis on `U` is needed: the evaluation of a pushforward along a *measurable embedding* is
unconditional (`MeasurableEmbedding.map_apply`).
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract Work.EKLProd

/-- The change of variables `w ↦ ((t⁻¹ * w) * t) * u₀` underlying the `uShift` reparametrisation
of the `U`-leafwise measure. -/
def shiftMap (t u₀ : SL3) (w : SL3) : SL3 := ((t⁻¹ * w) * t) * u₀

theorem shiftMap_mul (t u₀ g : SL3) : g * (t * u₀) = t * shiftMap t u₀ g := by
  unfold shiftMap; group

/-- `shiftMap t u₀` is a homeomorphism, hence a measurable embedding. -/
theorem measurableEmbedding_shiftMap (t u₀ : SL3) : MeasurableEmbedding (shiftMap t u₀) := by
  unfold shiftMap
  have h1 : MeasurableEmbedding (fun w : SL3 => t⁻¹ * w) :=
    (MeasurableEquiv.mulLeft t⁻¹).measurableEmbedding
  have h2 : MeasurableEmbedding (fun w : SL3 => w * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  have h3 : MeasurableEmbedding (fun w : SL3 => w * u₀) :=
    (MeasurableEquiv.mulRight u₀).measurableEmbedding
  exact h3.comp (h2.comp h1)

/-- `shiftMap t u₀` preserves the normaliser relation: it maps `U` onto `U` when `t ∈ T`. -/
theorem shiftMap_mem_U_iff {T U : Subgroup SL3}
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    {t u₀ : SL3} (htT : t ∈ T) (huU : u₀ ∈ U) (g : SL3) :
    shiftMap t u₀ g ∈ U ↔ g ∈ U := by
  constructor
  · intro h
    have h1 : ((t⁻¹ * g) * t) * u₀ ∈ U := h
    have h2 : t⁻¹ * g * t ∈ U := by
      have hh := U.mul_mem h1 (U.inv_mem huU)
      have he : ((t⁻¹ * g) * t) * u₀ * u₀⁻¹ = t⁻¹ * g * t := by group
      rwa [he] at hh
    have h3 : t * (t⁻¹ * g * t) * t⁻¹ ∈ U := hnorm t htT _ h2
    have h4 : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
    rwa [h4] at h3
  · intro hg
    have h2 : t⁻¹ * g * t ∈ U := by
      have hh := hnorm t⁻¹ (T.inv_mem htT) g hg
      simpa using hh
    exact U.mul_mem h2 huU

/-- Membership in the product box of a *given* `T`-`U` decomposition, i.e. the decomposition is
unique when `T ⊓ U = 1`. -/
theorem prodBox_mem_iff_of_decomp {T U : Subgroup SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {ε : ℝ} {x a b : SL3}
    (ha : a ∈ T) (hb : b ∈ U) (h : a * b = x) :
    x ∈ prodBox T U ε ↔ a ∈ V ε ∧ b ∈ V ε := by
  constructor
  · intro hx
    rw [prodBox, Set.mem_mul] at hx
    obtain ⟨a', ha', b', hb', hab⟩ := hx
    rw [Set.mem_inter_iff] at ha' hb'
    obtain ⟨ha'V, ha'T⟩ := ha'
    obtain ⟨hb'V, hb'U⟩ := hb'
    have heq : a * b = a' * b' := h.trans hab.symm
    have haa : a = a' := hT_hU_unique hdisj ha hb ha'T hb'U heq
    have hbb : b = b' := hU_unique_of_decomp hdisj ha hb ha'T hb'U heq
    exact ⟨haa ▸ ha'V, hbb ▸ hb'V⟩
  · rintro ⟨haV, hbV⟩
    exact ⟨a, ⟨haV, ha⟩, b, ⟨hbV, hb⟩, h⟩

/-- The elementary facts about the two parts of the plaque coordinate of a point of a flower. -/
theorem co_decomp_facts {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ) {y : X3}
    (hy : y ∈ hf.Z n) :
    hT T U (hf.co n y) ∈ T ∧ hU T U (hf.co n y) ∈ U ∧
      hT T U (hf.co n y) * hU T U (hf.co n y) = hf.co n y ∧
      hT T U (hf.co n y) ∈ V hf.R ∧ hU T U (hf.co n y) ∈ V hf.R := by
  obtain ⟨a, ha, b, hb, hab⟩ := hf.co_mem n y hy
  have hcoH : hf.co n y ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n y hy)
  have hex : ∃ a ∈ T, ∃ b ∈ U, hf.co n y = a * b := ⟨a, ha.2, b, hb.2, hab.symm⟩
  refine ⟨hT_mem hex, hU_mem hex, hT_mul_hU hex, ?_, ?_⟩
  · rw [hT_eq_of_factor hcop hdisj hcoH ha.2 hb.2 hab]
    exact ha.1
  · rw [hU_eq_of_factor hdisj ha.2 hb.2 hab]
    exact hb.1

/-- `uShift` is the pushforward of `νU y` along `shiftMap`. -/
theorem uShift_eq_map {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}
    (hf : ProdFlowerFam H T U μ) (νU : X3 → MeasureTheory.Measure SL3) (n : ℕ) (y : X3) :
    uShift hf νU n y
      = (νU y).map (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y))) := by
  rw [uShift]
  rw [show (fun u : SL3 => gconj (hT T U (hf.co n y))⁻¹ u * (hU T U (hf.co n y)))
        = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) from by
      funext w
      simp only [shiftMap, gconj, inv_inv]]

/-- The `U`-shape of a product-box flower is the preimage of the ball `V R ∩ U` under
`shiftMap t u₀`. -/
theorem shapeU_eq_shift {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ) {y : X3}
    (hy : y ∈ hf.Z n) :
    shape (hf.mU n) U y
      = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) ⁻¹' (V hf.R ∩ (U : Set SL3)) := by
  obtain ⟨htT, huU, hdec, htV, huV⟩ := co_decomp_facts hTH hUH hcop hdisj hf n hy
  rw [hf.shapeU n y hy]
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hgU, hgco⟩
    have hgU' : shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g ∈ U :=
      (shiftMap_mem_U_iff hnorm htT huU g).mpr hgU
    have hco' : g * hf.co n y
        = hT T U (hf.co n y) * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g := by
      rw [show g * hf.co n y
            = g * (hT T U (hf.co n y) * hU T U (hf.co n y)) by rw [hdec], shiftMap_mul]
    have hprodm : hT T U (hf.co n y)
        * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g ∈ prodBox T U hf.R := by
      rw [← hco']; exact hgco
    have hV := (prodBox_mem_iff_of_decomp hdisj htT hgU' rfl).mp hprodm
    exact ⟨hV.2, hgU'⟩
  · rintro ⟨hV, hU'⟩
    have hgU : g ∈ U := (shiftMap_mem_U_iff hnorm htT huU g).mp hU'
    have hco' : g * hf.co n y
        = hT T U (hf.co n y) * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g := by
      rw [show g * hf.co n y
            = g * (hT T U (hf.co n y) * hU T U (hf.co n y)) by rw [hdec], shiftMap_mul]
    have hprodm : hT T U (hf.co n y)
        * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g ∈ prodBox T U hf.R :=
      (prodBox_mem_iff_of_decomp hdisj htT hU' rfl).mpr ⟨htV, hV⟩
    exact ⟨hgU, by rw [hco']; exact hprodm⟩

/-- On the `U`-shape, the `U`-part of the coordinate of `w • y` is `shiftMap t u₀ w`. -/
theorem hU_co_eq_shift {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ) {y : X3}
    (hy : y ∈ hf.Z n) :
    ∀ g ∈ shape (hf.mU n) U y,
      hU T U (hf.co n (g • y)) = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g := by
  intro g hg
  obtain ⟨htT, huU, hdec, htV, huV⟩ := co_decomp_facts hTH hUH hcop hdisj hf n hy
  have hgU : g ∈ U := hg.1
  have hgmU : g • y ∈ atom (hf.mU n) y := hg.2
  have hgmH : g • y ∈ atom (hf.mH n) y := atom_subset (hf.alignU n) y hgmU
  have hco : hf.co n (g • y) = g * hf.co n y := hf.co_smul n y hy g (hUH hgU) hgmH
  have hshiftU : shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g ∈ U :=
    (shiftMap_mem_U_iff hnorm htT huU g).mpr hgU
  have hco' : hf.co n (g • y)
      = hT T U (hf.co n y) * shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g := by
    rw [hco, show g * hf.co n y
          = g * (hT T U (hf.co n y) * hU T U (hf.co n y)) by rw [hdec], shiftMap_mul]
  rw [hco', hU_eq_of_factor hdisj htT hshiftU rfl]

theorem uAvg_eq {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ) (νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) {B : Set Work.EKLContract.SL3} (hB : @MeasurableSet Work.EKLContract.SL3 (borel Work.EKLContract.SL3) B) {y : Work.EKLContract.X3} (hy : y ∈ hf.Z n) : Work.EKLRelProduct.uAvg hf νU n y B = ((Work.EKLRelProduct.uShift hf νU n y) (B ∩ (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)))).toReal / ((Work.EKLRelProduct.uShift hf νU n y) (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3))).toReal := by
  classical
  have hmap : uShift hf νU n y
      = (νU y).map (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y))) :=
    uShift_eq_map hf νU n y
  have hshape := shapeU_eq_shift hTH hUH hnorm hcop hdisj hf n hy
  have hψ : MeasurableEmbedding (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y))) :=
    measurableEmbedding_shiftMap _ _
  have hgc : ∀ g ∈ shape (hf.mU n) U y,
      hU T U (hf.co n (g • y)) = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) g :=
    hU_co_eq_shift hTH hUH hnorm hcop hdisj hf n hy
  have hgmeas : Measurable (fun w : SL3 => hU T U (hf.co n (w • y))) :=
    (hf.meas_up n).comp (continuous_id.smul continuous_const).measurable
  have hsetB : shape (hf.mU n) U y ∩ (fun w : SL3 => hU T U (hf.co n (w • y))) ⁻¹' B
      = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) ⁻¹'
          (B ∩ (V hf.R ∩ (U : Set SL3))) := by
    rw [Set.preimage_inter, ← hshape]
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hwS, hwB⟩
      rw [hgc w hwS] at hwB
      exact ⟨hwB, hwS⟩
    · rintro ⟨hwB, hwS⟩
      exact ⟨hwS, by rwa [hgc w hwS]⟩
  rw [uAvg, hmap]
  have hstep :=
    setIntegral_indicator_comp_eq_toReal (ν := νU y) hgmeas hB (shape (hf.mU n) U y)
  rw [hstep]
  rw [MeasurableEmbedding.map_apply hψ, MeasurableEmbedding.map_apply hψ]
  rw [hsetB, hshape]

end Work.EKLRelProduct
