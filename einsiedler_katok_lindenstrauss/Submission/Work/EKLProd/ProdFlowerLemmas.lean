import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLC6Core.shape_mass_pos

/-!
# Elementary lemmas about `ProdFlowerFam` (C5b)

See `EKLComp/ProductPlan.md` §9.1: these are the shape/mass facts and the algebraic identities
that make the substitution of step 3 (`Work.EKLProd.nuT_class_of_mem_shape`) *fibre independent*
in the tower identity `Work.EKLProd.slicing_identity_gen`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

section Decomp

variable {H T U : Subgroup SL3}

/-- If `a * b = w` with `a ∈ T`, `b ∈ U` and `w ∈ H`, then `w` has `T`-part `a`. -/
theorem hT_eq_of_factor (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {w a b : SL3} (hw : w ∈ H)
    (haT : a ∈ T) (hbU : b ∈ U) (h : a * b = w) : hT T U w = a := by
  obtain ⟨g, hgT, u, huU, hgu⟩ := hcop w hw
  have hdec : hT T U w * hU T U w = w := hT_mul_hU ⟨g, hgT, u, huU, hgu⟩
  exact hT_hU_unique hdisj (hT_mem ⟨g, hgT, u, huU, hgu⟩) (hU_mem ⟨g, hgT, u, huU, hgu⟩)
    haT hbU (by rw [hdec]; exact h.symm)

theorem hT_mul_left (hTH : T ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {g w : SL3} (hg : g ∈ T) (hw : w ∈ H) :
    hT T U (g * w) = g * hT T U w := by
  obtain ⟨g', hg'T, u', hu'U, hgu'⟩ := hcop w hw
  have hdecw : hT T U w * hU T U w = w := hT_mul_hU ⟨g', hg'T, u', hu'U, hgu'⟩
  refine hT_eq_of_factor hcop hdisj (H.mul_mem (hTH hg) hw)
    (T.mul_mem hg (hT_mem ⟨g', hg'T, u', hu'U, hgu'⟩))
    (hU_mem ⟨g', hg'T, u', hu'U, hgu'⟩) ?_
  rw [mul_assoc, hdecw]

theorem hT_mul_right_U (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hUH : U ≤ H)
    {u z : SL3} (hu : u ∈ U) (hz : z ∈ H) : hT T U (u * z) = hT T U z := by
  obtain ⟨g, hgT, v, hvU, hgv⟩ := hcop z hz
  have hz_eq : hT T U z = g := hT_eq_of_factor hcop hdisj hz hgT hvU hgv.symm
  have hconj : g⁻¹ * u * g ∈ U := by
    have h := hnorm g⁻¹ (T.inv_mem hgT) u hu
    simpa using h
  have hfac : g * ((g⁻¹ * u * g) * v) = u * z := by rw [hgv]; group
  have h' : hT T U (u * z) = g :=
    hT_eq_of_factor hcop hdisj (H.mul_mem (hUH hu) hz) hgT (U.mul_mem hconj hvU) hfac
  rw [h', hz_eq]

end Decomp

/-! ## The shape has finite positive leafwise mass a.e. -/

theorem prodFlower_shape_mass {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup SL3} (hf : ProdFlowerFam H T U μ)
    {νH : X3 → MeasureTheory.Measure SL3} {XH : Set X3}
    (hνH : IsLeafwise μ H νH XH) (n : ℕ) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      0 < (νH x) (shape (hf.mH n) H x) ∧
        (νH x) (shape (hf.mH n) H x) < ⊤ := by
  have hXH : ∀ᵐ x ∂μ, x ∈ XH := by
    rw [MeasureTheory.ae_iff]
    exact hνH.conull
  have hXH' : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XH :=
    MeasureTheory.ae_restrict_of_ae hXH
  have hZmeas : MeasurableSet (hf.Z n) :=
    (MeasurableSpace.le_def.mp (hf.plaqH n).1) (hf.Z n) (hf.plaqH n).2.2.1
  have hZ' : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ hf.Z n :=
    MeasureTheory.ae_restrict_mem hZmeas
  filter_upwards [hXH', hZ'] with x hxX hxZ
  exact Work.EKLC6Core.shape_mass_pos hνH (hf.plaqH n) hxX hxZ

/-! ## The `T`-shape is a translate of `V R ∩ T` -/

theorem prodFlower_shapeT_eq {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {x : X3} (hx : x ∈ hf.Z n) :
    shape (hf.mT n) T x
      = (fun a : SL3 => a * (hT T U (hf.co n x))⁻¹) '' (V hf.R ∩ (T : Set SL3)) := by
  obtain ⟨t₀, ht₀, u₀, hu₀, ht₀u₀⟩ := hf.co_mem n x hx
  have hcoH : hf.co n x ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n x hx)
  have hdec : hT T U (hf.co n x) * hU T U (hf.co n x) = hf.co n x :=
    hT_mul_hU ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
  have htT : hT T U (hf.co n x) ∈ T := hT_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
  have huU : hU T U (hf.co n x) ∈ U := hU_mem ⟨t₀, ht₀.2, u₀, hu₀.2, ht₀u₀.symm⟩
  have htV : hT T U (hf.co n x) ∈ V hf.R := by
    have h := hT_eq_of_factor hcop hdisj hcoH ht₀.2 hu₀.2 ht₀u₀
    rw [h]; exact ht₀.1
  have huV : hU T U (hf.co n x) ∈ V hf.R := by
    have h : hU T U (hf.co n x) = u₀ := by
      have h2 : hT T U (hf.co n x) * hU T U (hf.co n x) = t₀ * u₀ := by
        rw [hdec]
        exact ht₀u₀.symm
      rw [hT_eq_of_factor hcop hdisj hcoH ht₀.2 hu₀.2 ht₀u₀] at h2
      exact mul_left_cancel h2
    rw [h]; exact hu₀.1
  rw [hf.shapeT n x hx]
  ext g
  constructor
  · rintro ⟨hgT, a, ha, b, hb, hab⟩
    rw [Set.mem_image]
    have hgt : g * hT T U (hf.co n x) ∈ T := T.mul_mem hgT htT
    have h1 : (g * hT T U (hf.co n x)) * hU T U (hf.co n x) = a * b := by
      rw [mul_assoc, hdec]
      exact hab.symm
    have hfac : a⁻¹ * (g * hT T U (hf.co n x)) = b * (hU T U (hf.co n x))⁻¹ := by
      calc a⁻¹ * (g * hT T U (hf.co n x))
          = a⁻¹ * ((g * hT T U (hf.co n x)) * hU T U (hf.co n x))
              * (hU T U (hf.co n x))⁻¹ := by group
        _ = a⁻¹ * (a * b) * (hU T U (hf.co n x))⁻¹ := by rw [h1]
        _ = b * (hU T U (hf.co n x))⁻¹ := by group
    have h2 : a⁻¹ * (g * hT T U (hf.co n x)) ∈ T := T.mul_mem (T.inv_mem ha.2) hgt
    have h3 : a⁻¹ * (g * hT T U (hf.co n x)) ∈ U := by
      rw [hfac]; exact U.mul_mem hb.2 (U.inv_mem huU)
    have h4 : a⁻¹ * (g * hT T U (hf.co n x)) = 1 := hdisj _ h2 h3
    have h5 : g * hT T U (hf.co n x) = a := by
      have hh := congrArg (fun z => a * z) h4
      simpa [mul_assoc] using hh
    exact ⟨a, ⟨ha.1, ha.2⟩, by rw [← h5]; group⟩
  · rintro ⟨a, ha, rfl⟩
    have hmem : a * hU T U (hf.co n x) ∈ prodBox T U hf.R :=
      ⟨a, ⟨ha.1, ha.2⟩, hU T U (hf.co n x), ⟨huV, huU⟩, rfl⟩
    have key : a * (hT T U (hf.co n x))⁻¹ * hf.co n x = a * hU T U (hf.co n x) := by
      calc a * (hT T U (hf.co n x))⁻¹ * hf.co n x
          = a * (hT T U (hf.co n x))⁻¹
              * (hT T U (hf.co n x) * hU T U (hf.co n x)) := by rw [hdec]
        _ = a * hU T U (hf.co n x) := by group
    refine ⟨T.mul_mem ha.2 (T.inv_mem htT), ?_⟩
    rw [key]
    exact hmem

/-! ## The cancellation identity behind the fibre independence -/

theorem prodFlower_tpart_cancel {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {x : X3} (hx : x ∈ hf.Z n) {h : SL3} (hh : h ∈ shape (hf.mH n) H x) :
    (hT T U h)⁻¹ * hT T U (h * hf.co n x) = hT T U (hf.co n x) := by
  have hH : h ∈ H := hh.1
  obtain ⟨t₀, ht₀, u₀, hu₀, ht₀u₀⟩ := hf.co_mem n x hx
  have hcoH : hf.co n x ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n x hx)
  obtain ⟨gh, hghT, uh, huhU, hghuh⟩ := hcop h hH
  have hdecH : hT T U h * hU T U h = h := hT_mul_hU ⟨gh, hghT, uh, huhU, hghuh⟩
  have hhT : hT T U h ∈ T := hT_mem ⟨gh, hghT, uh, huhU, hghuh⟩
  have hhU : hU T U h ∈ U := hU_mem ⟨gh, hghT, uh, huhU, hghuh⟩
  have hw : hU T U h * hf.co n x ∈ H := H.mul_mem (hUH hhU) hcoH
  have h1 : h * hf.co n x = hT T U h * (hU T U h * hf.co n x) := by
    calc h * hf.co n x = (hT T U h * hU T U h) * hf.co n x := by rw [hdecH]
      _ = hT T U h * (hU T U h * hf.co n x) := by group
  rw [h1, hT_mul_left hTH hcop hdisj hhT hw,
    hT_mul_right_U hnorm hcop hdisj hUH hhU hcoH]
  group

end Work.EKLProd
