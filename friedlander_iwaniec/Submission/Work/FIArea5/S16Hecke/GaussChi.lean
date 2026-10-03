/-
# `GaussChi`: the character `χ` on the Gaussian residue ring `ℤ[i]/(4d)`.

Properties of the periodic weight `FR d χ` (multiplicativity, vanishing off the units, unit
modulus one) used in the proof of the Gauss-sum identity.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.GaussBasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

namespace GaussBasic

variable {d : ℕ} [NeZero (4 * d)]

/-! ## The projections of `IsCharMod4d` -/

lemma IsCharMod4d.one {chi : GaussianInt → ℂ} (h : Work.FITop3.IsCharMod4d d chi) :
    chi 1 = 1 := h.1

lemma IsCharMod4d.mul {chi : GaussianInt → ℂ} (h : Work.FITop3.IsCharMod4d d chi)
    (z w : GaussianInt) : chi (z * w) = chi z * chi w := h.2.1 z w

lemma IsCharMod4d.norm_le {chi : GaussianInt → ℂ} (h : Work.FITop3.IsCharMod4d d chi)
    (z : GaussianInt) : ‖chi z‖ ≤ 1 := h.2.2.1 z

lemma IsCharMod4d.periodic {chi : GaussianInt → ℂ} (h : Work.FITop3.IsCharMod4d d chi)
    {z w : GaussianInt} (hw : ((((4*d:ℕ):ℤ)) : GaussianInt) ∣ (z - w)) : chi z = chi w :=
  h.2.2.2.1 z w hw

lemma IsCharMod4d.zero_of_dvd {chi : GaussianInt → ℂ} (h : Work.FITop3.IsCharMod4d d chi)
    {z : GaussianInt} (hz : ((((4*d:ℕ):ℤ)) : GaussianInt) ∣ z) : chi z = 0 :=
  h.2.2.2.2 z hz

/-- `χ` only depends on the residue class modulo `4d`. -/
lemma chi_eq_of_gOfZI_eq {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    {z w : GaussianInt} (h : gOfZI d z = gOfZI d w) : chi z = chi w :=
  IsCharMod4d.periodic hchi (dvd_of_gOfZI_eq h)

/-! ## `chiR` and `FR` -/

lemma chiR_mul {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    (x y : ZMod (4 * d) × ZMod (4 * d)) :
    chiR d chi (gmul d x y) = chiR d chi x * chiR d chi y := by
  have h : gOfZI d (zOfG d (gmul d x y)) = gOfZI d (zOfG d x * zOfG d y) := by
    rw [gOfZI_zOfG, gOfZI_mul, gOfZI_zOfG, gOfZI_zOfG]
  simp only [chiR]
  rw [chi_eq_of_gOfZI_eq hchi h, IsCharMod4d.mul hchi]

lemma chiR_one {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi) :
    chiR d chi (gone d) = 1 := by
  have h : gOfZI d (zOfG d (gone d)) = gOfZI d (1 : GaussianInt) := by
    rw [gOfZI_zOfG, gOfZI_one]
  simp only [chiR]
  rw [chi_eq_of_gOfZI_eq hchi h, IsCharMod4d.one hchi]

lemma isOddR_mul (x y : ZMod (4 * d) × ZMod (4 * d)) :
    isOddR d (gmul d x y) ↔ isOddR d x ∧ isOddR d y := by
  have h : gOfZI d (zOfG d (gmul d x y)) = gOfZI d (zOfG d x * zOfG d y) := by
    rw [gOfZI_zOfG, gOfZI_mul, gOfZI_zOfG, gOfZI_zOfG]
  simp only [isOddR]
  rw [isOddG_periodic (dvd_of_gOfZI_eq h), isOddG_mul]

/-- Units of the Gaussian residue ring are exactly the classes that are invertible modulo `4d`
in the sense of `IsUnitMod4d`. -/
lemma IsUnitR_iff_IsUnitMod4d {x : ZMod (4 * d) × ZMod (4 * d)} :
    IsUnitR d x ↔ IsUnitMod4d d (zOfG d x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨zOfG d y, ?_⟩
    have h : gOfZI d (zOfG d x * zOfG d y) = gOfZI d (1 : GaussianInt) := by
      rw [gOfZI_mul, gOfZI_zOfG, gOfZI_zOfG, hy, gOfZI_one]
    exact dvd_of_gOfZI_eq h
  · rintro ⟨w, hw⟩
    refine ⟨gOfZI d w, ?_⟩
    have h : gOfZI d (zOfG d x * w) = gOfZI d (1 : GaussianInt) := by
      rw [gOfZI_eq_of_dvd hw, gOfZI_one]
    calc gmul d x (gOfZI d w) = gmul d (gOfZI d (zOfG d x)) (gOfZI d w) := by rw [gOfZI_zOfG]
      _ = gOfZI d (zOfG d x * w) := (gOfZI_mul _ _).symm
      _ = gOfZI d (1 : GaussianInt) := h
      _ = gone d := gOfZI_one

lemma chiR_eq_zero_of_not_unit {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi)
    {x : ZMod (4 * d) × ZMod (4 * d)} (hx : ¬ IsUnitR d x) : chiR d chi x = 0 :=
  hchi.2 (zOfG d x) (fun h => hx (IsUnitR_iff_IsUnitMod4d.mpr h))

lemma isOddR_of_IsUnitR {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnitR d x) :
    isOddR d x := by
  obtain ⟨w, hw⟩ := (IsUnitR_iff_IsUnitMod4d.mp h)
  have h1 : isOddG (zOfG d x * w) := (isOddG_periodic hw).mpr isOddG_one
  exact (isOddG_mul _ _).mp h1 |>.1

lemma chiR_ne_zero_of_unit {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnitR d x) : chiR d chi x ≠ 0 := by
  obtain ⟨y, hy⟩ := h
  intro h0
  have h1 := chiR_mul (chi := chi) hchi x y
  rw [hy, chiR_one hchi] at h1
  rw [h0, zero_mul] at h1
  exact one_ne_zero h1

lemma norm_chiR_eq_one_of_unit {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnitR d x) : ‖chiR d chi x‖ = 1 := by
  obtain ⟨y, hy⟩ := h
  have h1 := chiR_mul (chi := chi) hchi x y
  rw [hy, chiR_one hchi] at h1
  have hnx : ‖chiR d chi x‖ ≤ 1 := IsCharMod4d.norm_le hchi _
  have hny : ‖chiR d chi y‖ ≤ 1 := IsCharMod4d.norm_le hchi _
  have h2 : ‖chiR d chi x‖ * ‖chiR d chi y‖ = 1 := by
    rw [← norm_mul, ← h1, norm_one]
  have hnx0 : 0 ≤ ‖chiR d chi x‖ := norm_nonneg _
  have hny0 : 0 ≤ ‖chiR d chi y‖ := norm_nonneg _
  nlinarith

/-- The periodic weight is multiplicative against a unit. -/
lemma FR_mul_unit {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    {u : ZMod (4 * d) × ZMod (4 * d)} (hu : IsUnitR d u) (x : ZMod (4 * d) × ZMod (4 * d)) :
    FR d chi (gmul d x u) = FR d chi x * chiR d chi u := by
  have hu' : isOddR d u := isOddR_of_IsUnitR hu
  have hmul' : isOddR d (gmul d x u) ↔ isOddR d x :=
    ⟨fun h => (isOddR_mul x u).mp h |>.1, fun h => (isOddR_mul x u).mpr ⟨h, hu'⟩⟩
  by_cases hx : isOddR d x
  · simp only [FR]
    rw [if_pos (hmul'.mpr hx), if_pos hx, chiR_mul hchi]
  · simp only [FR]
    rw [if_neg (fun h => hx (hmul'.mp h)), if_neg hx, zero_mul]

end GaussBasic

end

end Work.FIArea5.S16Hecke
