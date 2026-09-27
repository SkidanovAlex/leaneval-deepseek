import Mathlib
import Submission.Work.EKLProd.ProdPlaqueDefs
import Submission.Work.EKLProd.continuous_uPart
import Submission.Work.EKLComp.PlaqueToolkit
import Submission.Work.EKLProd.inv_entries_bound

/-!
# Coordinates of the decomposition `H = T · U`

Auxiliary API for `EKLProd/prodPlaque_strip.lean`.

For closed subgroups `T, U ≤ H ≤ SL₃(ℝ)` with `T` normalising `U`, `H = T·U` and `T ⊓ U = ⊥`,
`Work.EKLProd.continuous_uPart` produces the continuous `U`-coordinate `ρ` of the (unique)
decomposition `h = t · u`.  Here we package that choice as `uCoord`, derive the companion
`T`-coordinate `tCoord`, and record the two facts used throughout the product-box strip
development:

* uniqueness of the decomposition (`mul_eq_mul_of_mem`), which identifies the chosen coordinates
  with the factors of any decomposition;
* the characterisation of the product box
  `prodBox T U ε = (V ε ∩ T) * (V ε ∩ U)` by the coordinates,
  `h ∈ prodBox T U ε ↔ tCoord h ∈ V ε ∧ uCoord h ∈ V ε` (`mem_prodBox_iff`).

The latter makes the product box **open in `H`** (`isOpen_prodBox_preimage`, and its right
translate `isOpen_prodBox_mul_inv_preimage`), which is what makes the orbit image
`prodPlaque H T U x₀ ε` a plaque algebra for `H`.
-/

open MeasureTheory Topology
open scoped Pointwise
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

variable {H T U : Subgroup SL3}

/-- The chosen `U`-coordinate of the decomposition `H = T · U`. -/
noncomputable def uCoord (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3)) :
    ↥H → ↥U :=
  (continuous_uPart hTH hUH hnorm hcop hdisj hHc hTc hUc).choose

theorem uCoord_continuous (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3)) :
    Continuous (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc) :=
  (continuous_uPart hTH hUH hnorm hcop hdisj hHc hTc hUc).choose_spec.1

theorem uCoord_spec (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) :
    ∃ t ∈ T, (h : SL3) = t * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) :=
  (continuous_uPart hTH hUH hnorm hcop hdisj hHc hTc hUc).choose_spec.2 h

/-- The companion `T`-coordinate: `tCoord h = h · (uCoord h)⁻¹`. -/
noncomputable def tCoord (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) : ↥T :=
  ⟨(h : SL3) * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹, by
    obtain ⟨t, htT, ht⟩ := uCoord_spec hTH hUH hnorm hcop hdisj hHc hTc hUc h
    have hEq : (h : SL3) * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ = t := by
      rw [ht]; group
    rw [hEq]; exact htT⟩

theorem tCoord_continuous (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3)) :
    Continuous (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc) := by
  refine Continuous.subtype_mk ?_ _
  show Continuous (fun h : ↥H =>
    ((h : SL3)) * ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))⁻¹)
  exact continuous_subtype_val.mul
    ((continuous_subtype_val.comp (uCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc)).inv)

theorem tCoord_mul_uCoord (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) :
    (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
      * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) = (h : SL3) := by
  show ((h : SL3) * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹)
      * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) = (h : SL3)
  group

/-- Uniqueness of the decomposition `H = T · U` when `T ⊓ U = ⊥`. -/
theorem mul_eq_mul_of_mem (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {t₁ t₂ : SL3} (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T) {u₁ u₂ : SL3} (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U)
    (h : t₁ * u₁ = t₂ * u₂) : t₁ = t₂ ∧ u₁ = u₂ := by
  have hkey : t₂⁻¹ * t₁ = u₂ * u₁⁻¹ := by
    calc t₂⁻¹ * t₁ = t₂⁻¹ * (t₁ * u₁) * u₁⁻¹ := by group
      _ = t₂⁻¹ * (t₂ * u₂) * u₁⁻¹ := by rw [h]
      _ = u₂ * u₁⁻¹ := by group
  have hkeyT : t₂⁻¹ * t₁ ∈ T := T.mul_mem (T.inv_mem ht₂) ht₁
  have hkeyU : t₂⁻¹ * t₁ ∈ U := by rw [hkey]; exact U.mul_mem hu₂ (U.inv_mem hu₁)
  have hone : t₂⁻¹ * t₁ = 1 := hdisj _ hkeyT hkeyU
  have ht : t₁ = t₂ := by
    have := congrArg (fun x => t₂ * x) hone
    simpa using this
  have hu : u₂ * u₁⁻¹ = 1 := by rw [← hkey]; exact hone
  have hu' : u₂ = u₁ := by
    have := congrArg (fun x => x * u₁) hu
    simpa using this
  exact ⟨ht, hu'.symm⟩

/-- Any decomposition of `h` has the chosen coordinates. -/
theorem eq_coords_of (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {t u : SL3} (ht : t ∈ T) (hu : u ∈ U) (htu : (h : SL3) = t * u) :
    tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h = ⟨t, ht⟩
      ∧ uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h = ⟨u, hu⟩ := by
  have hkey : (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
      * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) = t * u := by
    rw [tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h, htu]
  obtain ⟨h1, h2⟩ := mul_eq_mul_of_mem hdisj (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 ht
    (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 hu hkey
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- Left multiplication by `t ∈ T` multiplies the `T`-coordinate by `t`. -/
theorem tCoord_mul_left (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {t : SL3} (ht : t ∈ T) :
    tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨t * (h : SL3), H.mul_mem (hTH ht) h.2⟩
      = ⟨t * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3),
          T.mul_mem ht (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2⟩ := by
  have hkey : t * (h : SL3)
      = (t * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))
        * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) := by
    rw [mul_assoc, tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h]
  obtain ⟨h1, -⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨t * (h : SL3), H.mul_mem (hTH ht) h.2⟩ : ↥H)
    (T.mul_mem ht (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2)
    (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 (by exact hkey)
  exact h1

/-- Left multiplication by `t ∈ T` does not change the `U`-coordinate. -/
theorem uCoord_mul_left (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {t : SL3} (ht : t ∈ T) :
    uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨t * (h : SL3), H.mul_mem (hTH ht) h.2⟩
      = uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h := by
  have hkey : t * (h : SL3)
      = (t * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))
        * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) := by
    rw [mul_assoc, tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h]
  obtain ⟨-, h2⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨t * (h : SL3), H.mul_mem (hTH ht) h.2⟩ : ↥H)
    (T.mul_mem ht (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2)
    (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 (by exact hkey)
  exact h2

/-- Right multiplication by `w ∈ U` does not change the `T`-coordinate. -/
theorem tCoord_mul_right (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {w : SL3} (hw : w ∈ U) :
    tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨(h : SL3) * w, H.mul_mem h.2 (hUH hw)⟩
      = tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h := by
  have hkey : (h : SL3) * w
      = (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
        * ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) * w) := by
    rw [← tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h, mul_assoc]
  obtain ⟨h1, -⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨(h : SL3) * w, H.mul_mem h.2 (hUH hw)⟩ : ↥H)
    (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2
    (U.mul_mem (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 hw) (by exact hkey)
  exact h1

/-- Right multiplication by `w ∈ U` multiplies the `U`-coordinate by `w`. -/
theorem uCoord_mul_right (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {w : SL3} (hw : w ∈ U) :
    uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨(h : SL3) * w, H.mul_mem h.2 (hUH hw)⟩
      = ⟨(uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) * w,
          U.mul_mem (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 hw⟩ := by
  have hkey : (h : SL3) * w
      = (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
        * ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) * w) := by
    rw [← tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h, mul_assoc]
  obtain ⟨-, h2⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨(h : SL3) * w, H.mul_mem h.2 (hUH hw)⟩ : ↥H)
    (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2
    (U.mul_mem (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 hw) (by exact hkey)
  exact h2

/-- Left multiplication by `u ∈ U` does not change the `T`-coordinate (this uses that `T`
normalises `U`). -/
theorem tCoord_umul_left (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {u : SL3} (hu : u ∈ U) :
    tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨u * (h : SL3), H.mul_mem (hUH hu) h.2⟩
      = tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h := by
  have hw : (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ * u
      * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ U := by
    have hh := hnorm _ (T.inv_mem (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2) u hu
    simpa using hh
  have hkey : u * (h : SL3)
      = (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
        * (((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ * u
            * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))
          * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)) := by
    rw [← tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h]
    group
  obtain ⟨h1, -⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨u * (h : SL3), H.mul_mem (hUH hu) h.2⟩ : ↥H)
    (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2
    (U.mul_mem hw (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2) (by exact hkey)
  exact h1

/-- Left multiplication by `u ∈ U` multiplies the `U`-coordinate by the conjugate
`t⁻¹ u t` (this uses that `T` normalises `U`). -/
theorem uCoord_umul_left (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (h : ↥H) {u : SL3} (hu : u ∈ U) :
    uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨u * (h : SL3), H.mul_mem (hUH hu) h.2⟩
      = ⟨((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ * u
            * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))
          * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3),
          U.mul_mem (by
            have hh := hnorm _ (T.inv_mem (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2) u hu
            simpa using hh)
          (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2⟩ := by
  have hw : (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ * u
      * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ U := by
    have hh := hnorm _ (T.inv_mem (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2) u hu
    simpa using hh
  have hkey : u * (h : SL3)
      = (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)
        * (((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)⁻¹ * u
            * (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3))
          * (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3)) := by
    rw [← tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h]
    group
  obtain ⟨-, h2⟩ := eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc
    (⟨u * (h : SL3), H.mul_mem (hUH hu) h.2⟩ : ↥H)
    (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2
    (U.mul_mem hw (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2) (by exact hkey)
  exact h2

/-- The product box, described by the coordinates of the decomposition `H = T · U`. -/
theorem mem_prodBox_iff (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    {ε : ℝ} (h : ↥H) :
    (h : SL3) ∈ prodBox T U ε ↔
      (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ V ε
        ∧ (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ V ε := by
  constructor
  · rintro ⟨a, ⟨haV, haT⟩, b, ⟨hbV, hbU⟩, hab⟩
    obtain ⟨ht, hu⟩ := mul_eq_mul_of_mem hdisj haT (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2
      hbU (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2 (by
        rw [tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h]; exact hab)
    rw [← ht, ← hu]
    exact ⟨haV, hbV⟩
  · rintro ⟨htV, huV⟩
    exact ⟨(tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3),
      ⟨htV, (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2⟩,
      (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3),
      ⟨huV, (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h).2⟩,
      tCoord_mul_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h⟩

/-- **The product box is open in `H`.** -/
theorem isOpen_prodBox_preimage (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    {ε : ℝ} :
    IsOpen {h : ↥H | (h : SL3) ∈ prodBox T U ε} := by
  have hset : {h : ↥H | (h : SL3) ∈ prodBox T U ε} =
      {h : ↥H | (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ V ε}
        ∩ {h : ↥H | (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : SL3) ∈ V ε} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    exact mem_prodBox_iff hTH hUH hnorm hcop hdisj hHc hTc hUc h
  rw [hset]
  refine IsOpen.inter ?_ ?_
  · exact (Work.EKLComp.isOpen_V ε).preimage
      (continuous_subtype_val.comp (tCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc))
  · exact (Work.EKLComp.isOpen_V ε).preimage
      (continuous_subtype_val.comp (uCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc))

/-- The right translate `(prodBox) · g₀⁻¹`, a neighbourhood of `1` in `H`, is open in `H`. -/
theorem isOpen_prodBox_mul_inv_preimage (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    {ε : ℝ} {g₀ : SL3} (hg₀ : g₀ ∈ prodBox T U ε) :
    IsOpen {h : ↥H | (h : SL3) ∈ prodBox T U ε * ({g₀⁻¹} : Set SL3)} := by
  have hg₀H : g₀ ∈ H := prodBox_subset_H hTH hUH hg₀
  have hbase := isOpen_prodBox_preimage hTH hUH hnorm hcop hdisj hHc hTc hUc (H := H) (T := T)
    (U := U) (ε := ε)
  have himg := (Homeomorph.mulRight (⟨g₀⁻¹, H.inv_mem hg₀H⟩ : ↥H)).isOpenMap _ hbase
  have hgoal : {h : ↥H | (h : SL3) ∈ prodBox T U ε * ({g₀⁻¹} : Set SL3)}
      = (fun a : ↥H => a * (⟨g₀⁻¹, H.inv_mem hg₀H⟩ : ↥H)) '' {h : ↥H | (h : SL3) ∈ prodBox T U ε} := by
    ext h
    constructor
    · intro hh
      change (h : SL3) ∈ prodBox T U ε * ({g₀⁻¹} : Set SL3) at hh
      rw [Set.mem_mul] at hh
      obtain ⟨b, hb, c, hc, hbc⟩ := hh
      rw [Set.mem_singleton_iff] at hc
      subst hc
      refine ⟨⟨b, prodBox_subset_H hTH hUH hb⟩, hb, ?_⟩
      exact Subtype.ext hbc
    · rintro ⟨a, ha, rfl⟩
      change (a : SL3) * g₀⁻¹ ∈ prodBox T U ε * ({g₀⁻¹} : Set SL3)
      rw [Set.mem_mul]
      exact ⟨(a : SL3), ha, g₀⁻¹, rfl, rfl⟩
  rw [hgoal]
  exact himg

end Work.EKLProd

end
