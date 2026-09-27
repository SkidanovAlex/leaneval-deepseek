import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_const

/-!
# `Work.KT.Fund.kbi_setup` — setup for `kappa_bott`

Definitions and elementary lemmas for the proof of `Work.KT.Fund.kappa_bott` (private copy, namespace KBI): the coordinate
function `ζ` on the disc together with its conjugate, the normalising factor `c = (1 + |ζ|²)⁻¹`
and their boundary values on the circle `ζ = z`, `ζ̄ = z⁻¹`, `c = 1/2`.

This file is sorry-free; it is the interface on which the remaining pieces of the proof of
`kappa_bott` are built.
-/

namespace Work.KT.Fund
namespace KBI

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## A complex scalar lemma -/

/-- On the unit circle, `z̄ = z⁻¹`. -/
lemma star_eq_inv_of_norm_eq_one (z : ℂ) (h : ‖z‖ = 1) : star z = z⁻¹ := by
  have h1 : z * star z = 1 := by
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, ← Complex.sq_norm, h]
    norm_num
  exact eq_inv_of_mul_eq_one_right h1

/-! ## The coordinate on the disc -/

/-- The coordinate function `ζ` on the disc: `(x, z) ↦ z`. -/
def zc : C(X × Ball ℂ, ℂ) := ⟨fun p => (p.2 : ℂ), by fun_prop⟩

/-- The conjugate coordinate `ζ̄` on the disc. -/
def zcb : C(X × Ball ℂ, ℂ) := ⟨fun p => star (p.2 : ℂ), by fun_prop⟩

/-- The normalising factor `c = (1 + |ζ|²)⁻¹` on the disc. -/
def zcn : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹, by
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro p
      have : (0:ℝ) < 1 + ‖(p.2 : ℂ)‖ ^ 2 := by positivity
      exact_mod_cast this.ne'⟩

@[simp] lemma zc_apply (p : X × Ball ℂ) : zc X p = (p.2 : ℂ) := rfl
@[simp] lemma zcb_apply (p : X × Ball ℂ) : zcb X p = star (p.2 : ℂ) := rfl
@[simp] lemma zcn_apply (p : X × Ball ℂ) :
    zcn X p = ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ := rfl

lemma zcn_ne_zero (p : X × Ball ℂ) :
    zcn X p ≠ 0 := by
  rw [zcn_apply]
  exact inv_ne_zero (by
    have : (0:ℝ) < 1 + ‖(p.2 : ℂ)‖ ^ 2 := by positivity
    exact_mod_cast this.ne')

lemma zc_mul_zcb (p : X × Ball ℂ) :
    zc X p * zcb X p = ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
  simp only [zc_apply, zcb_apply]
  rw [show star (p.2 : ℂ) = (starRingEnd ℂ) (p.2 : ℂ) from rfl, Complex.mul_conj,
    ← Complex.sq_norm]
  push_cast
  ring

/-- `c * (1 + ζ ζ̄) = 1` on the disc. -/
lemma zcn_mul_one_add : zcn X * (1 + zc X * zcb X) = 1 := by
  ext p
  show zcn X p * (1 + zc X p * zcb X p) = 1
  rw [zcn_apply, zc_mul_zcb]
  have h0 : (1 : ℂ) + ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have hp : (0:ℝ) < 1 + ‖(p.2 : ℂ)‖ ^ 2 := by positivity
    have hne : (1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) ≠ 0 := hp.ne'
    push_cast
    exact_mod_cast hne
  have hcast : ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
    push_cast; ring
  rw [hcast]
  exact inv_mul_cancel₀ h0

/-! ## Boundary values -/

lemma bdryRestrict_zc : bdryRestrict X (zc X) = (zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext p
  simp only [bdryRestrict_apply, zc_apply, zUnit_apply]
  rfl

lemma coe_inv_zUnit_apply (p : X × Sph ℂ) :
    (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p = ((p.2 : ℂ))⁻¹ := by
  have h : (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) * (zUnit X : C(X × Sph ℂ, ℂ)) = 1 := by
    simpa using congrArg (fun w : (C(X × Sph ℂ, ℂ))ˣ => (w : C(X × Sph ℂ, ℂ)))
      (Units.inv_mul (zUnit X))
  have hp := DFunLike.congr_fun h p
  rw [ContinuousMap.mul_apply, ContinuousMap.one_apply, zUnit_apply] at hp
  have hp' : (p.2 : ℂ) * (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p = 1 := by rw [mul_comm]; exact hp
  exact eq_inv_of_mul_eq_one_right hp'

lemma bdryRestrict_zcb : bdryRestrict X (zcb X) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) := by
  ext p
  show star ((sphIncl p.2 : Ball ℂ) : ℂ) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p
  rw [coe_inv_zUnit_apply]
  show star (p.2 : ℂ) = ((p.2 : ℂ))⁻¹
  exact star_eq_inv_of_norm_eq_one (p.2 : ℂ) (norm_coe_sph p.2)

lemma star_zUnit_eq_inv :
    star ((zUnit X : C(X × Sph ℂ, ℂ))) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) := by
  ext p
  show star (p.2 : ℂ) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p
  rw [coe_inv_zUnit_apply]
  exact star_eq_inv_of_norm_eq_one (p.2 : ℂ) (norm_coe_sph p.2)

lemma bdryRestrict_zcn : bdryRestrict X (zcn X) = (ContinuousMap.const (X × Sph ℂ) (1/2) :
    C(X × Sph ℂ, ℂ)) := by
  ext p
  show ((1 + ‖((sphIncl p.2 : Ball ℂ) : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ = 1/2
  rw [show ((sphIncl p.2 : Ball ℂ) : ℂ) = (p.2 : ℂ) from rfl, norm_coe_sph p.2]
  norm_num

end

end KBI

end Work.KT.Fund
