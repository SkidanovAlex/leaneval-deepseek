/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.

# The affine chart of a conjugacy at a parabolic fixed point

This file collects the elementary analysis of the affine chart
`aff z₀ lam u = z₀ + lam * u` and its inverse `affInv z₀ lam z = (z - z₀) / lam`
(`lam ≠ 0`) that is used to transport petal data along an affine conjugacy
(`Work.FatouParabolic2.transport_petalData`).

## Main definitions

* `Work.FatouParabolic2.aff`, `Work.FatouParabolic2.affInv`.

## Main results

* `aff_affInv`, `affInv_aff` — the two maps are mutually inverse;
* `aff_injective`, `mem_aff_image_iff`, `aff_image_eq_preimage` — set-theoretic behaviour;
* `continuous_aff`, `continuous_affInv`, `differentiable_aff`, `differentiable_affInv`.
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- The affine chart `u ↦ z₀ + lam * u` attached to a conjugacy of scale `lam` at `z₀`. -/
def aff (z₀ lam : ℂ) : ℂ → ℂ := fun u => z₀ + lam * u

/-- The inverse `z ↦ (z - z₀) / lam` of the affine chart `aff z₀ lam` (for `lam ≠ 0`). -/
def affInv (z₀ lam : ℂ) : ℂ → ℂ := fun z => (z - z₀) / lam

theorem aff_apply (z₀ lam u : ℂ) : aff z₀ lam u = z₀ + lam * u := rfl

theorem affInv_apply (z₀ lam z : ℂ) : affInv z₀ lam z = (z - z₀) / lam := rfl

@[simp] theorem aff_zero (z₀ lam : ℂ) : aff z₀ lam 0 = z₀ := by simp [aff]

@[simp] theorem affInv_self (z₀ lam : ℂ) : affInv z₀ lam z₀ = 0 := by simp [affInv]

theorem aff_affInv (z₀ lam : ℂ) (hlam : lam ≠ 0) (z : ℂ) :
    aff z₀ lam (affInv z₀ lam z) = z := by
  simp only [aff, affInv]; field_simp; ring

theorem affInv_aff (z₀ lam : ℂ) (hlam : lam ≠ 0) (u : ℂ) :
    affInv z₀ lam (aff z₀ lam u) = u := by
  simp only [aff, affInv]; field_simp; ring

theorem aff_injective (z₀ lam : ℂ) (hlam : lam ≠ 0) : Function.Injective (aff z₀ lam) := by
  intro u v huv
  simp only [aff] at huv
  exact mul_left_cancel₀ hlam (add_left_cancel huv)

theorem continuous_aff (z₀ lam : ℂ) : Continuous (aff z₀ lam) := by
  unfold aff; fun_prop

theorem continuous_affInv (z₀ lam : ℂ) : Continuous (affInv z₀ lam) := by
  unfold affInv; fun_prop

theorem differentiable_aff (z₀ lam : ℂ) : Differentiable ℂ (aff z₀ lam) := by
  unfold aff; fun_prop

theorem differentiable_affInv (z₀ lam : ℂ) : Differentiable ℂ (affInv z₀ lam) := by
  unfold affInv; fun_prop

theorem mem_aff_image_iff (z₀ lam : ℂ) (hlam : lam ≠ 0) (A : Set ℂ) (z : ℂ) :
    z ∈ aff z₀ lam '' A ↔ affInv z₀ lam z ∈ A := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [affInv_aff z₀ lam hlam]; exact hu
  · intro hz
    exact ⟨affInv z₀ lam z, hz, aff_affInv z₀ lam hlam z⟩

theorem aff_image_eq_preimage (z₀ lam : ℂ) (hlam : lam ≠ 0) (A : Set ℂ) :
    aff z₀ lam '' A = affInv z₀ lam ⁻¹' A := by
  ext z
  rw [mem_aff_image_iff z₀ lam hlam A z, Set.mem_preimage]

end

end Work.FatouParabolic2
