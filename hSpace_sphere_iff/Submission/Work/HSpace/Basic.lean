/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# H-space structures transported along homeomorphisms, and unit spheres

This file collects the elementary infrastructure used to build H-space structures on unit
spheres:

* `Submission.HSpace.of_homeomorph` (and `Submission.hSpace_transport`): an `HSpace` structure
  transports across a homeomorphism.
* `Submission.sphereCongr`: an isometry equivalence fixing `0` restricts to the unit spheres.
* `Submission.hSpace_unitSphere`: the unit sphere of a normed additive group carrying a
  multiplication with strictly multiplicative norm, strict two-sided unit and continuous
  multiplication is an H-space.  This is the version of `IsTopologicalGroup.toHSpace` that does
  not require associativity, and is what makes the octonion unit sphere `S⁷` an H-space.
-/
import Mathlib

open scoped unitInterval
open ContinuousMap

namespace Submission

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport an `HSpace` structure across a homeomorphism `φ : Y ≃ₜ X`. -/
@[instance_reducible]
noncomputable def HSpace.of_homeomorph (φ : Y ≃ₜ X) (h : HSpace Y) : HSpace X where
  hmul := ⟨fun p => φ (h.hmul (φ.symm p.1, φ.symm p.2)), by fun_prop⟩
  e := φ h.e
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk]
    rw [φ.symm_apply_apply h.e, h.hmul_e_e]
  eHmul :=
  { toFun := fun p : I × X => φ (h.eHmul (p.1, φ.symm p.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun x => by
      simp only [ContinuousMap.coe_mk, HomotopyLike.map_zero_left h.eHmul (φ.symm x),
        ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
        ContinuousMap.id_apply, φ.symm_apply_apply]
    map_one_left := fun x => by
      simp only [HomotopyLike.map_one_left h.eHmul (φ.symm x), ContinuousMap.id_apply,
        φ.apply_symm_apply]
    prop' := fun t x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [ContinuousMap.coe_mk, HomotopyRel.eq_fst h.eHmul t (Set.mem_singleton _),
        ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
        ContinuousMap.id_apply, φ.symm_apply_apply] }
  hmulE :=
  { toFun := fun p : I × X => φ (h.hmulE (p.1, φ.symm p.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun x => by
      simp only [ContinuousMap.coe_mk, HomotopyLike.map_zero_left h.hmulE (φ.symm x),
        ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
        ContinuousMap.id_apply, φ.symm_apply_apply]
    map_one_left := fun x => by
      simp only [HomotopyLike.map_one_left h.hmulE (φ.symm x), ContinuousMap.id_apply,
        φ.apply_symm_apply]
    prop' := fun t x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [ContinuousMap.coe_mk, HomotopyRel.eq_fst h.hmulE t (Set.mem_singleton _),
        ContinuousMap.comp_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply,
        ContinuousMap.id_apply, φ.symm_apply_apply] }

/-- The unit sphere of an H-space is an H-space, as a `Nonempty` statement. -/
theorem hSpace_transport (φ : Y ≃ₜ X) (h : Nonempty (HSpace Y)) : Nonempty (HSpace X) :=
  h.map (HSpace.of_homeomorph φ)

/-- An isometry equivalence mapping `0` to `0` restricts to the unit spheres. -/
noncomputable def sphereCongr {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (e : E ≃ᵢ F) (h0 : e 0 = 0) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by
    show dist x 0 = 1 ↔ dist (e x) 0 = 1
    rw [← h0, e.dist_eq])

/-- A linear isometry equivalence restricts to the unit spheres. -/
noncomputable def sphereCongrLIE {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [Module ℝ E] [Module ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 :=
  sphereCongr e.toIsometryEquiv (by simp)

section UnitSphere

variable {𝕆 : Type*} [NormedAddCommGroup 𝕆] [Mul 𝕆] [One 𝕆]

omit [One 𝕆] in
/-- The unit sphere is closed under a multiplication whose norm is multiplicative. -/
theorem mem_unitSphere_mul (hnorm : ∀ x y : 𝕆, ‖x * y‖ = ‖x‖ * ‖y‖) {x y : 𝕆}
    (hx : x ∈ Metric.sphere (0 : 𝕆) 1) (hy : y ∈ Metric.sphere (0 : 𝕆) 1) :
    x * y ∈ Metric.sphere (0 : 𝕆) 1 := by
  have hx' : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hy' : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  simp [hnorm, hx', hy']

/-- The multiplication on the unit sphere inherited from a norm-multiplicative multiplication. -/
@[instance_reducible]
noncomputable def unitSphereMul (hnorm : ∀ x y : 𝕆, ‖x * y‖ = ‖x‖ * ‖y‖) :
    Mul (Metric.sphere (0 : 𝕆) 1) :=
  ⟨fun x y => ⟨x.1 * y.1, mem_unitSphere_mul hnorm x.2 y.2⟩⟩

/-- `1` lies on the unit sphere when `‖1‖ = 1`. -/
@[instance_reducible]
noncomputable def unitSphereOne (h1 : ‖(1 : 𝕆)‖ = 1) : One (Metric.sphere (0 : 𝕆) 1) :=
  ⟨⟨1, by simpa [Metric.mem_sphere, dist_zero_right] using h1⟩⟩

set_option linter.style.haveILetI false in
/-- The unit sphere of a normed group with a strictly unital, norm-multiplicative multiplication.
This is the non-associative analogue of the unit sphere of a normed ring. -/
theorem hSpace_unitSphere [ContinuousMul 𝕆] (h1 : ‖(1 : 𝕆)‖ = 1)
    (hone : ∀ x : 𝕆, 1 * x = x) (hmul : ∀ x : 𝕆, x * 1 = x)
    (hnorm : ∀ x y : 𝕆, ‖x * y‖ = ‖x‖ * ‖y‖) :
    Nonempty (HSpace (Metric.sphere (0 : 𝕆) 1)) := by
  letI : MulOneClass (Metric.sphere (0 : 𝕆) 1) :=
    { mul := fun x y => ⟨x.1 * y.1, mem_unitSphere_mul hnorm x.2 y.2⟩
      one := ⟨1, by simpa [Metric.mem_sphere, dist_zero_right] using h1⟩
      one_mul := fun x => Subtype.ext (hone x.1)
      mul_one := fun x => Subtype.ext (hmul x.1) }
  letI : ContinuousMul (Metric.sphere (0 : 𝕆) 1) :=
    ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) _⟩
  exact ⟨IsTopologicalGroup.toHSpace _⟩

end UnitSphere

end Submission
