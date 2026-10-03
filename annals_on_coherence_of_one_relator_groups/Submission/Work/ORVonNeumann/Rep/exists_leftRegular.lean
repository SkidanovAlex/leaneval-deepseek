/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The left regular representation of a countable group on `ℓ²(G)`

For a countable group `G` the assignment `(λ g f) (x) = f (g⁻¹ * x)` defines an operator on
`ℓ²(G)`; the resulting map `λ : G →* B(ℓ²(G))` is the (left) regular representation.  It is
unitary (`star (λ g) = λ g⁻¹`), it is given by composition with the measure preserving left
translation `g⁻¹ * ·`, and it generates the group von Neumann algebra
`N(G) = ρ(G)'` of `Work.ORVonNeumann.Rep.GroupVonNeumann`: indeed `λ g` commutes with every
right translation `ρ h` (`(ρ h f) x = f (x * h)`), since
`(λ g (ρ h f)) x = f (g⁻¹ * (x * h)) = (ρ h (λ g f)) x`.

The elementary operator facts about `λ g` mirror those proved for the right regular
representation in `Work.ORVonNeumann.Rep.exists_rightRegular`; the only extra ingredient is the
commutation with `ρ h`.

This module proves `Work.ORVonNeumann.Rep.exists_leftRegular`, the existence of `λ` with the
three properties needed downstream.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann

open MeasureTheory

set_option autoImplicit false

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The operator of the left regular representation of `G` on `ℓ²(G)` attached to `g`: the
composition `f ↦ f ∘ (g⁻¹ * ·)` with the (measure preserving) left translation by `g⁻¹`. -/
noncomputable def leftRegOp (g : G) : Work.ORVonNeumann.boundedEnd G :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun h : G => g⁻¹ * h)
    (measurePreserving_mul_left (Measure.count : Measure G) g⁻¹)).toContinuousLinearMap

omit [Countable G] [MeasurableSingletonClass G] in
/-- `leftRegOp g` is composition with the left translation `g⁻¹ * ·`. -/
theorem leftRegOp_apply (g : G) (f : Work.ORVonNeumann.l2 G) :
    leftRegOp g f =
      Lp.compMeasurePreserving (fun h : G => g⁻¹ * h)
        (measurePreserving_mul_left (Measure.count : Measure G) g⁻¹) f := rfl

omit [Countable G] [MeasurableSingletonClass G] in
/-- `leftRegOp` is multiplicative with the covariant order: `λ g (λ h f) = λ (g * h) f`. -/
theorem leftRegOp_mul_apply (g h : G) (f : Work.ORVonNeumann.l2 G) :
    leftRegOp g (leftRegOp h f) = leftRegOp (g * h) f := by
  rw [leftRegOp_apply, leftRegOp_apply, leftRegOp_apply]
  rw [← Lp.compMeasurePreserving_comp_apply (p := 2) (E := ℂ)
      (μ := (Measure.count : Measure G)) (μb := (Measure.count : Measure G))
      (μc := (Measure.count : Measure G)) f
      (measurePreserving_mul_left (Measure.count : Measure G) h⁻¹)
      (measurePreserving_mul_left (Measure.count : Measure G) g⁻¹)]
  exact compMeasurePreserving_congr_ae (f := fun a : G => h⁻¹ * (g⁻¹ * a))
    (f' := fun a : G => (g * h)⁻¹ * a) (by filter_upwards with a; group) _ _ f

omit [Countable G] [MeasurableSingletonClass G] in
/-- `leftRegOp 1` is the identity operator. -/
theorem leftRegOp_one_apply (f : Work.ORVonNeumann.l2 G) : leftRegOp (1 : G) f = f := by
  rw [leftRegOp_apply]
  rw [compMeasurePreserving_congr_ae (f := fun h : G => (1 : G)⁻¹ * h) (f' := id)
    (by filter_upwards with a; simp) _ _ f]
  exact Lp.compMeasurePreserving_id_apply f

omit [Countable G] [MeasurableSingletonClass G] in
/-- `leftRegOp g` is an isometry of `ℓ²(G)`. -/
theorem leftRegOp_isometry (g : G) : Isometry (leftRegOp g) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro f
  rw [leftRegOp_apply, Lp.norm_compMeasurePreserving]

omit [Countable G] [MeasurableSingletonClass G] in
/-- The adjoint of `leftRegOp g` is `leftRegOp g⁻¹`, i.e. `leftRegOp` respects the involution
(`leftRegOp` is unitary). -/
theorem leftRegOp_star (g : G) : star (leftRegOp g) = leftRegOp g⁻¹ := by
  have hI : Isometry (leftRegOp g) := leftRegOp_isometry g
  have hadj : ContinuousLinearMap.adjoint (leftRegOp g) * leftRegOp g = 1 := by
    have hbase : ContinuousLinearMap.adjoint (leftRegOp g) ∘SL leftRegOp g = 1 :=
      (ContinuousLinearMap.isometry_iff_adjoint_comp_self (leftRegOp g)).mp hI
    ext f
    rw [mul_apply_eq_comp, ← hbase]
    rfl
  have hmul : leftRegOp g * leftRegOp g⁻¹ = 1 := by
    refine ContinuousLinearMap.ext fun f => ?_
    show leftRegOp g (leftRegOp g⁻¹ f) = f
    rw [leftRegOp_mul_apply, mul_inv_cancel]
    exact leftRegOp_one_apply f
  calc star (leftRegOp g)
      = star (leftRegOp g) * 1 := (mul_one _).symm
    _ = star (leftRegOp g) * (leftRegOp g * leftRegOp g⁻¹) := by rw [hmul]
    _ = (star (leftRegOp g) * leftRegOp g) * leftRegOp g⁻¹ := (mul_assoc _ _ _).symm
    _ = (ContinuousLinearMap.adjoint (leftRegOp g) * leftRegOp g) * leftRegOp g⁻¹ := by
          rw [ContinuousLinearMap.star_eq_adjoint]
    _ = 1 * leftRegOp g⁻¹ := by rw [hadj]
    _ = leftRegOp g⁻¹ := one_mul _

omit [Countable G] [MeasurableSingletonClass G] in
/-- The left and right regular representations commute: `λ g * ρ h = ρ h * λ g`. -/
theorem leftRegOp_commute_rightRegOp (g h : G) :
    leftRegOp g * rightRegOp h = rightRegOp h * leftRegOp g := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  rw [leftRegOp_apply, leftRegOp_apply, rightRegOp_apply, rightRegOp_apply]
  rw [← Lp.compMeasurePreserving_comp_apply (p := 2) (E := ℂ)
      (μ := (Measure.count : Measure G)) (μb := (Measure.count : Measure G))
      (μc := (Measure.count : Measure G)) f
      (measurePreserving_mul_right (Measure.count : Measure G) h)
      (measurePreserving_mul_left (Measure.count : Measure G) g⁻¹)]
  rw [← Lp.compMeasurePreserving_comp_apply (p := 2) (E := ℂ)
      (μ := (Measure.count : Measure G)) (μb := (Measure.count : Measure G))
      (μc := (Measure.count : Measure G)) f
      (measurePreserving_mul_left (Measure.count : Measure G) g⁻¹)
      (measurePreserving_mul_right (Measure.count : Measure G) h)]
  exact compMeasurePreserving_congr_ae (f := fun a : G => (g⁻¹ * a) * h)
    (f' := fun a : G => g⁻¹ * (a * h)) (by filter_upwards with a; rw [mul_assoc]) _ _ f

/-- `leftRegOp g` lies in the group von Neumann algebra `N(G)`, i.e. it commutes with every
right translation. -/
theorem leftRegOp_mem_groupVonNeumann (g : G) :
    leftRegOp g ∈ Work.ORVonNeumann.groupVonNeumann G := by
  rw [Work.ORVonNeumann.mem_groupVonNeumann_iff]
  intro h
  exact leftRegOp_commute_rightRegOp g h

/-- The left regular representation of `G` on `ℓ²(G)` as a monoid homomorphism. -/
noncomputable def leftRegHom : G →* Work.ORVonNeumann.boundedEnd G where
  toFun := leftRegOp
  map_one' := by
    refine ContinuousLinearMap.ext fun f => ?_
    exact leftRegOp_one_apply f
  map_mul' := by
    intro g h
    refine ContinuousLinearMap.ext fun f => ?_
    rw [mul_apply_eq_comp]
    exact (leftRegOp_mul_apply g h f).symm

/-- **The left regular representation exists.**  There is a monoid homomorphism
`λ : G →* B(ℓ²(G))` with `star (λ g) = λ g⁻¹`, with each `λ g` in the group von Neumann algebra
`N(G)`, and such that `λ g` is composition with the left translation `g⁻¹ * ·`. -/
theorem exists_leftRegular {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : ∃ lam : G →* (Work.ORVonNeumann.boundedEnd G), (∀ g : G, star (lam g) = lam g⁻¹) ∧ (∀ g : G, lam g ∈ Work.ORVonNeumann.groupVonNeumann G) ∧ (∀ (g : G) (f : Work.ORVonNeumann.l2 G), lam g f = MeasureTheory.Lp.compMeasurePreserving (fun h : G => g⁻¹ * h) (MeasureTheory.measurePreserving_mul_left (MeasureTheory.Measure.count : MeasureTheory.Measure G) g⁻¹) f) := by
  exact ⟨leftRegHom, fun g => leftRegOp_star g, fun g => leftRegOp_mem_groupVonNeumann g,
    fun g f => leftRegOp_apply g f⟩

end Work.ORVonNeumann.Rep
