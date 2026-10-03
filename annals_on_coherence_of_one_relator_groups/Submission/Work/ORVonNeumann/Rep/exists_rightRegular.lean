/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The right regular representation of a countable group on `ℓ²(G)`

For a countable group `G` the assignment
`(ρ g f) (x) = f (x * g)` defines an operator on `ℓ²(G)`; the resulting map
`ρ : G →* B(ℓ²(G))` is the (right) regular representation.  It is unitary, and
in a countable group the operators `ρ g` are injective.

This module proves `Work.ORVonNeumann.Rep.exists_rightRegular`, whose statement is the
existence of this representation together with the three properties needed downstream
(the adjoint of `ρ g` is `ρ g⁻¹`, each `ρ g` is injective, and `ρ g` is given by
composition with `· * g`).

The technical core is the general fact recorded as
`Work.ORVonNeumann.Rep.compMeasurePreserving_congr_ae`: composition of `L^p` functions with
two a.e. equal functions gives the same result.  All the `a.e.`-identifications in the
multiplicativity / unitarity of `ρ` are reduced to pointwise identities via it.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep

open MeasureTheory

namespace Work.ORVonNeumann.Rep

section General

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {μb : Measure β}
variable {E : Type*} [NormedAddCommGroup E] {p : ENNReal}

/-- Composition of an `L^p` function with two a.e. equal functions gives the same result.
(Only the a.e. statement matters: if `f a = f' a` then also `x (f a) = x (f' a)`.) -/
theorem compMeasurePreserving_congr_ae {f f' : α → β} (h : f =ᵐ[μ] f')
    (hf : MeasurePreserving f μ μb) (hf' : MeasurePreserving f' μ μb) (x : Lp E p μb) :
    Lp.compMeasurePreserving f hf x = Lp.compMeasurePreserving f' hf' x := by
  refine Lp.ext ?_
  have h1 : (x : β → E) ∘ f =ᵐ[μ] (x : β → E) ∘ f' :=
    h.mono (fun a ha => by exact congrArg _ ha)
  exact (Lp.coeFn_compMeasurePreserving x hf).trans
    (h1.trans (Lp.coeFn_compMeasurePreserving x hf').symm)

end General

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The operator of the right regular representation of `G` on `ℓ²(G)` attached to `g`: the
composition `f ↦ f ∘ (· * g)` with the (measure preserving) right translation by `g`. -/
noncomputable def rightRegOp (g : G) : boundedEnd G :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun h : G => h * g)
    (measurePreserving_mul_right (Measure.count : Measure G) g)).toContinuousLinearMap

omit [Countable G] [MeasurableSingletonClass G] in
/-- `rightRegOp g` is composition with the right translation `· * g`. -/
theorem rightRegOp_apply (g : G) (f : l2 G) :
    rightRegOp g f =
      Lp.compMeasurePreserving (fun h : G => h * g)
        (measurePreserving_mul_right (Measure.count : Measure G) g) f := rfl

omit [Countable G] [MeasurableSingletonClass G] in
/-- `rightRegOp` is multiplicative with the covariant order: `ρ g (ρ h f) = ρ (g * h) f`. -/
theorem rightRegOp_mul_apply (g h : G) (f : l2 G) :
    rightRegOp g (rightRegOp h f) = rightRegOp (g * h) f := by
  rw [rightRegOp_apply, rightRegOp_apply, rightRegOp_apply]
  rw [← Lp.compMeasurePreserving_comp_apply (p := 2) (E := ℂ)
      (μ := (Measure.count : Measure G)) (μb := (Measure.count : Measure G))
      (μc := (Measure.count : Measure G)) f
      (measurePreserving_mul_right (Measure.count : Measure G) h)
      (measurePreserving_mul_right (Measure.count : Measure G) g)]
  exact compMeasurePreserving_congr_ae (f := fun a : G => (a * g) * h)
    (f' := fun a : G => a * (g * h)) (by filter_upwards with a; exact mul_assoc a g h) _ _ f

omit [Countable G] [MeasurableSingletonClass G] in
/-- `rightRegOp 1` is the identity operator. -/
theorem rightRegOp_one_apply (f : l2 G) : rightRegOp (1 : G) f = f := by
  rw [rightRegOp_apply]
  rw [compMeasurePreserving_congr_ae (f := fun h : G => h * 1) (f' := id)
    (by filter_upwards with a; simp) _ _ f]
  exact Lp.compMeasurePreserving_id_apply f

omit [Countable G] [MeasurableSingletonClass G] in
/-- `rightRegOp g` is an isometry of `ℓ²(G)`. -/
theorem rightRegOp_isometry (g : G) : Isometry (rightRegOp g) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro f
  rw [rightRegOp_apply, Lp.norm_compMeasurePreserving]

omit [Countable G] [MeasurableSingletonClass G] in
/-- `rightRegOp g` is injective. -/
theorem rightRegOp_injective (g : G) : Function.Injective (rightRegOp g) :=
  (rightRegOp_isometry g).injective

omit [Countable G] [MeasurableSingletonClass G] in
/-- The adjoint of `rightRegOp g` is `rightRegOp g⁻¹`, i.e. `rightRegOp` respects the
involution (`rightRegOp` is unitary). -/
theorem rightRegOp_star (g : G) : star (rightRegOp g) = rightRegOp g⁻¹ := by
  have hI : Isometry (rightRegOp g) := rightRegOp_isometry g
  have hadj : ContinuousLinearMap.adjoint (rightRegOp g) * rightRegOp g = 1 := by
    have hbase : ContinuousLinearMap.adjoint (rightRegOp g) ∘SL rightRegOp g = 1 :=
      (ContinuousLinearMap.isometry_iff_adjoint_comp_self (rightRegOp g)).mp hI
    ext f
    rw [mul_apply_eq_comp, ← hbase]
    rfl
  have hmul : rightRegOp g * rightRegOp g⁻¹ = 1 := by
    refine ContinuousLinearMap.ext fun f => ?_
    show rightRegOp g (rightRegOp g⁻¹ f) = f
    rw [rightRegOp_mul_apply, mul_inv_cancel]
    exact rightRegOp_one_apply f
  calc star (rightRegOp g)
      = star (rightRegOp g) * 1 := (mul_one _).symm
    _ = star (rightRegOp g) * (rightRegOp g * rightRegOp g⁻¹) := by rw [hmul]
    _ = (star (rightRegOp g) * rightRegOp g) * rightRegOp g⁻¹ := (mul_assoc _ _ _).symm
    _ = (ContinuousLinearMap.adjoint (rightRegOp g) * rightRegOp g) * rightRegOp g⁻¹ := by
          rw [ContinuousLinearMap.star_eq_adjoint]
    _ = 1 * rightRegOp g⁻¹ := by rw [hadj]
    _ = rightRegOp g⁻¹ := one_mul _

/-- The right regular representation of `G` on `ℓ²(G)` as a monoid homomorphism. -/
noncomputable def rightRegHom : G →* boundedEnd G where
  toFun := rightRegOp
  map_one' := by
    refine ContinuousLinearMap.ext fun f => ?_
    exact rightRegOp_one_apply f
  map_mul' := by
    intro g h
    refine ContinuousLinearMap.ext fun f => ?_
    rw [mul_apply_eq_comp]
    exact (rightRegOp_mul_apply g h f).symm

/-- **The right regular representation exists.**  There is a monoid homomorphism
`ρ : G →* B(ℓ²(G))` with `star (ρ g) = ρ g⁻¹`, with each `ρ g` injective, and such that
`ρ g` is composition with the right translation `· * g`. -/
theorem exists_rightRegular {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : ∃ ρ : G →* (Work.ORVonNeumann.boundedEnd G), (∀ g : G, star (ρ g) = ρ g⁻¹) ∧ (∀ g : G, Function.Injective (ρ g)) ∧ (∀ (g : G) (f : Work.ORVonNeumann.l2 G), ρ g f = MeasureTheory.Lp.compMeasurePreserving (fun h : G => h * g) (MeasureTheory.measurePreserving_mul_right (MeasureTheory.Measure.count : MeasureTheory.Measure G) g) f) := by
  exact ⟨rightRegHom, fun g => rightRegOp_star g, fun g => rightRegOp_injective g,
    fun g f => rightRegOp_apply g f⟩

end Work.ORVonNeumann.Rep
