import Mathlib
import Submission.Work.Transgression.Pieces
import Submission.Work.Transgression.Rank
import Submission.Work.Transgression.Algebra
import Submission.Work.Agree.kunnethInj
import Submission.Work.Agree.kunnethSpan
import Submission.Work.Cohomology.sphereCohomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# `Work.Transgression.KunnethInjQ2` — Künneth injectivity for `S³ × S³`

The lemma says: a class in `H³(S³ × S³; ℤ)` (quaternionic model `S³ = Sp(1)` of
`Work.CharacteristicClasses`) whose pullbacks along *both* factor inclusions
`sectA (v) = (v, 1)` and `sectB (v) = (1, v)` vanish is zero.

The proof is the one prescribed in `Submission/Work/Agree/BOTTHOPF_PLAN.md`:

* `Work.Transgression.Sph33Rank` (proved in `Transgression/Rank.lean`) gives
  `H³(S³ × S³; ℤ) ≅ ℤ²`;
* the four pairings between the factor pullbacks `prjA*`, `prjB*` and the factor
  inclusions `sectA*`, `sectB*` form the `2 × 2` identity matrix: `sectA* ∘ prjA* = id`
  and `sectB* ∘ prjB* = id` on the nose, while the two cross composites `prjB ∘ sectA`,
  `prjA ∘ sectB` are *constant* maps, whose pullbacks vanish in degree `3`
  (`Work.Agree.HMap_const_eq_zero`, `H³(pt) = 0`);
* `H³(S³; ℤ) ≅ ℤ` (the quaternionic model, via `Work.CharacteristicClasses.s3Homeo`
  and `Work.Cohomology.sphereCohomologyTop`).

The abstract `ℤ`-module input — a split injection `ℤ² → M` into a module isomorphic
to `ℤ²` is bijective, so the two factor restrictions jointly kill only `0` — is
`Work.Agree.span_eq_bot` (`Submission/Work/Agree/kunnethSpan.lean`), which packages
the rank statement exactly in this shape.
-/

namespace Work.Transgression

open Work.TangentClasses CategoryTheory

noncomputable section

/-! ## 1. The two projections, the two factor inclusions and their four pairings -/

/-- `prjA ∘ sectA = id` (on the nose). -/
lemma prjA_comp_sectA : prjA.comp sectA = ContinuousMap.id _ := by
  apply ContinuousMap.ext; intro v; rfl

/-- `prjB ∘ sectB = id` (on the nose). -/
lemma prjB_comp_sectB : prjB.comp sectB = ContinuousMap.id _ := by
  apply ContinuousMap.ext; intro v; rfl

/-- `prjB ∘ sectA` is the constant map at `1`. -/
lemma prjB_comp_sectA :
    prjB.comp sectA = ContinuousMap.const _ (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

/-- `prjA ∘ sectB` is the constant map at `1`. -/
lemma prjA_comp_sectB :
    prjA.comp sectB = ContinuousMap.const _ (Work.CharacteristicClasses.s3One) := by
  apply ContinuousMap.ext; intro v; rfl

/-- The pullback along `sectA` is a left inverse of the pullback along `prjA`. -/
theorem sectA_comp_prjA :
    (HMap sectA 3).hom.comp (HMap prjA 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp,
    ← HMap_comp (B₁ := (Work.CharacteristicClasses.S3))
      (B₂ := (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))
      (B₃ := (Work.CharacteristicClasses.S3)) sectA prjA 3,
    prjA_comp_sectA, HMap_id]
  rfl

/-- The pullback along `sectB` is a left inverse of the pullback along `prjB`. -/
theorem sectB_comp_prjB :
    (HMap sectB 3).hom.comp (HMap prjB 3).hom = LinearMap.id := by
  rw [← ModuleCat.hom_comp,
    ← HMap_comp (B₁ := (Work.CharacteristicClasses.S3))
      (B₂ := (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))
      (B₃ := (Work.CharacteristicClasses.S3)) sectB prjB 3,
    prjB_comp_sectB, HMap_id]
  rfl

/-- The first cross pullback vanishes in degree `3`: `sectA^* ∘ prjB^* = 0`. -/
theorem sectA_prjB_zero :
    ((HMap sectA 3).hom).comp ((HMap prjB 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectA prjB 3
  rw [prjB_comp_sectA] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-- The second cross pullback vanishes in degree `3`: `sectB^* ∘ prjA^* = 0`. -/
theorem sectB_prjA_zero :
    ((HMap sectB 3).hom).comp ((HMap prjA 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp sectB prjA 3
  rw [prjA_comp_sectB] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact Work.Agree.HMap_const_eq_zero (Work.CharacteristicClasses.s3One) 2 x

/-! ## 2. The identification `H³(S³; ℤ) ≅ ℤ` -/

/-- **`H³(S³; ℤ) ≅ ℤ`** in the quaternionic model, obtained from the Euclidean sphere model
through `Work.CharacteristicClasses.s3Homeo` and `Work.Cohomology.sphereCohomologyTop`. -/
def s3CohIso : ↥(Work.Thom.Coh ℤ 3 Work.CharacteristicClasses.S3) ≃ₗ[ℤ] ℤ :=
  ((Work.Cohomology.cohomologyIso_of_homotopyEquiv
      (Work.CharacteristicClasses.s3Homeo.toHomotopyEquiv) 3).some ≪≫
    (Work.Cohomology.sphereCohomologyTop 3 (by norm_num)).some).toLinearEquiv

end

end Work.Transgression

namespace Work.Transgression

/-- **Künneth injectivity for `S³ × S³` in the quaternionic model**: a class in
`H³(S³ × S³; ℤ)` whose pullbacks along the two factor inclusions `sectA`, `sectB` vanish is zero.

This is the rank statement `H³(S³ × S³; ℤ) ≅ ℤ²` (`Work.Transgression.Sph33Rank`) combined with the
four pairings `sectA^* ∘ prjA^* = id`, `sectB^* ∘ prjB^* = id`, `sectA^* ∘ prjB^* = 0`,
`sectB^* ∘ prjA^* = 0` and `H³(S³; ℤ) ≅ ℤ` (`s3CohIso`): see `Work.Agree.span_eq_bot`. -/
theorem KunnethInjQ2 (x : ↥(Work.Thom.Coh ℤ 3 (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3)))
    (h1 : (Work.TangentClasses.HMap Work.Transgression.sectA 3).hom x = 0)
    (h2 : (Work.TangentClasses.HMap Work.Transgression.sectB 3).hom x = 0) : x = 0 := by
  obtain ⟨e⟩ := Sph33Rank
  exact Work.Agree.span_eq_bot
    (A := (Work.TangentClasses.HMap Work.Transgression.prjA 3).hom)
    (B := (Work.TangentClasses.HMap Work.Transgression.prjB 3).hom)
    (A' := (Work.TangentClasses.HMap Work.Transgression.sectA 3).hom)
    (B' := (Work.TangentClasses.HMap Work.Transgression.sectB 3).hom)
    sectA_comp_prjA sectA_prjB_zero sectB_prjA_zero sectB_comp_prjB
    (e.trans (LinearEquiv.finTwoArrow ℤ ℤ)) s3CohIso x h1 h2

end Work.Transgression
