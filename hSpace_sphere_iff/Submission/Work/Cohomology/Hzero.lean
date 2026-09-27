/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Degree `0`: evaluation of a `0`-cocycle at a point

The `0`-simplices of the singular complex of a space `X` are the points of `X`
(`TopCat.toSSetObj₀Equiv`), so a `0`-cochain is a function on `X`.  Since there are no boundaries in
degree `0`, this evaluation descends to cohomology and is injective: a cohomology class of degree
`0` is determined by its values at the points of `X`.
-/
import Mathlib
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Cohomology

noncomputable section

/-- Evaluation of a `0`-cochain of the singular complex of `X` at a point of `X`. -/
def HzeroEvalAux (X : TopCat.{0}) :
    Cochain (TopCat.toSSet.obj X) ℚ 0 →ₗ[ℚ] (X → ℚ) where
  toFun f := fun x => f ((TopCat.toSSetObj₀Equiv (X := X)).symm x)
  map_add' f g := by funext x; rfl
  map_smul' r f := by funext x; rfl

/-- Evaluation of a cohomology class of degree `0` at a point of the space.  It is well defined
because there are no boundaries in degree `0`. -/
def HzeroEval (X : TopCat.{0}) : H (TopCat.toSSet.obj X) ℚ 0 →ₗ[ℚ] (X → ℚ) :=
  Submodule.liftQ _ ((HzeroEvalAux X).comp (Submodule.subtype _)) (by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    have hx0 : (x : Cochain (TopCat.toSSet.obj X) ℚ 0) = 0 := by
      have h := hx
      rw [boundariesInCycles, Submodule.mem_comap] at h
      rwa [show boundaries (TopCat.toSSet.obj X) ℚ 0 = ⊥ from rfl, Submodule.mem_bot] at h
    rw [show (Submodule.subtype _) x = 0 from hx0]
    simp)

/-- `HzeroEval` on the class of a cocycle. -/
lemma HzeroEval_mk (X : TopCat.{0}) (u : Cochain (TopCat.toSSet.obj X) ℚ 0)
    (hu : u ∈ cycles (TopCat.toSSet.obj X) ℚ 0) :
    HzeroEval X (H.mk u hu) = fun x => u ((TopCat.toSSetObj₀Equiv (X := X)).symm x) := by
  rw [show H.mk u hu
      = Submodule.mkQ (boundariesInCycles (TopCat.toSSet.obj X) ℚ 0) ⟨u, hu⟩ from rfl]
  rw [Submodule.mkQ_apply, HzeroEval, Submodule.liftQ_apply]
  rfl

/-- A cohomology class of degree `0` is determined by its values at the points of the space. -/
theorem HzeroEval_injective (X : TopCat.{0}) : Function.Injective (HzeroEval X) := by
  intro a b hab
  have h1 : (Quot.out a).1 = (Quot.out b).1 := by
    funext σ
    have h := congrFun hab (TopCat.toSSetObj₀Equiv σ)
    rw [show a = H.mk (Quot.out a).1 (Quot.out a).2 from (Quot.out_eq a).symm,
      show b = H.mk (Quot.out b).1 (Quot.out b).2 from (Quot.out_eq b).symm,
      HzeroEval_mk, HzeroEval_mk] at h
    simpa using h
  have h2 : (Quot.out a : cycles (TopCat.toSSet.obj X) ℚ 0)
      = (Quot.out b : cycles (TopCat.toSSet.obj X) ℚ 0) := Subtype.ext h1
  rw [← Quot.out_eq a, ← Quot.out_eq b, h2]

/-- The constant `1`-cochain is a cocycle in degree `0`. -/
lemma const_one_mem_cycles (X : TopCat.{0}) :
    (1 : Cochain (TopCat.toSSet.obj X) ℚ 0)
      ∈ cycles (TopCat.toSSet.obj X) ℚ 0 := by
  rw [mem_cycles_iff]
  ext σ
  rw [coboundary_apply]
  simp [Fin.sum_univ_two]

/-- The cohomology class of the constant `1`-cochain is nonzero on a nonempty space. -/
theorem H_mk_const_one_ne_zero (X : TopCat.{0}) [Nonempty X] :
    (H.mk (1 : Cochain (TopCat.toSSet.obj X) ℚ 0) (const_one_mem_cycles X) :
      H (TopCat.toSSet.obj X) ℚ 0) ≠ 0 := by
  intro h0
  have h1 : HzeroEval X (H.mk (1 : Cochain (TopCat.toSSet.obj X) ℚ 0) (const_one_mem_cycles X))
      = HzeroEval X 0 := congrArg (HzeroEval X) h0
  rw [map_zero] at h1
  have h2 := congrFun h1 (Classical.choice ‹Nonempty X›)
  rw [HzeroEval_mk] at h2
  simp at h2

end

end Submission.Cohomology
