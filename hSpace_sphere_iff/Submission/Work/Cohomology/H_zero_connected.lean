/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `H⁰` of a path-connected space is `ℚ`

For a path-connected topological space `X`, the degree `0` singular cohomology with coefficients
in `ℚ` is a one-dimensional `ℚ`-vector space:

`H⁰(X; ℚ) ≃ₗ[ℚ] ℚ`.

Indeed, `0`-simplices of the singular complex are the points of `X`, so a `0`-cochain is a
function on `X` (`Submission.Cohomology.HzeroEvalAux`); a `0`-cocycle is a function which is
constant along the edges of the simplicial set, i.e. along paths of `X`
(`zeroCocycle_eq_of_hom`).  Hence, when `X` is path-connected, every `0`-cocycle is constant
(`HzeroEval_eq_of_path`), the evaluation map at any point `p` is a linear equivalence
`H⁰(X; ℚ) ≃ₗ[ℚ] ℚ`, and the constant class `1` shows that it is onto.
-/
import Mathlib
import Submission.Work.Cohomology.Hzero

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Cohomology

noncomputable section

/-- The coboundary of a `0`-cochain, evaluated at a `1`-simplex: it is the difference of the
values of the cochain at the two endpoints of the edge. -/
lemma coboundary_zero_apply (X : TopCat.{0}) (u : Cochain (TopCat.toSSet.obj X) ℚ 0)
    (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    Submission.Cohomology.coboundary (TopCat.toSSet.obj X) ℚ 0 u σ
      = u ((TopCat.toSSet.obj X).δ 0 σ) - u ((TopCat.toSSet.obj X).δ 1 σ) := by
  rw [Submission.Cohomology.coboundary_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, zsmul_eq_mul, Int.cast_neg,
    Int.cast_one, one_mul, neg_one_mul, sub_eq_add_neg]

/-- A `0`-cocycle of the singular complex of `X` takes the same value at the two endpoints of a
path of `X` (given here as a morphism `I ⟶ X`). -/
lemma zeroCocycle_eq_of_hom (X : TopCat.{0}) (u : Cochain (TopCat.toSSet.obj X) ℚ 0)
    (hu : u ∈ Submission.Cohomology.cycles (TopCat.toSSet.obj X) ℚ 0)
    (f : TopCat.I ⟶ X) :
    u (TopCat.toSSetObj₀Equiv.symm (f 0)) = u (TopCat.toSSetObj₀Equiv.symm (f 1)) := by
  have h := congrFun ((Submission.Cohomology.mem_cycles_iff u).mp hu)
    (TopCat.toSSetObj₁Equiv.symm f)
  rw [coboundary_zero_apply, TopCat.δ_one_toSSetObj₁Equiv.symm f,
    TopCat.δ_zero_toSSetObj₁Equiv.symm f, Pi.zero_apply] at h
  exact (sub_eq_zero.mp h).symm

/-- A cohomology class of degree `0` of the singular complex of `X` has constant evaluation on
the points of `X`, along every path. -/
lemma HzeroEval_eq_of_path (X : TopCat.{0})
    (z : Submission.Cohomology.H (TopCat.toSSet.obj X) ℚ 0) {x y : X} (γ : X.Path x y) :
    Submission.Cohomology.HzeroEval X z x = Submission.Cohomology.HzeroEval X z y := by
  rw [show z = Submission.Cohomology.H.mk (Quot.out z).1 (Quot.out z).2
        from (Quot.out_eq z).symm]
  simp only [Submission.Cohomology.HzeroEval_mk]
  simpa using zeroCocycle_eq_of_hom X (Quot.out z).1 (Quot.out z).2 γ.hom

/-- Evaluation of a function on `X` at a point, as a `ℚ`-linear map. -/
def evalAt {X : Type*} (p : X) : (X → ℚ) →ₗ[ℚ] ℚ where
  toFun f := f p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`H⁰` of a path-connected space is one-dimensional.**  The evaluation map at any point of
`X`, composed with `HzeroEval`, is a linear equivalence with `ℚ`. -/
theorem H_zero_connected (X : TopCat.{0}) [PathConnectedSpace X] :
    Nonempty (Submission.Cohomology.H (TopCat.toSSet.obj X) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  have hne : Nonempty X := PathConnectedSpace.nonempty
  let p : X := Classical.choice hne
  -- every `0`-cohomology class has constant evaluation on `X`
  have hconst : ∀ (z : Submission.Cohomology.H (TopCat.toSSet.obj X) ℚ 0) (x : X),
      Submission.Cohomology.HzeroEval X z x = Submission.Cohomology.HzeroEval X z p :=
    fun z x => (HzeroEval_eq_of_path X z
      ((TopCat.pathEquiv (x := p) (y := x)).symm (PathConnectedSpace.somePath p x))).symm
  refine ⟨LinearEquiv.ofBijective ((evalAt p).comp (Submission.Cohomology.HzeroEval X))
    ⟨?_, ?_⟩⟩
  · -- injectivity: a class whose evaluation at `p` vanishes is constantly zero
    intro z w hzw
    apply Submission.Cohomology.HzeroEval_injective X
    funext x
    rw [hconst z x, hconst w x]
    simpa [evalAt] using hzw
  · -- surjectivity: the class of the constant `1`-cochain evaluates to `1`
    intro r
    refine ⟨r • Submission.Cohomology.H.mk (1 : Cochain (TopCat.toSSet.obj X) ℚ 0)
        (Submission.Cohomology.const_one_mem_cycles X), ?_⟩
    show (evalAt p) (Submission.Cohomology.HzeroEval X (r • Submission.Cohomology.H.mk
      (1 : Cochain (TopCat.toSSet.obj X) ℚ 0)
        (Submission.Cohomology.const_one_mem_cycles X))) = r
    rw [map_smul, map_smul, evalAt]
    rw [Submission.Cohomology.HzeroEval_mk]
    simp [smul_eq_mul]

end

end Work.Cohomology
