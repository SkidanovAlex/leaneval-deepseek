import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORHomAlg.JL52.diagTensor_regular_projective
import Submission.Work.ORHomAlg.JL52.isScalarTowerDiag

/-!
# `X ↦ A ⊗[K] X` (diagonal `K[G]`-structure) preserves projective objects

This file proves `Work.ORHomAlg.JL52.diagTensor_preservesProjectiveObjects`: the endofunctor
`diagTensor A` of `ModuleCat (MonoidAlgebra K G)`, `X ↦ A ⊗[K] X` with the diagonal `K[G]`-action
`g • (a ⊗ x) = (g • a) ⊗ (g • x)` (Jaikin-Zapirain--Linton, Lemma 5.2 (2)), sends projective
objects to projective objects.

Route (as in the paper):
* `A ⊗[K] K[G]`, with the diagonal action, is a *free* (hence projective) left `K[G]`-module
  (`Work.ORHomAlg.JL52.diagTensor_regular_projective`).
* `diagTensor A` commutes with direct sums: `A ⊗[K] (ι →₀ K[G]) ≃ₗ[K[G]] ι →₀ (A ⊗[K] K[G])`
  (`diagTensor_finsupp_aux`), so the image of a free module is a direct sum of copies of a
  projective module, hence projective.
* A projective module is a direct summand of a free one; applying `A ⊗[K] -` (which is `K[G]`-linear
  on the diagonal structures, by `diagTensorMap_smul`) to the splitting exhibits `A ⊗[K] X` as a
  direct summand of the projective module `A ⊗[K] (X →₀ K[G])`.

Note on the `attribute [-instance]` occurrences below: on `A ⊗[K] K[G]` there are two candidate
`K[G]`-actions, the diagonal one (`DiagTensorDefs.instDiagSMul`, priority `2000`) and Mathlib's
action on the left factor.  For the *plain* `SMul` the diagonal one wins, but the coefficient module
of the direct sum `ι →₀ (A ⊗[K] K[G])` is asked for a `SMulZeroClass`, and instance search then
happily solves that through the left factor, giving `ι →₀ (A ⊗[K] K[G])` a *different* (pointwise
left-factor) structure than the one `diagTensor` produces.  Removing Mathlib's left-factor instances
for the duration of the two declarations concerned removes the ambiguity, so that `ι →₀ (A ⊗[K] K[G])`
unambiguously carries the direct sum of copies of the diagonal `K[G]`-module `A ⊗[K] K[G]`.
-/

namespace Work.ORHomAlg.JL52

universe u

open CategoryTheory
open scoped TensorProduct

/-- A finitely supported function type `ι →₀ P` is projective whenever `P` is. -/
theorem finsupp_projective_aux {R : Type u} [Semiring R] {P : Type u} [AddCommMonoid P]
    [Module R P] {ι : Type u} [Module.Projective R P] : Module.Projective R (ι →₀ P) := by
  classical
  exact Module.Projective.of_equiv' (finsuppLEquivDirectSum R P ι).symm

section Finsupp

variable (K : Type u) [Field K] (G : Type u) [Group G]
variable (A : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
  [SMulCommClass K (MonoidAlgebra K G) A]

set_option maxHeartbeats 1600000 in
attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul in
/-- `diagTensor A` commutes with direct sums:
`A ⊗[K] (ι →₀ K[G]) ≃ₗ[K[G]] ι →₀ (A ⊗[K] K[G])`, where the direct sum carries the pointwise
diagonal `K[G]`-structure. -/
theorem diagTensor_finsupp_aux (ι : Type u) :
    Nonempty (TensorProduct K A (ι →₀ MonoidAlgebra K G) ≃ₗ[MonoidAlgebra K G]
      (ι →₀ TensorProduct K A (MonoidAlgebra K G))) := by
  classical
  haveI hST1 : IsScalarTower K (MonoidAlgebra K G)
      (TensorProduct K A (ι →₀ MonoidAlgebra K G)) :=
    isScalarTowerDiag K G A (ι →₀ MonoidAlgebra K G)
  haveI hST2 : IsScalarTower K (MonoidAlgebra K G) (TensorProduct K A (MonoidAlgebra K G)) :=
    isScalarTowerDiag K G A (MonoidAlgebra K G)
  haveI hST3 : IsScalarTower K (MonoidAlgebra K G)
      (ι →₀ TensorProduct K A (MonoidAlgebra K G)) :=
    ⟨fun c r f => by
      ext i
      simp only [Finsupp.smul_apply]
      exact hST2.smul_assoc c r (f i)⟩
  -- the underlying `K`-linear equivalence: `a ⊗ (single i x) ↦ single i (a ⊗ x)`
  let fR : TensorProduct K A (ι →₀ MonoidAlgebra K G) ≃ₗ[K]
      (ι →₀ TensorProduct K A (MonoidAlgebra K G)) :=
    TensorProduct.finsuppRight K K A (MonoidAlgebra K G) ι
  have hfR : ∀ (a : A) (p : ι →₀ MonoidAlgebra K G) (i : ι),
      fR (a ⊗ₜ[K] p) i = a ⊗ₜ[K] p i :=
    fun a p i => TensorProduct.finsuppRight_apply_tmul_apply a p i
  -- additivity of the diagonal action, exposed through `diag_smul_def` (whose instance is fixed)
  have hT_add : ∀ (g : G) (x y : TensorProduct K A (ι →₀ MonoidAlgebra K G)),
      MonoidAlgebra.single g (1:K) • (x + y)
        = MonoidAlgebra.single g (1:K) • x + MonoidAlgebra.single g (1:K) • y := by
    intro g x y
    rw [diag_smul_def, map_add, ← diag_smul_def, ← diag_smul_def]
  have hT_zero : ∀ g : G,
      MonoidAlgebra.single g (1:K) • (0 : TensorProduct K A (ι →₀ MonoidAlgebra K G)) = 0 := by
    intro g
    rw [diag_smul_def]
    exact map_zero _
  -- the same pointwise on the direct sum
  have hW_add : ∀ (g : G) (u v : ι →₀ TensorProduct K A (MonoidAlgebra K G)),
      MonoidAlgebra.single g (1:K) • (u + v)
        = MonoidAlgebra.single g (1:K) • u + MonoidAlgebra.single g (1:K) • v := by
    intro g u v
    ext i
    simp only [Finsupp.smul_apply, Finsupp.add_apply, diag_smul_def, map_add]
  have hW_zero : ∀ g : G,
      MonoidAlgebra.single g (1:K) • (0 : ι →₀ TensorProduct K A (MonoidAlgebra K G)) = 0 := by
    intro g
    ext i
    simp only [Finsupp.smul_apply, Finsupp.zero_apply, diag_smul_def, map_zero]
  -- `fR` is `K[G]`-equivariant on the group generators
  have key : ∀ (g : G) (z : TensorProduct K A (ι →₀ MonoidAlgebra K G)),
      fR (MonoidAlgebra.single g (1 : K) • z) = MonoidAlgebra.single g (1 : K) • fR z := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => rw [hT_zero g, map_zero, hW_zero g]
    | add x y hx hy =>
        rw [hT_add g x y, map_add, map_add, hW_add g (fR x) (fR y), hx, hy]
    | tmul a p =>
        rw [diag_smul_single_tmul (K := K) (G := G) A (ι →₀ MonoidAlgebra K G) g a p]
        ext i
        simp only [hfR, Finsupp.smul_apply,
          diag_smul_single_tmul (K := K) (G := G) A (MonoidAlgebra K G) g a (p i)]
  let g : TensorProduct K A (ι →₀ MonoidAlgebra K G) →ₗ[MonoidAlgebra K G]
      (ι →₀ TensorProduct K A (MonoidAlgebra K G)) :=
    MonoidAlgebra.equivariantOfLinearOfComm
      (V := TensorProduct K A (ι →₀ MonoidAlgebra K G))
      (W := ι →₀ TensorProduct K A (MonoidAlgebra K G))
      (fR : TensorProduct K A (ι →₀ MonoidAlgebra K G) →ₗ[K]
        (ι →₀ TensorProduct K A (MonoidAlgebra K G))) key
  have hg : ⇑g = ⇑fR := rfl
  exact ⟨LinearEquiv.ofBijective g (hg ▸ fR.bijective)⟩

end Finsupp

set_option maxHeartbeats 1600000 in
attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul in
/-- The functor `X ↦ TensorProduct K A X` on left `K[G]`-modules (diagonal `K[G]`-structure)
preserves projective objects.  Route: `TensorProduct K A (MonoidAlgebra K G)` is a free (hence
projective) left `K[G]`-module, `diagTensor A` is additive and preserves direct sums, and a
projective module is a direct summand of a free one. -/
theorem diagTensor_preservesProjectiveObjects (K : Type u) [Field K] (G : Type u) [Group G]
    (A : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A] :
    (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) A).PreservesProjectiveObjects := by
  refine ⟨fun {X} hX => ?_⟩
  -- `X` is projective as a module, hence a direct summand of the free module `↥X →₀ K[G]`.
  haveI hXp : Module.Projective (MonoidAlgebra K G) ↥X :=
    ModuleCat.projective_of_module_projective X
  obtain ⟨sX, hsX⟩ := Module.projective_def'.mp hXp
  -- tensoring the regular module with `A` (diagonal action) is projective
  haveI hReg : Module.Projective (MonoidAlgebra K G) (TensorProduct K A (MonoidAlgebra K G)) :=
    diagTensor_regular_projective K G A
  -- and `diagTensor A` commutes with direct sums, so it stays projective for `↥X →₀ K[G]`
  haveI hMid : Module.Projective (MonoidAlgebra K G)
      (TensorProduct K A (↥X →₀ MonoidAlgebra K G)) := by
    obtain ⟨e⟩ := diagTensor_finsupp_aux K G A ↥X
    haveI : Module.Projective (MonoidAlgebra K G)
        (↥X →₀ TensorProduct K A (MonoidAlgebra K G)) := finsupp_projective_aux
    exact Module.Projective.of_equiv' e.symm
  -- tensor the splitting `K[G]^(X) → X` with `A` over `K` to split `A ⊗ X`
  let lc : (↥X →₀ MonoidAlgebra K G) →ₗ[MonoidAlgebra K G] ↥X :=
    Finsupp.linearCombination (MonoidAlgebra K G) id
  have hlc : ∀ x : ↥X, lc (sX x) = x := fun x => LinearMap.congr_fun hsX x
  let i : TensorProduct K A ↥X →ₗ[MonoidAlgebra K G]
      TensorProduct K A (↥X →₀ MonoidAlgebra K G) :=
    { toFun := TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK sX)
      map_add' := map_add _
      map_smul' := fun r z => diagTensorMap_smul A sX r z }
  let s : TensorProduct K A (↥X →₀ MonoidAlgebra K G) →ₗ[MonoidAlgebra K G]
      TensorProduct K A ↥X :=
    { toFun := TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK lc)
      map_add' := map_add _
      map_smul' := fun r z => diagTensorMap_smul A lc r z }
  haveI hP : Module.Projective (MonoidAlgebra K G) (TensorProduct K A ↥X) := by
    refine Module.Projective.of_split (i := i) (s := s) ?_
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
        show TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK lc)
          (TensorProduct.map (LinearMap.id : A →ₗ[K] A) (restrictK sX) (a ⊗ₜ[K] x))
            = a ⊗ₜ[K] x
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
          LinearMap.id_apply, restrictK_apply, restrictK_apply, hlc x]
  show CategoryTheory.Projective (ModuleCat.of (MonoidAlgebra K G) (TensorProduct K A ↥X))
  exact ModuleCat.projective_of_categoryTheory_projective _

end Work.ORHomAlg.JL52
