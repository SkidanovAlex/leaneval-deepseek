import Mathlib
import Submission.Work.BW.sieg2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linear independence descends from the mixed-coordinate embedding

The map `x ↦ siegCoordF x` (`Submission.Work.BW.siegCoordF`) sends a tuple `Fin N → F`
of elements of a number field to its *mixed coordinates* in `ℝ^{d N}`; it is the
composite of the mixed embedding `mixedEmbedding F : F → ℝ^{r₁} × ℂ^{r₂}` with the
coordinate map of the standard basis.  Since `mixedEmbedding F` is a `ℚ`-algebra
homomorphism, this coordinate map is `ℚ`-linear and injective, so a `ℚ`-linear relation
among the coordinates of a family of tuples forces a relation among the tuples.

This is the form in which the Siegel/Bombieri–Vaaler reduction passes information about
`SiegCoord F N` back to `F^N`.
-/

open NumberField
open scoped Classical

namespace Work.BW

/-- The `q`-th mixed coordinate of an element of `F`, as a `ℚ`-linear functional.  It is the
composition of the mixed embedding `mixedEmbedding F` with the `q`-th coordinate functional
`(mixedEmbedding.stdBasis F).coord q`. -/
noncomputable def siegCoordLinQ {F : Type*} [Field F] [NumberField F]
    (q : NumberField.mixedEmbedding.index F) : F →ₗ[ℚ] ℝ :=
  ((NumberField.mixedEmbedding.stdBasis F).coord q).restrictScalars ℚ ∘ₗ
    (NumberField.mixedEmbedding F).toRatAlgHom.toLinearMap

/-- `siegCoordLinQ q` computes the `q`-th mixed coordinate of `x`. -/
theorem siegCoordLinQ_apply {F : Type*} [Field F] [NumberField F]
    (q : NumberField.mixedEmbedding.index F) (x : F) :
    siegCoordLinQ q x = (NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F x) q := rfl

/-- `siegCoordF`, viewed as a `ℚ`-linear map `F^N → ℝ^{d N}`. -/
noncomputable def siegCoordFLin {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    (Fin N → F) →ₗ[ℚ] SiegCoord F N where
  toFun := siegCoordF
  map_add' := fun x y => by
    funext j k
    simp only [siegCoordF, Pi.add_apply, map_add, Finsupp.add_apply]
  map_smul' := fun c x => by
    funext j k
    simp [siegCoordF, map_rat_smul]

/-- `siegCoordFLin` agrees with `siegCoordF`. -/
theorem siegCoordFLin_apply {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x : Fin N → F) : siegCoordFLin (F := F) N x = siegCoordF x := rfl

/-- The mixed-coordinate map `siegCoordF` is injective: it is the composite of the injective
mixed embedding with the coordinate map of a basis. -/
theorem siegCoordFLin_ker {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    (siegCoordFLin (F := F) N).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  funext j
  have hj : (NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F (x j)) = 0 := by
    apply Finsupp.ext
    intro k
    have h1 : (siegCoordF x) j k = (0 : SiegCoord F N) j k := by
      rw [← hx]; rfl
    simpa [siegCoordF] using h1
  have h2 : NumberField.mixedEmbedding F (x j) = 0 :=
    (NumberField.mixedEmbedding.stdBasis F).repr.map_eq_zero_iff.mp hj
  have h3 : NumberField.mixedEmbedding F (x j) = NumberField.mixedEmbedding F 0 := by
    simpa using h2
  simpa using NumberField.mixedEmbedding_injective F h3

theorem linearIndependent_of_siegCoordF {F : Type*} [Field F] [NumberField F]
    {k N : ℕ} (w : Fin k → Fin N → F)
    (h : LinearIndependent ℚ (fun i => Work.BW.siegCoordF (w i))) :
    LinearIndependent ℚ w := by
  have hker : (siegCoordFLin (F := F) N).ker = ⊥ := siegCoordFLin_ker N
  exact (LinearMap.linearIndependent_iff (siegCoordFLin (F := F) N) hker).mp h

end Work.BW
