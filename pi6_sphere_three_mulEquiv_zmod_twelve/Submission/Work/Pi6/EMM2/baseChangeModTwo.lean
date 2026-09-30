import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Change of coefficients `H_*(X; 𝕜) ≅ H_*(X; ℤ/2) ⊗[ℤ/2] 𝕜` for `CharP 𝕜 2`

For a field `𝕜` of characteristic `2` and any topological space `X`, the singular homology of `X`
with coefficients in `𝕜` is the extension of scalars along the canonical ring homomorphism
`ZMod 2 →+* 𝕜` of the homology with coefficients in `ℤ/2`:

`H_n(X; 𝕜) ≅ (extendScalars (ZMod.castHom … 𝕜)).obj (H_n(X; ℤ/2))`.

The proof is the degreewise consequence of the two standard facts, both taken from the shared
library (`Submission/Work/StemsB/sphRatHomology.lean`):

* `Work.StemsB.SphRat.chainComplexBaseChange`: `C_*(X; ℤ/2) ⊗[ℤ/2] 𝕜 ≅ C_*(X; 𝕜)` as chain
  complexes of `𝕜`-modules (here `C_*` is the simplicial chain complex of the singular
  simplicial set of `X`), together with the identification of the coefficient object
  `𝕜 ⊗[ℤ/2] ℤ/2 ≅ 𝕜` (`extendScalarsZModTwoIso` below);
* `Work.StemsB.SphRat.homologyMapBaseChange`: an additive exact functor commutes with homology.

Exactness of `− ⊗[ℤ/2] 𝕜` is where the characteristic hypothesis enters: a field has
characteristic `2`, so `ZMod 2` is a field and every module over it is free, hence flat, and
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat` applies.

The same statement for general prime characteristic (and for `ℤ → 𝕜`) is
`Work.Pi6.K2Z.baseChangeCharP` / `Work.Pi6.K2Z.baseChangeFlat`; the case `p = 2` is the one needed
by the mod-`2` forcing computation of the area `EMM2`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.Pi6.EMM2

/-- The canonical `ZMod 2`-algebra structure on a field of characteristic `2`, i.e. the one
induced by `ZMod.castHom (by decide : 2 ∣ 2) 𝕜`.  It is `local`: it is only needed to speak of the
`𝕜`-module structure on the tensor product `𝕜 ⊗[ZMod 2] ZMod 2` inside this file. -/
local instance zmodTwoAlgebraInst {𝕜 : Type} [Field 𝕜] [CharP 𝕜 2] :
    Algebra (ZMod 2) 𝕜 :=
  (ZMod.castHom (by decide : 2 ∣ 2) 𝕜).toAlgebra

/-- The `𝕜`-linear equivalence `𝕜 ⊗[ZMod 2] ZMod 2 ≃ₗ[𝕜] 𝕜`, `x ⊗ a ↦ x * (a : 𝕜)`
(equivalently `TensorProduct.rid`). -/
noncomputable def ridLinEquivModTwo {𝕜 : Type} [Field 𝕜] [CharP 𝕜 2] :
    (𝕜 ⊗[ZMod 2] ZMod 2) ≃ₗ[𝕜] 𝕜 where
  toFun := fun x => TensorProduct.rid (ZMod 2) 𝕜 x
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro q x
    induction x using TensorProduct.inductionOn with
    | tmul a z =>
        show TensorProduct.rid (ZMod 2) 𝕜 (q • (a ⊗ₜ[ZMod 2] z)) =
          q • TensorProduct.rid (ZMod 2) 𝕜 (a ⊗ₜ[ZMod 2] z)
        rw [TensorProduct.smul_tmul', TensorProduct.rid_tmul, TensorProduct.rid_tmul]
        simp only [Algebra.smul_def]
        ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, smul_add]
  invFun := fun q => q ⊗ₜ[ZMod 2] (1 : ZMod 2)
  left_inv := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a z =>
        show (TensorProduct.rid (ZMod 2) 𝕜 (a ⊗ₜ[ZMod 2] z)) ⊗ₜ[ZMod 2] (1 : ZMod 2) =
          a ⊗ₜ[ZMod 2] z
        rw [TensorProduct.rid_tmul]
        rw [← TensorProduct.smul_tmul' (R := ZMod 2) (R' := ZMod 2) z a (1 : ZMod 2)]
        rw [← TensorProduct.tmul_smul z a (1 : ZMod 2)]
        simp
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  right_inv := by
    intro q
    show TensorProduct.rid (ZMod 2) 𝕜 (q ⊗ₜ[ZMod 2] (1 : ZMod 2)) = q
    rw [TensorProduct.rid_tmul]
    simp

/-- **The base ring of the extension of scalars is the ring itself:**
`(extendScalars (ZMod 2 → 𝕜)).obj ↧(ZMod 2) ≅ ↧𝕜`, i.e. `𝕜 ⊗[ℤ/2] ℤ/2 ≅ 𝕜`. -/
noncomputable def extendScalarsZModTwoIso {𝕜 : Type} [Field 𝕜] [CharP 𝕜 2] :
    (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)).obj
      (ModuleCat.of (ZMod 2) (ZMod 2)) ≅ ModuleCat.of 𝕜 𝕜 :=
  LinearEquiv.toModuleIso (ridLinEquivModTwo (𝕜 := 𝕜))

/-- **`𝕜` is flat over `ℤ/2`** for a field `𝕜` of characteristic `2`, with respect to the
structure induced by `ZMod.castHom (by decide : 2 ∣ 2) 𝕜`: `ZMod 2` is a field, so every module
over it is free, hence flat. -/
lemma flat_castHom_two {𝕜 : Type} [Field 𝕜] (h2 : CharP 𝕜 2) :
    (ZMod.castHom (by decide : 2 ∣ 2) 𝕜).Flat := by
  rw [RingHom.Flat]
  letI : Algebra (ZMod 2) 𝕜 := (ZMod.castHom (by decide : 2 ∣ 2) 𝕜).toAlgebra
  infer_instance

theorem baseChangeModTwo (𝕜 : Type) [Field 𝕜] (h2 : CharP 𝕜 2) {X : Type} [TopologicalSpace X]
    (n : ℕ) :
    Nonempty (Work.Pi6.HR 𝕜 X n ≅
      (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)).obj
        (Work.Pi6.HR (ZMod 2) X n)) := by
  -- `𝕜` is flat over `ℤ/2`, so extension of scalars is exact, hence preserves homology
  have hf : (ZMod.castHom (by decide : 2 ∣ 2) 𝕜).Flat := flat_castHom_two h2
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)) :=
    inferInstance
  haveI : (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)).PreservesHomology :=
    inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)) := fun _ => inferInstance
  -- the comparison `C_*(X; ℤ/2) ⊗[ℤ/2] 𝕜 ≅ C_*(X; 𝕜)` of chain complexes
  let F : ModuleCat (ZMod 2) ⥤ ModuleCat 𝕜 :=
    ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat (ZMod 2)) ℕ := Work.Cohomology.singularChains (ZMod 2) Y
  let L : ChainComplex (ModuleCat 𝕜) ℕ := Work.Cohomology.singularChains 𝕜 Y
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y)
        (ModuleCat.of (ZMod 2) (ZMod 2)) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        (extendScalarsZModTwoIso (𝕜 := 𝕜))
  -- hence, `𝕜` being exact over `ℤ/2`, `H_n(X;𝕜)` is the extension of scalars of `H_n(X;ℤ/2)`
  exact ⟨(HomologicalComplex.homologyMapIso hΦ n).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange F K n).some⟩

end Work.Pi6.EMM2
