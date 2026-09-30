import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Change of coefficients `H_*(X; 𝕜) ≅ H_*(X; ℤ/p) ⊗[ℤ/p] 𝕜`

For a field `𝕜` of characteristic `p` and any space `X`, the singular homology of `X` with
coefficients in `𝕜` is the extension of scalars of the homology with coefficients in `ℤ/p` along
the canonical ring homomorphism `ZMod p →+* 𝕜`:

`H_n(X; 𝕜) ≅ (extendScalars (ZMod.castHom … 𝕜)).obj (H_n(X; ℤ/p))`.

This is the degreewise consequence of the two standard facts

* `C_*(X; 𝕜) ≅ C_*(X; ℤ/p) ⊗[ℤ/p] 𝕜` (an isomorphism of chain complexes, `chainComplexBaseChange`
  together with the canonical isomorphism `𝕜 ⊗[ℤ/p] ℤ/p ≅ 𝕜`);
* `𝕜` is flat over `ℤ/p`, so extension of scalars is exact and commutes with homology
  (`homologyMapBaseChange`).

The flatness of `𝕜` over `ZMod p` is where the characteristic hypothesis enters: for a field of
characteristic `p ≠ 0`, `p` is a prime (`CharP.char_prime_of_ne_zero`), so `ZMod p` is a field and
every module over it is free, hence flat; for `p = 0` the ring is `ℤ` itself
(`ZMod 0 = ℤ` definitionally) and flatness of `𝕜` reduces to the unique (torsion free) `ℤ`-module
structure on a field of characteristic zero, `AddCommGroup.toIntModule`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.Pi6.K2Z

/-- The canonical `ZMod p`-algebra structure on a ring of characteristic `p`, i.e. the one induced
by `ZMod.castHom (dvd_refl p) 𝕜`.  It is the structure along which extension of scalars is taken
below, and it is `local` so that it is (only) picked up by instance search in this file. -/
local instance zmodAlgebraInst {𝕜 : Type} [Field 𝕜] (p : ℕ) [CharP 𝕜 p] :
    Algebra (ZMod p) 𝕜 :=
  (ZMod.castHom (dvd_refl p) 𝕜).toAlgebra

/-- The `𝕜`-linear equivalence `𝕜 ⊗[ZMod p] ZMod p ≃ₗ[𝕜] 𝕜`, `x ⊗ a ↦ x * (cast a)`. -/
noncomputable def ridLinEquiv {𝕜 : Type} [Field 𝕜] (p : ℕ) [CharP 𝕜 p] :
    (𝕜 ⊗[ZMod p] ZMod p) ≃ₗ[𝕜] 𝕜 where
  toFun := fun x => TensorProduct.rid (ZMod p) 𝕜 x
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro q x
    induction x using TensorProduct.inductionOn with
    | tmul a z =>
        show TensorProduct.rid (ZMod p) 𝕜 (q • (a ⊗ₜ[ZMod p] z)) =
          q • TensorProduct.rid (ZMod p) 𝕜 (a ⊗ₜ[ZMod p] z)
        rw [TensorProduct.smul_tmul', TensorProduct.rid_tmul, TensorProduct.rid_tmul]
        simp only [Algebra.smul_def]
        ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, smul_add]
  invFun := fun q => q ⊗ₜ[ZMod p] (1 : ZMod p)
  left_inv := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a z =>
        show (TensorProduct.rid (ZMod p) 𝕜 (a ⊗ₜ[ZMod p] z)) ⊗ₜ[ZMod p] (1 : ZMod p) =
          a ⊗ₜ[ZMod p] z
        rw [TensorProduct.rid_tmul]
        rw [← TensorProduct.smul_tmul' (R := ZMod p) (R' := ZMod p) z a (1 : ZMod p)]
        rw [← TensorProduct.tmul_smul z a (1 : ZMod p)]
        simp
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  right_inv := by
    intro q
    show TensorProduct.rid (ZMod p) 𝕜 (q ⊗ₜ[ZMod p] (1 : ZMod p)) = q
    rw [TensorProduct.rid_tmul]
    simp

/-- **The base ring of the extension of scalars is the ring itself:**
`(extendScalars (ZMod p → 𝕜)).obj ↧(ZMod p) ≅ ↧𝕜`, i.e. `𝕜 ⊗[ZMod p] ZMod p ≅ 𝕜`. -/
noncomputable def extendScalarsZModIso {𝕜 : Type} [Field 𝕜] (p : ℕ) [CharP 𝕜 p] :
    (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)).obj (ModuleCat.of (ZMod p) (ZMod p)) ≅
      ModuleCat.of 𝕜 𝕜 :=
  LinearEquiv.toModuleIso (ridLinEquiv p)

/-- Every `ℤ`-module structure on a fixed additive group is the canonical one, so flatness is
independent of the chosen `Module ℤ M` instance. -/
lemma flat_int_congr {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℤ M)
    (h : @Module.Flat ℤ M _ _ i₁) : @Module.Flat ℤ M _ _ i₂ := by
  rw [Subsingleton.elim i₁ i₂] at h
  exact h

/-- A field of characteristic zero is flat as a `ℤ`-module. -/
lemma module_flat_int_of_charZero {𝕜 : Type} [Field 𝕜] [CharZero 𝕜] :
    @Module.Flat ℤ 𝕜 _ _ (AddCommGroup.toIntModule 𝕜) := by
  letI : Module ℤ 𝕜 := AddCommGroup.toIntModule 𝕜
  infer_instance

/-- **`𝕜` is flat over `ZMod p`** for a field `𝕜` of characteristic `p`, with respect to the
structure induced by `ZMod.castHom (dvd_refl p) 𝕜`. -/
lemma flat_castHom {𝕜 : Type} [Field 𝕜] (p : ℕ) [CharP 𝕜 p] :
    (ZMod.castHom (dvd_refl p) 𝕜).Flat := by
  rw [RingHom.Flat]
  by_cases hp0 : p = 0
  · -- `ZMod 0 = ℤ` definitionally, and a field of characteristic zero is flat over `ℤ`.
    subst hp0
    haveI : CharZero 𝕜 := CharP.charP_to_charZero 𝕜
    exact flat_int_congr _ _ (module_flat_int_of_charZero (𝕜 := 𝕜))
  · -- `p` is prime, so `ZMod p` is a field and `𝕜` is a free, hence flat, `ZMod p`-module.
    haveI : Fact (Nat.Prime p) := ⟨CharP.char_prime_of_ne_zero 𝕜 hp0⟩
    letI : Algebra (ZMod p) 𝕜 := (ZMod.castHom (dvd_refl p) 𝕜).toAlgebra
    infer_instance

/-- **Base change of coefficients for singular homology.**  For a field `𝕜` of characteristic `p`
and any topological space `X`,

`H_n(X; 𝕜) ≅ (extendScalars (ZMod.castHom (dvd_refl p) 𝕜)).obj (H_n(X; ℤ/p))`. -/
theorem baseChangeCharP {𝕜 : Type} [Field 𝕜] (p : ℕ) [CharP 𝕜 p] (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    Nonempty (Work.Pi6.HR 𝕜 X n ≅
      (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)).obj (Work.Pi6.HR (ZMod p) X n)) := by
  have hf : (ZMod.castHom (dvd_refl p) 𝕜).Flat := flat_castHom p
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)) :=
    inferInstance
  haveI : (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)).PreservesHomology :=
    inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)) := fun _ => inferInstance
  let F : ModuleCat (ZMod p) ⥤ ModuleCat 𝕜 := ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat (ZMod p)) ℕ := Work.Cohomology.singularChains (ZMod p) Y
  let L : ChainComplex (ModuleCat 𝕜) ℕ := Work.Cohomology.singularChains 𝕜 Y
  -- `C_*(X;𝕜) ≅ C_*(X;ℤ/p) ⊗[ℤ/p] 𝕜`, hence on homology.
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y)
        (ModuleCat.of (ZMod p) (ZMod p)) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y) (extendScalarsZModIso p)
  exact ⟨(HomologicalComplex.homologyMapIso hΦ n).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange F K n).some⟩

end Work.Pi6.K2Z
