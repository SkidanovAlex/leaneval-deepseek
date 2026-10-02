import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.StemsB.TorsionBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Rational homology vanishing forces torsion integral homology

This file proves the change-of-coefficients step that the area RATHUREWICZ and its consumers
(area THOM, area STEMS) use in the vanishing form

`H_j(X;ℚ) = 0 ⟹ H_j(X;ℤ)` is a torsion group,

i.e. `Work.RatHurewicz.torsion_of_subsingleton_ratHomology`.

## The mathematics

For a space `X` and a degree `j`, the singular chain complex with coefficients in `ℚ` is obtained
from the integral one by the change-of-rings functor `ModuleCat.extendScalars (ℤ → ℚ)`, i.e. by the
base change `- ⊗[ℤ] ℚ`:

`C_*(X;ℚ) ≅ C_*(X;ℤ) ⊗[ℤ] ℚ`  (an isomorphism of chain complexes, degreewise),

and `ℚ` is flat over the Dedekind domain `ℤ`, so base change is exact and commutes with homology:

`H_j(X;ℚ) ≅ H_j(X;ℤ) ⊗[ℤ] ℚ`.

Hence if `H_j(X;ℚ)` is a subsingleton, so is `H_j(X;ℤ) ⊗[ℤ] ℚ`, and the rational-to-torsion bridge
`Work.StemsB.exists_nat_smul_eq_zero_of_subsingleton_tensorRat` concludes that every element of
`H_j(X;ℤ)` has finite order.  (That bridge is the content of `Submission/Work/StemsB/TorsionBridge.lean`:
`A ⊗[ℤ] ℚ = 0` forces `A` to be a torsion group, because an element of infinite order spans a copy
of `ℤ`, whose tensor product with the flat module `ℚ` stays non-zero.)

The only care needed in the formalisation is that Mathlib's `TensorProduct` takes the `ℤ`-module
structure of the factors as *instance* arguments, and that the module structure which
`ModuleCat.extendScalars` puts on the homology of the integral chain complex is the one bundled in
the `ModuleCat ℤ` object, not the canonical `AddCommGroup.toIntModule` structure picked by type
class synthesis.  The two are equal — every `ℤ`-module structure on a fixed additive group is the
canonical one (`AddCommGroup.uniqueIntModule`) — which is the content of
`Work.RatHurewicz.exists_nat_smul_eq_zero_of_subsingleton_tensorRat_module` below.

## Imports

The change-of-rings chapter for singular chains (`Work.StemsB.SphRat.chainComplexBaseChange`,
`chainComplexCoeffIso`, `homologyMapBaseChange`, `extendScalarsIntRatIso`, essentially the statement
`H_j(X;ℤ) ⊗ ℚ ≅ H_j(X;ℚ)` used by `Work.StemsB.sphRatHomology`) lives in
`Submission/Work/StemsB/sphRatHomology.lean`; the rational-to-torsion bridge lives in
`Submission/Work/StemsB/TorsionBridge.lean`.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.RatHurewicz

noncomputable section

/-- **The rational-to-torsion bridge for a prescribed `ℤ`-module structure.**

Mathlib's `TensorProduct` takes the module structure of its factors as an *instance* argument, so
the statement "`A ⊗[ℤ] ℚ` is a subsingleton" is a statement about a chosen `Module ℤ A`.  The
present lemma is the version of `Work.StemsB.exists_nat_smul_eq_zero_of_subsingleton_tensorRat` in
which that structure is an explicit argument `M`; it is what a consumer who arrives with a tensor
product manufactured by `ModuleCat.extendScalars` (whose module structure is the bundled one) can
apply directly.

The proof is a change of the instance only: all `ℤ`-module structures on a given additive group
coincide (`AddCommGroup.uniqueIntModule`), and the conclusion `∃ N > 0, N • a = 0` mentions the
`ℕ`-action, which comes from the additive group structure alone. -/
theorem exists_nat_smul_eq_zero_of_subsingleton_tensorRat_module {A : Type*} [AddCommGroup A]
    (M : Module ℤ A) (h : @Subsingleton (@TensorProduct ℤ _ A ℚ _ _ M _)) (a : A) :
    ∃ N : ℕ, 0 < N ∧ N • a = 0 := by
  have hM : M = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  rw [hM] at h
  exact Work.StemsB.exists_nat_smul_eq_zero_of_subsingleton_tensorRat h a

/-- **Rational homology vanishing forces torsion integral homology.**  For a topological space `X`
and a degree `j`, if the rational homology `H_j(X;ℚ)` vanishes (is a subsingleton), then every
element of the integral homology `H_j(X;ℤ)` is of finite order.  This is the change-of-coefficients
step `H_*(X;ℚ) ≅ H_*(X;ℤ) ⊗ ℚ` together with the flatness of `ℚ` over `ℤ` (a `ℤ`-module whose
tensor product with `ℚ` vanishes is a torsion module; compare
`Submission/Work/StemsB/TorsionBridge.lean`, and the general change-of-rings chapter for singular
chains used by `Work.StemsB.sphRatHomology`). -/
theorem torsion_of_subsingleton_ratHomology {X : Type} [TopologicalSpace X] (j : ℕ)
    (h : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology j)) :
    ∀ b : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j,
      ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  -- `ℚ` is flat over `ℤ`, so extension of scalars along `ℤ → ℚ` is exact and preserves homology.
  have hf : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : (ModuleCat.extendScalars (Int.castRingHom ℚ)).PreservesHomology := inferInstance
  haveI : ∀ (S : Type),
      PreservesColimitsOfShape (Discrete S) (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    fun _ => inferInstance
  -- `C_*(X;ℚ) ≅ C_*(X;ℤ) ⊗[ℤ] ℚ` as chain complexes, hence on homology.
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  let L : ChainComplex (ModuleCat ℚ) ℕ := Work.Cohomology.singularChains ℚ Y
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        Work.StemsB.SphRat.extendScalarsIntRatIso
  have hΨ : L.homology j ≅ F.obj (K.homology j) :=
    (HomologicalComplex.homologyMapIso hΦ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange F K j).some
  -- Vanishing of `H_j(X;ℚ)` therefore transfers to `H_j(X;ℤ) ⊗[ℤ] ℚ`.
  haveI : Subsingleton ↥(L.homology j) := h
  have hFsub : Subsingleton ↥(F.obj (K.homology j)) :=
    Function.Surjective.subsingleton (f := fun x => hΨ.toLinearEquiv x)
      hΨ.toLinearEquiv.surjective
  -- The underlying type of `F.obj (K.homology j)` is `ℚ ⊗[ℤ] H_j(X;ℤ)`, with the `ℤ`-module
  -- structure on `H_j(X;ℤ)` that is bundled in the `ModuleCat` object; commute the two tensor
  -- factors to put it in the form used by the bridge.  (The two tensor products have the same
  -- `ℤ`-module structure on `H_j(X;ℤ)` as `F.obj (K.homology j)`, which is *not* the structure
  -- type class synthesis picks for the bare type, hence the explicit instance below.)
  letI : Module ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) :=
    ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j).isModule
  have hsub : Subsingleton (TensorProduct ℤ
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) ℚ) := by
    have h2 : Subsingleton (TensorProduct ℤ ℚ
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j)) := hFsub
    exact Function.Surjective.subsingleton
      (f := fun x : TensorProduct ℤ ℚ
          ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) =>
        (TensorProduct.comm ℤ
          ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) ℚ).symm x)
      (TensorProduct.comm ℤ
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) ℚ).symm.surjective
  exact fun b => exists_nat_smul_eq_zero_of_subsingleton_tensorRat_module
    ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j).isModule hsub b

end

end Work.RatHurewicz
