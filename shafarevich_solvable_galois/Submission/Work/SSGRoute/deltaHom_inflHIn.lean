import Mathlib
import Submission.Work.SSGRoute.phi1_lambda_defs
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level naturality of the connecting map `δ` under inflation along `L ≤ L'`

Target: `Work.SSGRoute.deltaHom_inflHIn` (node `E6Ω`/`E5s` coherence, companion of
`Work.SSGRoute.phiAt_level_infl`).

For finite Galois levels `k ⊆ K ⊆ L ⊆ L' ≤ Ω`, a short exact sequence `S` of `Gal(K/k)`-modules and
a class `j ∈ H¹(Gal(L/k), S.X₃)`, inflating the level-`L` connecting value
`δ_L(j) = j ∘ hS.extClass` along the canonical transport `Gal(L'/k) ↠ Gal(L/k)` equals the level-`L'`
connecting value of the inflated class:

`δ_{L'}(inflHIn h j) = inflHIn h (δ_L j)`.

The content is the bookkeeping of

* the functoriality of `Abelian.Ext.mapExactFunctor` under a composite of restriction functors
  (`extRes_comp_of_comp`, i.e. `ext_mapExactFunctor_comp_functor_aux` for `Rep.resFunctor`),
* the identification of the canonical transport `resResHom` with the `eqToHom` of the equality
  of group homomorphisms `galRes k K L' = (galRes k K L).comp (galRes k L L')`
  (`resResHom_eq_transport`),
* the associativity of the Yoneda product `Abelian.Ext.comp`,

all of it formal — no CFT input, no bridge, no choice.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ## Functoriality of `extRes` along a composite of group homomorphisms -/

/-- Restriction along a composite of group homomorphisms is the composite of the restrictions:
`extRes (ψ.comp φ) x = extRes φ (extRes ψ x)` (a restatement of
`Work.SSGRoute.SylowDesc.extRes_comp_aux`, proved here to avoid importing the Sylow layer). -/
theorem extRes_comp_of_comp {G G' G'' : Type} [Group G] [Group G'] [Group G'']
    (ψ : G' →* G) (φ : G'' →* G') {M A : Rep.{0} Coeff G} {n : ℕ}
    (x : Abelian.Ext.{0} M A n) :
    extRes (ψ.comp φ) x = extRes φ (extRes ψ x) := by
  rw [extRes, extRes, extRes]
  exact (ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor ψ) (Rep.resFunctor φ)
    n M A x).symm

/-! ## The canonical transport `resResHom` as an `eqToHom` -/

section ConcreteTransport

variable {k K L L₂ : Type} [Field k] [NumberField k] [Field K] [NumberField K]
  [Field L] [NumberField L] [Field L₂] [NumberField L₂] [Algebra k K] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [Algebra L L₂] [Algebra K L₂]
  [Algebra k L₂] [IsScalarTower k L L₂] [IsScalarTower K L L₂] [IsScalarTower k K L₂]
  [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional L L₂] [IsGalois L L₂]
  [FiniteDimensional k L₂] [IsGalois k L₂]

/-- The canonical transport `resResHom` between the two presentations of the `Gal(L₂/k)`-module
obtained from `M` is the `eqToHom` along the equality of group homomorphisms
`galRes k K L₂ = (galRes k K L).comp (galRes k L L₂)`. -/
theorem resResHom_eq_transport (hF : galRes k K L₂ = (galRes k K L).comp (galRes k L L₂))
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    resResHom (k := k) (K := K) (L := L) (L' := L₂) M
      = eqToHom (congrArg (fun t => Rep.res t M) hF.symm) := by
  show eqToHom _ = eqToHom _
  exact congrArg CategoryTheory.eqToHom (Subsingleton.elim _ _)

end ConcreteTransport

/-! ## The formal `Ext`-identity -/

/-- **Formal naturality of the connecting map.**  Abstract form of `deltaHom_inflHIn`, for group
homomorphisms `f : H →* G`, `g : I →* H`, the composite presentation `f₂` of `f ∘ g` and the
canonical transports `eqToHom` of the corresponding restriction of a module: composing the inflated
class `extHMap g ρ_A j` with the connecting class `extRes f₂ x` equals inflating the level-`H`
connecting class `j ∘ extRes f x`. -/
theorem extHMap_comp_extRes_transport {G H I : Type} [Group G] [Group H] [Group I]
    (f : H →* G) (g : I →* H) (f₂ : I →* G) (hf : f₂ = f.comp g)
    {A B : Rep.{0} Coeff G} (x : Abelian.Ext.{0} A B 1) (j : extH (Rep.res f A) 1) :
    ((extHMap g (eqToHom (congrArg (fun t => Rep.res t A) hf.symm)) j).comp
        (extRes f₂ x) (show 1 + 1 = 2 by norm_num) :
        Abelian.Ext.{0} (unitRep I) (Rep.res f₂ B) 2)
      = extHMap g (eqToHom (congrArg (fun t => Rep.res t B) hf.symm))
          (j.comp (extRes f x) (show 1 + 1 = 2 by norm_num)) := by
  cases hf
  rw [show (congrArg (fun t => Rep.res t A) (rfl : f.comp g = f.comp g)) = rfl from
        Subsingleton.elim _ _,
      eqToHom_refl,
      show (congrArg (fun t => Rep.res t B) (rfl : f.comp g = f.comp g)) = rfl from
        Subsingleton.elim _ _,
      eqToHom_refl]
  rw [extRes_comp_of_comp]
  unfold extHMap extRes
  simp only [Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.comp_mk₀_id, Abelian.Ext.comp_mk₀_id]
  exact Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (by norm_num) (by norm_num)

/-! ## The level naturality of `δ` -/

theorem deltaHom_inflHIn {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    {L L' : IntermediateField K Ω} [NumberField L] [NumberField L'] [FiniteDimensional k L]
    [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L'] (h : L ≤ L')
    (S : CategoryTheory.ShortComplex (Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)))
    (hS : S.ShortExact)
    (j : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) S.X₃) 1) :
    Work.SSGRoute.deltaHom (k := k) (K := K) (L := L') S hS
        (SSGRoute.PTExt.inflHIn (k := k) (K := K) h j)
      = SSGRoute.PTExt.inflHIn (k := k) (K := K) (M := S.X₁) h
          (Work.SSGRoute.deltaHom (k := k) (K := K) (L := L) S hS j) := by
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  haveI : IsGalois ↥L ↥L' := IsGalois.tower_top_of_isGalois k ↥L ↥L'
  have hF : galRes k K ↥L' = (galRes k K ↥L).comp (galRes k ↥L ↥L') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k K ↥L ↥L'
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflHLevel, deltaHom_apply]
  rw [resResHom_eq_transport (k := k) (K := K) (L := ↥L) (L₂ := ↥L') hF S.X₃,
    resResHom_eq_transport (k := k) (K := K) (L := ↥L) (L₂ := ↥L') hF S.X₁]
  exact extHMap_comp_extRes_transport (galRes k K ↥L) (galRes k ↥L ↥L') (galRes k K ↥L')
    hF hS.extClass j

end Work.SSGRoute
