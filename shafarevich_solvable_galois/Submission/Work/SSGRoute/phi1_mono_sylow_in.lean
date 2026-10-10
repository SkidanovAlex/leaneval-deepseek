import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Have
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.phi1_mono_pgroup_in
import Submission.Work.SSGRoute.phi1_sylow_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E6Ω: Sylow descent for `φ¹` (the target)

The `SylowIn` infrastructure lives in `Submission/Work/SSGRoute/sylow_in_defs.lean`, the level
bookkeeping (cases (i) and (ii) of the transfer, and the `Ω`-level inflation injectivity) in
`Submission/Work/SSGRoute/phi1_sylow_level.lean` and
`Submission/Work/SSGRoute/sylow_infl_injective.lean`; this module contains the target
`Work.SSGRoute.phi1_mono_sylow_in` (E6Ω).

Proof.  Let `P ≤ Gal(K/k)` be a `p`-Sylow subgroup fixing `ζ`, `k' := K^P` its fixed field.  The
base change `x'' := baseChangeExt M x ∈ Ext¹_{Gal(K/k')}(res M, C_{k'})`:
* `x''` has vanishing level values (`PhiOneVanishesIn Ω x''`): at levels that are Galois over `k`
  this is case (i) of the transfer, at the remaining levels case (ii) (normal closure + injectivity
  of the level inflation);
* `Gal(K/k') ≅ P` is a `p`-group, so E5Ω (`Work.SSGRoute.phi1_mono_pgroup_in`) gives `x'' = 0`;
* undoing the base-change isomorphism and using that `p ∤ [P : 1] = [Gal(K/k) : Gal(K/k')]`, the
  restriction `extRes P.subtype x` vanishes, hence `x = 0`
  (`Work.SSGRoute.SylowDesc.extRes_eq_zero_of_pTorsion`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open Work.SSGRoute.SylowIn
open Work.SSGRoute.SylowLevel

/-! ## The target -/

/-- **E6Ω.** If `μ_p ⊆ K`, `φ¹` is injective on `Ext¹_{Gal(K/k)}(M, C_K)` for every finite
`p`-torsion `M`, testing on the levels of `Ω` (descent to `k' = K^P`, `P` a `p`-Sylow). -/
theorem phi1_mono_sylow_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1) (hx : PhiOneVanishesIn Ω x) : x = 0 := by
  classical
  obtain ⟨P, hPgrp, hPidx, hPfix⟩ := exists_pSylow_le_fixingSubgroup (p := p) (k := k) (K := K) hζ
  let k'i : IntermediateField k K := IntermediateField.fixedField P
  haveI : NumberField ↥k'i := inferInstance
  haveI : FiniteDimensional k ↥k'i := inferInstance
  let x'' : Abelian.Ext (Rep.res (resBaseHom k ↥k'i K) M) (classesK ↥k'i K) 1 :=
    baseChangeExt (k := k) (k' := ↥k'i) (K := K) M x
  -- the level vanishing of the base-changed class
  have hx'' : PhiOneVanishesIn (k := ↥k'i) (K := K) Ω x'' :=
    phiOneVanishesIn_baseChangeExt (k := k) (k' := ↥k'i) (K := K) (Ω := Ω) M x
      (fun L' => hx L')
      (fun (L L' : IntermediateField K Ω) (hNF : NumberField L) (hNF' : NumberField L')
        (hFd : FiniteDimensional ↥k'i L) (hGal : IsGalois ↥k'i L)
        (hFd' : FiniteDimensional ↥k'i L') (hGal' : IsGalois ↥k'i L') (hLL : L ≤ L') => by
        haveI : NumberField L := hNF
        haveI : NumberField L' := hNF'
        haveI : FiniteDimensional ↥k'i L := hFd
        haveI : IsGalois ↥k'i L := hGal
        haveI : FiniteDimensional ↥k'i L' := hFd'
        haveI : IsGalois ↥k'i L' := hGal'
        exact SylowLevel.inflCIn_injective L L' hLL)
  -- E5Ω: `Gal(K/k')` is a `p`-group, so the base-changed class vanishes
  have hE5 : x'' = 0 :=
    phi1_mono_pgroup_in p ↥k'i K Ω
      (⟨ζ, mem_fixedField_of_forall P ζ hPfix⟩ : ↥k'i)
      (isPrimitiveRoot_fixedField P hζ hPfix) (isPGroup_fixedField P hPgrp)
      (Rep.res (resBaseHom k ↥k'i K) M) (fun m => hM m) x'' hx''
  -- undo the base change
  have hres : extRes (resBaseHom k ↥k'i K) x = 0 := by
    have h3 : (extRes (resBaseHom k ↥k'i K) x).comp (Abelian.Ext.mk₀
        (𝟙 (Rep.res (resBaseHom k ↥k'i K) (classesK k K)))) (add_zero 1) = 0 := hE5
    exact (Abelian.Ext.comp_mk₀_id (extRes (resBaseHom k ↥k'i K) x)).symm.trans h3
  -- transport to the Sylow subgroup `P` and use that `p ∤ P.index`
  have hpx : p • x = 0 := E6Util.ext_nsmul_p_torsion_left p hM x
  have h0 : extRes P.subtype x = 0 := by
    let e : (K ≃ₐ[↥k'i] K) ≃* ↥P := fixedFieldGalEquiv P
    have h2 : extRes e.toMonoidHom (extRes P.subtype x) = 0 :=
      ((SylowDesc.extRes_comp_aux (ψ := P.subtype) (φ := e.toMonoidHom) x).symm).trans hres
    refine (extRes_bijective_of_mulEquiv e (Rep.res P.subtype M)
      (Rep.res P.subtype (classesK k K)) 1).1 ?_
    show extRes e.toMonoidHom (extRes P.subtype x) = extRes e.toMonoidHom 0
    rw [h2, E6Util.extRes_zero]
  exact SylowDesc.extRes_eq_zero_of_pTorsion P p hPidx x hpx h0

end Work.SSGRoute
