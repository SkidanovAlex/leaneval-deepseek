/-
# Level naturality of the pairing `phiAt` under inflation along `L ≤ L'`

Target: `Work.SSGRoute.phiAt_level_infl` (node `E6Ω`/`E5s` coherence).

`inflCIn hLL (phiAt_L y h) = phiAt_{L'} y (inflHIn hLL h)` for finite Galois levels
`K ≤ L ≤ L' ≤ Ω`.

The proof is a two-step computation with the `Ext`-calculus of `PTDefs`:

* `PhiAtInfl.levelPair_restrict'` (the restriction-companion of `levelPair`, the statement of
  `Work.SSGRoute.SylowIn.levelPair_restrict` re-proved here) rewrites the inflated level-`L` value
  as the level-`L'` value at the *composite* group homomorphism
  `(galRes k K L).comp (galRes k L L')`, with the coefficient morphism
  `Rep.resMap (galRes k L L') (classIncl k K L) ≫ classIncl k L L'`;
* `PhiAtInfl.levelPair_transport` is a purely formal `Ext`-identity comparing the pairing at two
  propositionally equal group homomorphisms, given the transports of the coefficient morphism, of
  the cohomology class and of `extRes` (`PhiAtInfl.extRes_transport`);
* the transports are the canonical ones: `resResHom` for the coefficient module and for the
  `M`-module (`PhiAtInfl.resResHom_eq_eqToHom`, `PhiAtInfl.resResHom_comp_eqToHom`), the composite
  coefficient morphism is identified with the one-step one by `PhiAtInfl.classIncl_compat'`
  (morphism-level form of `Work.SSGRoute.classIncl_compat_apply`), and the cohomology class is
  transported by `PhiAtInfl.extHMap_comp_id_coeff`.

## Import note

The import list of the original skeleton included
`Submission.Work.SSGRoute.local_duality_ext` (through `phi1_mono_sylow_in`) *and*
`Submission.Work.SSGRoute.phi_pair_natural` (through `phi1_classIncl_compat`); the two are
inconsistent in the current workspace, since both `local_duality_ext` and `phiPushClass` declare
`Work.SSGRoute.pushClass` (importing both makes any module that needs them unloadable).  Likewise
`Submission.Work.SSGRoute.phi1_classIncl_compat_morph` has no compiled `.olean` in the workspace.
The ingredients those modules provide and that are used here (`levelPair_restrict`,
`comp_assoc_of_first_deg_zero`, the morphism-level `classIncl_compat`) are therefore re-proved below
in the auxiliary namespace `Work.SSGRoute.PhiAtInfl`.
-/

import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_classIncl_compat
import Submission.Work.SSGRoute.sylow_descend
import Submission.Work.SSGRoute.inflTrivIn_trans
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## Auxiliary `Ext`-calculus (re-proved here, see the import note) -/

namespace PhiAtInfl

/-- Associativity of `Ext.comp` when the first factor has degree `0`. -/
theorem comp_assoc_of_first_deg_zero {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z T : C} {a₂ a₃ : ℕ} (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z a₂)
    (γ : Abelian.Ext Z T a₃) :
    (α.comp β (zero_add a₂)).comp γ rfl = α.comp (β.comp γ rfl) (zero_add (a₂ + a₃)) := by
  exact Abelian.Ext.comp_assoc α β γ (zero_add a₂) rfl (by omega)

/-- **Restriction-companion of the level pairing.**  For group homs `f : H →* G`, `g : H' →* H`, a
class `x ∈ Ext^r_G(M, A)`, `h ∈ H^s(H, res f M)`, a coefficient morphism `ι : res f A ⟶ B` and its
composite `ι' = Rep.resMap g ι ≫ ιg`, restricting the value of the level pairing along `g` gives the
level pairing at the composite level.  (Statement of `Work.SSGRoute.SylowIn.levelPair_restrict`,
re-proved here because `phi1_mono_sylow_in` is not importable together with
`phi1_classIncl_compat` in the current workspace.) -/
theorem levelPair_restrict' {G H H' : Type} [Group G] [Group H] [Group H']
    (f : H →* G) (g : H' →* H) {M A : Rep Coeff G} {B : Rep Coeff H}
    {B' : Rep Coeff H'} (ι : Rep.res f A ⟶ B) (ιg : Rep.res g B ⟶ B')
    (ι' : Rep.res (f.comp g) A ⟶ B') {r s : ℕ} (x : Abelian.Ext M A r)
    (h : extH (Rep.res f M) s)
    (hι : Rep.resMap g ι ≫ ιg = ι') :
    extHMap g ιg (levelPair f ι x h)
      = levelPair (f.comp g) ι' x (extHMap g (𝟙 (Rep.res g (Rep.res f M))) h) := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor g)
        (Abelian.Ext.mapExactFunctor (Rep.resFunctor f) x) =
      Abelian.Ext.mapExactFunctor (Rep.resFunctor (f.comp g)) x := by
    simpa only [extRes] using (Work.SSGRoute.SylowDesc.extRes_comp_aux f g x).symm
  have hh : extHMap g (𝟙 (Rep.res g (Rep.res f M))) h
      = (Abelian.Ext.mk₀ (unitRes g)).comp (extRes g h) (zero_add s) := by
    simp only [extHMap, Abelian.Ext.comp_mk₀_id]
  rw [hh]
  simp only [levelPair, extHMap, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp, Abelian.Ext.mk₀_comp_mk₀, hι,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    comp_assoc_of_first_deg_zero]

/-- **Transport of `extRes` along an equality of group homomorphisms.**  If `f₁` and `f₂` are
propositionally equal and `σM`, `ρA` are the transports of the `M`- and `A`-modules along that
equality (as `eqToHom`), then `extRes f₂ x` is the transport of `extRes f₁ x`. -/
theorem extRes_transport {G H : Type} [Group G] [Group H]
    {A M : Rep Coeff G} {r : ℕ} (x : Abelian.Ext M A r)
    {f₁ f₂ : H →* G} (hf : f₂ = f₁) :
    extRes f₂ x = ((Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M) hf))).comp
        (extRes f₁ x) (zero_add r)).comp
        (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))) (add_zero r) := by
  cases hf
  simp [CategoryTheory.eqToHom_refl, Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

/-- **Comparison of the level pairing at two propositionally equal group homomorphisms.**  This is
purely formal `Ext`-algebra: given the transports `ρA : res f₁ A ⟶ res f₂ A`,
`ρM : res f₁ M ⟶ res f₂ M`, `σM : res f₂ M ⟶ res f₁ M` with `ρM ≫ σM = 𝟙`, the compatible
transports `hι`, `hh` of the coefficient morphism and of the cohomology class, and the transport
`hx` of `extRes`, the level pairings agree. -/
theorem levelPair_transport {G H : Type} [Group G] [Group H]
    {A M : Rep Coeff G} {B' : Rep Coeff H} {r s : ℕ}
    {f₁ f₂ : H →* G} (x : Abelian.Ext M A r)
    (ρA : Rep.res f₁ A ⟶ Rep.res f₂ A) (ρM : Rep.res f₁ M ⟶ Rep.res f₂ M)
    (σM : Rep.res f₂ M ⟶ Rep.res f₁ M) (hρσM : ρM ≫ σM = 𝟙 _)
    (ι₁ : Rep.res f₁ A ⟶ B') (ι₂ : Rep.res f₂ A ⟶ B')
    (h₁ : extH (Rep.res f₁ M) s) (h₂ : extH (Rep.res f₂ M) s)
    (hι : ι₁ = ρA ≫ ι₂)
    (hh : h₂ = h₁.comp (Abelian.Ext.mk₀ ρM) (add_zero s))
    (hx : extRes f₂ x = ((Abelian.Ext.mk₀ σM).comp (extRes f₁ x) (zero_add r)).comp
        (Abelian.Ext.mk₀ ρA) (add_zero r)) :
    levelPair f₁ ι₁ x h₁ = levelPair f₂ ι₂ x h₂ := by
  subst hι
  subst hh
  simp only [levelPair]
  rw [hx]
  simp only [Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀_assoc,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    hρσM, Abelian.Ext.mk₀_id_comp]

/-- **The cohomology class of the composite coefficient morphism**: inflating along `g` with a
coefficient morphism `ι` is post-composing the inflation with the identity coefficient morphism by
`mk₀ ι`.  (Formal `Ext`-algebra.) -/
theorem extHMap_comp_id_coeff {G H : Type} [Group G] [Group H] (g : H →* G) {A : Rep Coeff G}
    {B : Rep Coeff H} (ι : Rep.res g A ⟶ B) {s : ℕ} (h : extH A s) :
    extHMap g ι h = (extHMap g (𝟙 (Rep.res g A)) h).comp (Abelian.Ext.mk₀ ι) (add_zero s) := by
  simp only [extHMap, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_mk₀_id]

/-! ## The canonical transports at a tower of number fields -/

section Concrete

variable {k K L L₂ : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Field L₂] [NumberField L₂] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [Algebra L L₂] [Algebra K L₂]
    [Algebra k L₂] [IsScalarTower k L L₂] [IsScalarTower K L L₂] [IsScalarTower k K L₂]
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional L L₂] [IsGalois L L₂]
    [FiniteDimensional k L₂] [IsGalois k L₂]

/-- **`resResHom` is the `eqToHom` of the equality of the two presentations of the composite
level.**  Its defining proof and `congrArg` of the group-hom equality are two proofs of the same
proposition. -/
theorem resResHom_eq_eqToHom (hF : galRes k K L₂ = (galRes k K L).comp (galRes k L L₂))
    (M : Rep Coeff (K ≃ₐ[k] K)) :
    resResHom (k := k) (K := K) (L := L) (L' := L₂) M
      = eqToHom (congrArg (fun t => Rep.res t M) hF.symm) := by
  show eqToHom _ = eqToHom _
  exact congrArg CategoryTheory.eqToHom (Subsingleton.elim _ _)

/-- **`resResHom` is inverse to its transpose.** -/
theorem resResHom_comp_eqToHom (hF : galRes k K L₂ = (galRes k K L).comp (galRes k L L₂))
    (M : Rep Coeff (K ≃ₐ[k] K)) :
    resResHom (k := k) (K := K) (L := L) (L' := L₂) M
      ≫ eqToHom (congrArg (fun t => Rep.res t M) hF) = 𝟙 _ := by
  rw [resResHom_eq_eqToHom (k := k) (K := K) (L := L) (L₂ := L₂) hF M,
    CategoryTheory.eqToHom_trans]
  exact CategoryTheory.eqToHom_refl _ _

/-- **Morphism-level compatibility of `classIncl` with a tower of levels**, in pointwise form:
the composite `C_K → C_L → C_{L₂}` of canonical inclusions and `resResHom ≫ classIncl k K L₂`
agree (this is `Work.SSGRoute.classIncl_compat_apply`, transported to the morphism level). -/
theorem classIncl_compat_fun (y : (classesK k K).V) :
    (Rep.Hom.hom (Rep.resMap (galRes k L L₂) (classIncl k K L) ≫ classIncl k L L₂)) y =
      (Rep.Hom.hom (resResHom (k := k) (K := K) (L := L) (L' := L₂) (classesK k K) ≫
        classIncl k K L₂)) y := by
  rw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.comp_apply, Rep.resMap_hom_apply,
    Work.SSGRoute.resResHom_hom_apply]
  exact Work.SSGRoute.classIncl_compat_apply (k := k) (K := K) (L := L) (L₂ := L₂) y

/-- **Morphism-level compatibility of `classIncl` with a tower of levels.** -/
theorem classIncl_compat' :
    Rep.resMap (galRes k L L₂) (classIncl k K L) ≫ classIncl k L L₂ =
      resResHom (k := k) (K := K) (L := L) (L' := L₂) (classesK k K) ≫ classIncl k K L₂ := by
  apply Rep.hom_ext
  ext y
  exact classIncl_compat_fun y

end Concrete

end PhiAtInfl

/-- **Level naturality of the pairing `phiAt` under inflation along `L ≤ L'`.**

For finite Galois levels `K ≤ L ≤ L' ≤ Ω` of a fixed algebraically closed `Ω ⊇ K`, a class
`y ∈ Ext¹_G(M, C_K)` (any `M`), and `h ∈ H¹(Gal(L/k), M)`: inflating the level-`L` pairing value
`phiAt_L y h` along the canonical inclusion `C_L → C_{L'}` equals the level-`L'` pairing value of the
*inflated* class `inflHIn hLL h`, i.e.

`inflCIn hLL (phiAt_L y h) = phiAt_{L'} y (inflHIn hLL h)`.

Both sides lie in `extH (classesK k L') 2`.  This is the `λ`-coherence hypothesis used to glue the
levelwise functionals `λ_L` of node `E5s` (`Work.SSGRoute.phi1_mono_step_in`) into a *compatible*
family over the levels of `Ω` (the input of `E4Ω`), and it is *unconditional*: it needs neither the
bridge `E0b` nor `E4Ω` nor any CFT input. -/
theorem phiAt_level_infl {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (L L' : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (hLL : L ≤ L') (M : Rep Coeff (K ≃ₐ[k] K)) (y : Abelian.Ext M (classesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) :
    inflCIn (k := k) hLL (phiAt (k := k) (K := K) (L := L) y h)
      = phiAt (k := k) (K := K) (L := L') y (inflHIn (k := k) hLL h) := by
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥L' := Module.Finite.of_restrictScalars_finite k ↥L ↥L'
  haveI : IsGalois ↥L ↥L' := IsGalois.tower_top_of_isGalois k ↥L ↥L'
  have hF : galRes k K ↥L' = (galRes k K ↥L).comp (galRes k ↥L ↥L') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k K ↥L ↥L'
  simp only [inflCIn, phiAt, inflHIn, inflC, inflHLevel]
  rw [PhiAtInfl.levelPair_restrict' (galRes k K ↥L) (galRes k ↥L ↥L') (classIncl k K ↥L)
    (classIncl k ↥L ↥L') (Rep.resMap (galRes k ↥L ↥L') (classIncl k K ↥L) ≫ classIncl k ↥L ↥L')
    y h rfl]
  refine PhiAtInfl.levelPair_transport (r := 1) (s := 1) (x := y)
    (f₁ := (galRes k K ↥L).comp (galRes k ↥L ↥L')) (f₂ := galRes k K ↥L')
    (ρA := resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') (classesK k K))
    (ρM := resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') M)
    (σM := eqToHom (congrArg (fun t => Rep.res t M) hF))
    (ι₁ := Rep.resMap (galRes k ↥L ↥L') (classIncl k K ↥L) ≫ classIncl k ↥L ↥L')
    (ι₂ := classIncl k K ↥L')
    (h₁ := extHMap (galRes k ↥L ↥L')
      (𝟙 (Rep.res (galRes k ↥L ↥L') (Rep.res (galRes k K ↥L) M))) h)
    (h₂ := extHMap (galRes k ↥L ↥L') (resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') M) h)
    ?_ ?_ ?_ ?_
  · exact PhiAtInfl.resResHom_comp_eqToHom (k := k) (K := K) (L := ↥L) (L₂ := ↥L') hF M
  · exact PhiAtInfl.classIncl_compat' (k := k) (K := K) (L := ↥L) (L₂ := ↥L')
  · exact PhiAtInfl.extHMap_comp_id_coeff (galRes k ↥L ↥L')
      (resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') M) h
  · rw [PhiAtInfl.extRes_transport (x := y) (f₁ := (galRes k K ↥L).comp (galRes k ↥L ↥L'))
      (f₂ := galRes k K ↥L') hF,
      ← PhiAtInfl.resResHom_eq_eqToHom (k := k) (K := K) (L := ↥L) (L₂ := ↥L') hF
        (classesK k K)]

namespace Work.SSGRoute

/-- Restatement of `Work.SSGRoute.phiAt_level_infl` under the namespace `Work.SSGRoute`
(interface compatibility: the skeleton of this file declared the target here). -/
theorem phiAt_level_infl {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (L L' : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (hLL : L ≤ L') (M : Rep Coeff (K ≃ₐ[k] K)) (y : Abelian.Ext M (classesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) :
    inflCIn (k := k) hLL (phiAt (k := k) (K := K) (L := L) y h)
      = phiAt (k := k) (K := K) (L := L') y (inflHIn (k := k) hLL h) :=
  _root_.Work.SSGRoute.phiAt_level_infl L L' hLL M y h

end Work.SSGRoute

end Work.SSGRoute
