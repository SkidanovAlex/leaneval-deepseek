import Submission.Work.SSGRoute.eb_arch_imports
import Submission.NK.CFTLib.HRclean.T3Bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of the level inflation `H²(Gal(L/k), Lˣ) → H²(Gal(E/k), Eˣ)`

For a tower of finite Galois number fields `k ⊆ L ⊆ E`, the inflation map of
`Submission/NK/NUV2/ARL/HR/TransferSupport.lean` is injective: Hilbert 90 for the finite Galois
extension `E/L` (giving `H¹(Gal(E/L), Eˣ) = 0`) together with the five-term inflation–restriction
exactness.  The factorization of the inflation through the ambient inflation is
`NK.CFTLib.HRclean.T3.unitsDescentIso_inv_comp_inflation`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.SSGRoute

/-- **Injectivity of the level inflation `H²(Gal(L/k), Lˣ) → H²(Gal(E/k), Eˣ)`** for a tower of
finite Galois number fields `k ⊆ L ⊆ E`. -/
theorem eb_arch_infl_injective {k L E : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Field E] [NumberField E] [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional k E] [IsGalois k L] [IsGalois k E] :
    Function.Injective ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom) := by
  haveI hfdLE : FiniteDimensional L E := Module.Finite.of_restrictScalars_finite k L E
  haveI hgalLE : IsGalois L E := IsGalois.tower_top_of_isGalois k L E
  -- the renamed copy of the inflation
  have hcopy : (NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E))
      = (NK.CFTLib.HRclean.ARL.inflation (K := k) (L := L) (E := E)) := rfl
  rw [hcopy]
  -- the factorization of the inflation through the ambient one
  have hfac := NK.CFTLib.HRclean.T3.unitsDescentIso_inv_comp_inflation
    (K := k) (M := L) (E := E)
  have hH1 : Subsingleton (groupCohomology
      (Rep.res (NK.CFTLib.HR.TransferAux.rN k L E).subtype
        (NK.CFTLib.HRclean.T3.urep k E)) 1) :=
    NK.CFTLib.HRclean.T3.subsingleton_H1_res_rn (K := k) (M := L) (E := E)
  have hinf : Function.Injective ⇑((groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0}
      (NK.CFTLib.HR.TransferAux.rN k L E) 2).app (NK.CFTLib.HRclean.T3.urep k E)).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general
      (NK.CFTLib.HR.TransferAux.rN k L E) (NK.CFTLib.HRclean.T3.urep k E) hH1
  have hmain : (NK.CFTLib.HRclean.ARL.inflation (K := k) (L := L) (E := E))
      = (NK.CFTLib.HRclean.T3.unitsDescentIso (K := k) (M := L) (E := E)).hom ≫
        (groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0}
          (NK.CFTLib.HR.TransferAux.rN k L E) 2).app (NK.CFTLib.HRclean.T3.urep k E) := by
    rw [← hfac, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hmain]
  intro a b hab
  rw [ModuleCat.comp_apply] at hab
  have h2 : (NK.CFTLib.HRclean.T3.unitsDescentIso (K := k) (M := L) (E := E)).hom a
      = (NK.CFTLib.HRclean.T3.unitsDescentIso (K := k) (M := L) (E := E)).hom b := hinf hab
  have h4 := congrArg (fun z => (NK.CFTLib.HRclean.T3.unitsDescentIso
    (K := k) (M := L) (E := E)).inv z) h2
  simpa only [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply] using h4

end Work.SSGRoute
