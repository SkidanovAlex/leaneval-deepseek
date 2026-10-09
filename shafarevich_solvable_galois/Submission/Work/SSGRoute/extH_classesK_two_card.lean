import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.classFormation_ext
import Submission.Work.SSGRoute.pt_char_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The order of `H²(Gal(L/k), C_L)` in the `Ext` spelling.**

For a finite Galois extension `k ⊆ L` of number fields, the second `Ext`-cohomology of the idèle
class group `C_L` with coefficients in `ℤ` has order `|Gal(L/k)| = [L : k]`.  This is the order
computation of the class formation (`H²(G, C_L)` is cyclic of order `|G|`, the invariant map
`H²(G, C_L) ≅ ℤ/|G|`), transported from `NK`'s group-cohomology spelling to the `Ext`/`Coeff`
spelling of `SSGRoute.PTExt` along

* the `E0b` bridge `Work.SSGRoute.Bridge.E` (`groupCohomology A 2 ≃+ extH A 2`) and
* the coefficient-ring transfer
  `NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer`
  (`Coeff = ULift ℤ → ℤ`),

i.e. it is the `S = ⊤` case of `Work.SSGRoute.ClassFormation.extH_classesK_two_card_sub`, with the
restriction `Rep.res ⊤.subtype` avoided by running the comparison at the full group `Gal(L/k)`. -/
theorem extH_classesK_two_card (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    Nat.card (extH (classesK k L) 2) = Nat.card (L ≃ₐ[k] L) := by
  -- Hasse's fundamental class / the class formation: `H²(Gal(L/k), C_L)` has order `[L : k]`.
  have hFC := NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement
    NK.CFTLib.fundamentalClassElement
  -- the `Ext`-cohomology of the class formation is the group cohomology of `C_L`:
  -- `extH (classesK k L) 2 ≃+ H²(Gal(L/k), C_L)`.
  obtain ⟨e⟩ := extH_classesK_two_addEquiv k L
  rw [Nat.card_congr e.toEquiv, hFC.order]

end Work.SSGRoute
