import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

/-- **E9's next leg, primitive form: localisation commutes with the Yoneda product.**

`extLoc w` (the `w`-component of a class with idèle coefficients, `PTDefs`) is `extRes` to the
decomposition group followed by the coefficient map `K_wˣ ↪ K_wˣ`; the Yoneda product
`yonedaPair z h = h ∘ z` is postcomposition.  The statement says that the `w`-component of the
*global* paired class is the *local* Yoneda product of the component of `z` with the restriction of
`h` — which is the primitive content of the "square" of `DESIGN_PT.md` §3 (`E8`) that E9 needs: the
design's assembly bullet 2 converts `ker(P¹(E) → Ext¹_G(E',C_K))` into the annihilator
`ann(loc H¹(k,E'))`, and that conversion is exactly "the sum of the local values of a global pair is
the global value", which is this statement read place by place (with E2's clause (i), injectivity of
the localisation, supplying the reconstruction).

*Level-freeness.*  No `∀ L ⊇ K` clause, no choice of local data: `z` and `h` are level-free and `w`
is a single place.

*Proof.*  Unfold `yonedaPair = ·.comp · rfl`, `extLoc = extRes · |>.comp (mk₀ ideleToLocalUnits)`,
use the functoriality `Abelian.Ext.mapExactFunctor_comp` for `extRes`, and finish with the
associativity of `Abelian.Ext.comp`
(`Abelian.Ext.comp_assoc_of_third_deg_zero`), then absorb `extHRestrict D h = extRes D h ∘ mk₀ 𝟙`
with `Abelian.Ext.mk₀_id_comp` / `Abelian.Ext.comp_mk₀_id` (note `unitRes f = 𝟙` definitionally).
The same computation is carried out *inside* the proof of
`Work.SSGRoute.Sha2Lib.yonedaPair_extToClasses_eq_zero_of_locTrivial` (the `have hloc` at line 87 of
`Submission/Work/SSGRoute/Sha2Lib/yonedaPair_extToClasses_eq_zero_of_locTrivial.lean`, in the
equivalent shape `(extRes D h).comp (extLoc w z) rfl`) — mirror that argument rather than
re-deriving it, but do **not** import that file unless it builds. -/
theorem extLoc_yonedaPair (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (z : Abelian.Ext.{0} M (idelesK k K) r) (h : extH M s) (w : NK.GlobalCFT.Place K) :
    extLoc (k := k) w (yonedaPair z h) =
      yonedaPair (extLoc (k := k) w z) (extHRestrict (decompK (k := k) w) h) := by
  -- `extHRestrict D h` is `extRes D.subtype h` up to the (definitionally trivial) coefficient
  -- map `mk₀ (unitRes D.subtype)` and the identity `mk₀ 𝟙` of the restricted module.
  have key : extHRestrict (decompK (k := k) w) h
      = extRes (decompK (k := k) w).subtype h := by
    rw [extHRestrict, extHMap]
    simp only [Abelian.Ext.comp_mk₀_id]
    exact Abelian.Ext.mk₀_id_comp _
  -- the `w`-component of the global product, with `extRes` pushed through the Yoneda product
  have hloc : extLoc (k := k) w (yonedaPair z h)
      = (extRes (decompK (k := k) w).subtype h).comp (extLoc (k := k) w z) rfl := by
    rw [yonedaPair, extLoc, extRes, Abelian.Ext.mapExactFunctor_comp]
    exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _
  rw [hloc, key]
  rfl

end Work.SSGRoute.PT
