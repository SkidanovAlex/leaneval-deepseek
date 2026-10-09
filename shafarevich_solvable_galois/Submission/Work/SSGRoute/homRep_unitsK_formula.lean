import Mathlib
import Submission.Work.SSGRoute.homRepFormulaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt

theorem homRep_unitsK_formula {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    ∃ Φ : (M ⟶ SSGRoute.PTExt.unitsK k K) ≃+
        ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K M)),
      ∀ (f : M ⟶ SSGRoute.PTExt.unitsK k K) (x : M.V),
        (Φ f : Work.SSGRoute.homCoind k Ω K M) x =
          Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidWithZeroHom
            (Additive.toMul (Rep.Hom.hom f x))) := by
  refine ⟨AddEquiv.ofBijective (toCoindH0 M) (toCoindH0_bijective M), ?_⟩
  intro f x
  exact toCoindH0_apply M f x

end Work.SSGRoute
