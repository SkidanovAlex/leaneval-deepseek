import Mathlib
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORHomAlg.Bridge.BridgeDefs
import Submission.Work.ORHomAlg.Bridge.forgetInt_preservesHomology
import Submission.Work.ORHomAlg.Bridge.leftDerived_comp_of_exactFunctor
import Submission.Work.ORHomAlg.Bridge.balancedFunctorIso
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Tor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory

namespace Work.ORHomAlg.Bridge

universe u

/-- `Tor_n^R(S, M)` computed in the `ORCoherence` chapter agrees with
`Work.ORHomAlg.Tor R n S M` (forgetting the `S`-module structure), where `S` is regarded as a
right `R`-module via `(MulOpposite.op r) • s = s * f r` (pinned by `h`). -/
theorem torEquiv {R S : Type u} [Ring R] [Ring S] (f : R →+* S) [Module Rᵐᵒᵖ S]
    (h : ∀ (r : R) (s : S), (MulOpposite.op r) • s = s * f r)
    (hs : SMulCommClass S Rᵐᵒᵖ S)
    (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    Nonempty (Work.ORCoherence.Tor f n (ModuleCat.of R M) ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := R) n S M) := by
  -- The two balanced tensor functors are naturally isomorphic.
  obtain ⟨α⟩ := balancedTensor_comp_forgetInt_iso f h
  -- Hence their left derived functors are isomorphic.
  let β : ((CategoryTheory.Functor.comp (Work.ORCoherence.tensorFunctor f) (forgetInt S)).leftDerived n) ≅
      ((Work.ORHomAlg.tensorLeftFunctor (R := R) S).leftDerived n) :=
    { hom := NatTrans.leftDerived α.hom n
      inv := NatTrans.leftDerived α.inv n
      hom_inv_id := by
        rw [← NatTrans.leftDerived_comp, Iso.hom_inv_id α, NatTrans.leftDerived_id]
      inv_hom_id := by
        rw [← NatTrans.leftDerived_comp, Iso.inv_hom_id α, NatTrans.leftDerived_id] }
  -- The forgetful functor `ModuleCat S ⥤ ModuleCat ℤ` is exact, so it commutes with the
  -- left derived functors of `S ⊗[R] -`.
  obtain ⟨γ⟩ := leftDerived_comp_of_exactFunctor (Work.ORCoherence.tensorFunctor f) (forgetInt S)
    (ModuleCat.of R M) n
  exact ⟨(γ ≪≫ β.app (ModuleCat.of R M)).toLinearEquiv⟩

end Work.ORHomAlg.Bridge
