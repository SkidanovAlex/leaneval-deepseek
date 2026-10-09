import Mathlib
import Submission.Work.SSGRoute.glue_involution_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped Pointwise NumberField

/-- **Čebotarev, element form**: every element of the Galois group of a finite Galois extension of
number fields fixes some place. -/
theorem chebotarev_element_stabilizer (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (τ : L ≃ₐ[k] L) :
    ∃ w : NK.GlobalCFT.Place L, τ ∈ MulAction.stabilizer (L ≃ₐ[k] L) w := by
  have hinf : (NK.ChebotarevGeneral.frobSet (K := k) (N := L) τ).Infinite :=
    Work.SSGRoute.chebotarevInfinite_type0 k L τ
  obtain ⟨𝔭, h𝔭⟩ := hinf.nonempty
  rw [NK.ChebotarevGeneral.mem_frobSet] at h𝔭
  obtain ⟨P, _hP, hfrob⟩ := h𝔭
  refine ⟨NK.GlobalCFT.Place.ofFinite P, ?_⟩
  rw [Work.SSGRoute.mem_stabilizer_ofFinite_iff P τ]
  exact NK.Chebotarev.IsFrobAtStabilizes (K := k) (L := L) hfrob

end Work.SSGRoute.Sha2Lib
