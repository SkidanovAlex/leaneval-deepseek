import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.EscapeCoreLib.algEquiv_extend_compositum
import Submission.Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.EscapeCoreLib

theorem memGesUOfIsFrobAtPrime {K : Type} [Field K] [NumberField K]
    (M : Type) [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (hcomm : ∀ a b : Gal(M/K), a * b = b * a)
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hV : NK.GlobalCFT.Idele.normClassSubgroup K M = V)
    (art : NK.GlobalCFT.Idele K →* Gal(M/K))
    (hker : art.ker = NK.GlobalCFT.Idele.normImage K M ⊔ NK.GlobalCFT.Idele.principalSubgroup K)
    (hfrob : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      NK.HeckeL.IsUnramifiedIn (K := K) (L := M) 𝔮 →
      art (NK.HeckeL.ideleOfPrime K 𝔮) = NK.Chebotarev.frobAtPrime (K := K) (L := M) 𝔮)
    (x : NK.GlobalCFT.Idele K) (α : Gal(M/K)) (hα : art x = α)
    (𝔮 : NK.Chebotarev.PrimeIdeal K)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := M) 𝔮)
    (hF : NK.Chebotarev.IsFrobAtPrime (K := K) (L := M) 𝔮 α⁻¹) :
    NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮)
      * NK.GlobalCFT.IdeleClassGroup.mk K x ∈ V := by
  -- At the unramified prime `𝔮`, `α⁻¹` is a Frobenius element, hence (abelian case) it equals the
  -- chosen `frobAtPrime 𝔮`, which is the image of `ideleOfPrime 𝔮` under the Artin map.
  have h1 : art (NK.HeckeL.ideleOfPrime K 𝔮) = α⁻¹ := by
    rw [hfrob 𝔮 hunr]
    exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔮 hunr α⁻¹).mp hF
  -- Consequently `ideleOfPrime 𝔮 * x` lies in the kernel of the Artin map.
  have h2 : art (NK.HeckeL.ideleOfPrime K 𝔮 * x) = 1 := by
    rw [map_mul, h1, hα, inv_mul_cancel]
  have hmem : NK.HeckeL.ideleOfPrime K 𝔮 * x ∈
      NK.GlobalCFT.Idele.normImage K M ⊔ NK.GlobalCFT.Idele.principalSubgroup K := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr h2
  -- Passing to idèle classes, the principal part is annihilated by `mk`.
  have h3 : NK.GlobalCFT.IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K 𝔮 * x) ∈
      (NK.GlobalCFT.Idele.normImage K M ⊔ NK.GlobalCFT.Idele.principalSubgroup K).map
        (NK.GlobalCFT.IdeleClassGroup.mk K) :=
    Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [Subgroup.map_sup, NK.GlobalCFT.IdeleClassGroup.map_principalSubgroup_eq_bot,
    sup_bot_eq] at h3
  rw [← hV, NK.GlobalCFT.Idele.normClassSubgroup, ← map_mul]
  exact h3

end Work.SSGRoute.EscapeCoreLib
