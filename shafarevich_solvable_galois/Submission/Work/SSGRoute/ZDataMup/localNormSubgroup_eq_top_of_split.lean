import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.HassePrinciple.ideleInclusion_smul_of_restrict
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.NUV2.ArtinBridge.kummerE_le_normImage_of_isGalois_exp
import Submission.NK.NUV2.ChebAux.Transfer.cycClassOf_translation
import Submission.NK.NUV2.ChebAux.Transfer.locUnits_res_inflation_eq_zero
import Submission.NK.NUV2.LC.localNormFinite_range_iff_val_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

theorem localNormSubgroup_eq_top_of_split {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hsplit : ∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) :
    NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite Q) = ⊤ := by
  -- Pick a prime `q` of `𝓞 L` lying over `Q`; the hypothesis `hsplit` makes it split completely,
  -- so the local norm at `q` is surjective and its range is the whole local norm subgroup.
  obtain ⟨q, hq⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
  obtain ⟨he, hf⟩ := hsplit q hq
  rw [← NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup (K := K) (L := L) Q q hq]
  exact MonoidHom.range_eq_top.mpr fun x =>
    NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_surjective_of_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) (L := L) Q q hq he hf x

end Work.SSGRoute.ZDataMup
