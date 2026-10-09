import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
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
