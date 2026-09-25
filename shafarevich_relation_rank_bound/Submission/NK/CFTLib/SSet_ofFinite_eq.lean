import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank

namespace NK.CFTLib

theorem SSet_ofFinite_eq (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) :
    NK.GlobalCFTdeep.SSet
        {w : NK.GlobalCFT.Place F | ∃ q ∈ T, w = NK.GlobalCFT.Place.ofFinite q}
      = (T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) := by
  ext q
  simp only [NK.GlobalCFTdeep.mem_SSet, Finset.mem_coe]
  constructor
  · rintro ⟨q', hq', hqq'⟩
    rwa [NK.GlobalCFT.Place.ofFinite_inj.mp hqq']
  · intro hq
    exact ⟨q, hq, rfl⟩

end NK.CFTLib
