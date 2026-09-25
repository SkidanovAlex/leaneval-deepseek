import Mathlib
import Submission.NK.CFTLib.roquetteDefs
import Submission.NK.CFTLib.roquette_plan
import Submission.NK.CFTLib.pRank
import Submission.NK.CFTLib.normQuotientSetup
import Submission.NK.CFTLib.pRank_units_le
import Submission.NK.CFTLib.pRank_normQuotientUnitImage_le
import Submission.NK.CFTLib.pRank_normQuotient_le_units_add_card

namespace NK.CFTLib

theorem finrank_normQuotient_le (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (K ≃ₐ[F] K)) (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (hunr : _root_.CFTLib.IsUnramified F K) (hT : _root_.CFTLib.SplitsAt F K T) (hclass : _root_.CFTLib.ClassCond F K p T) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (NK.CFTLib.normQuotient F K)) ≤
      NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1 + _root_.CFTLib.delta F p + T.card := by
  classical
  -- The `𝔽_p`-dimension of the unit part.
  have hunits : pRank p ↥(normQuotientUnitImage F K) ≤
      NumberField.Units.rank F + _root_.CFTLib.delta F p :=
    pRank_normQuotientUnitImage_le F K p
  -- The quotient of `normQuotient F K` by its unit part has `p`-rank at most `T.card`.
  have hcl : pRank p (normQuotient F K) ≤ pRank p ↥(normQuotientUnitImage F K) + T.card :=
    pRank_normQuotient_le_units_add_card F K p hG T hunr hT hclass
  have hmain : pRank p (normQuotient F K) ≤
      NumberField.Units.rank F + _root_.CFTLib.delta F p + T.card := by
    linarith
  -- `NumberField.Units.rank F = r₁ + r₂ - 1`.
  have hrank' : NumberField.Units.rank F =
      NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1 := by
    rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F]
  calc Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (normQuotient F K))
      = pRank p (normQuotient F K) := rfl
    _ ≤ NumberField.Units.rank F + _root_.CFTLib.delta F p + T.card := hmain
    _ = NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F - 1 + _root_.CFTLib.delta F p + T.card := by
        rw [hrank']

end NK.CFTLib
