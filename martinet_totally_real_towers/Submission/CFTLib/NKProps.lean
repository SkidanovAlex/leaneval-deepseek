import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.CFTLib.Interfaces

/-! Orchestrator-owned Props in the `NK` vocabulary (do not edit). -/

namespace CFTLib

/-- Roquette's idèle computation (proved in the neukirch workspace as `Work.CFTLib.roquette_bound`). -/
def RoquetteBound : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime],
    IsPGroup p (K ≃ₐ[F] K) → ∀ (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))),
    IsUnramified F K → SplitsAt F K T → ClassCond F K p T →
    Module.finrank (ZMod p)
        (TensorProduct ℤ (ZMod p) (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1))) ≤
      NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1 +
        delta F p + T.card

end CFTLib
