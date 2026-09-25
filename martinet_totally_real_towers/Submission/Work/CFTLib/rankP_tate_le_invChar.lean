import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFTLib.rankP_hm1_ideleClass_le
import Submission.Work.CFTLib.rankP_h0_oUnits_le
import Submission.Work.CFTLib.rankP_hm1_clRep_le_invChar

namespace Work.CFTLib

open NumberField

/-- **The `𝔽_p`-rank of `Ĥ⁻¹(G, C_K)` is bounded by the unit rank of `F` plus the
`G`-invariant characters of `Cl(𝓞 K)`.**

This is the finite-level (and `𝔽_p`-rank) form of Roquette's idèle computation: for an
unramified Galois `p`-extension `K/F`, the equivariant exact sequence
`1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` (`J_K = ∏_w 𝒪_{K_w}ˣ` the unit idèles) has, in low Tate
cohomology, `Ĥ⁻¹(J_K) = 0` (Hilbert 90 for units at the unramified places), so that
`Ĥ⁻¹(G, C_K)` is an extension of a subquotient of `Ĥ⁻¹(G, Cl(𝓞 K))` by one of `Ĥ⁰(G, 𝒪_Kˣ)`.
Passing to `𝔽_p`-ranks and using Dirichlet's unit theorem
(`rank_p Ĥ⁰(G, 𝒪_Kˣ) ≤ r₁+r₂−1+δ_p(F)`) and the duality
`rank_p Ĥ⁻¹(G, Cl(𝓞 K)) ≤ dim_{𝔽_p} Hom(Cl(𝓞 K), 𝔽_p)^G` gives the bound. -/
theorem rankP_tate_le_invChar (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (K ≃ₐ[F] K)) (hUnr : CFTLib.IsUnramified F K) :
    Work.CFT.ClassFormation.rankP p ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1))
      ≤ (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1)
        + CFTLib.delta F p
        + Module.finrank (ZMod p) (Work.CFTLib.clInvariantChar F K p) := by
  have h1 : Work.CFT.ClassFormation.rankP p
        ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1))
      ≤ Work.CFT.ClassFormation.rankP p ↑(tateCohomology (oUnitsRep F K) 0)
        + Work.CFT.ClassFormation.rankP p ↑(tateCohomology (clRep F K) (-1)) :=
    rankP_hm1_ideleClass_le p hUnr
  have h2 : Work.CFT.ClassFormation.rankP p ↑(tateCohomology (oUnitsRep F K) 0)
      ≤ (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1)
        + CFTLib.delta F p :=
    rankP_h0_oUnits_le p
  have h3 : Work.CFT.ClassFormation.rankP p ↑(tateCohomology (clRep F K) (-1))
      ≤ Module.finrank (ZMod p) (Work.CFTLib.clInvariantChar F K p) :=
    rankP_hm1_clRep_le_invChar p
  omega

end Work.CFTLib
