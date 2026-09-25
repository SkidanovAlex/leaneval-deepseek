import Mathlib
import Submission.CFTLib.NKProps
import Submission.Work.CFTLib.tate_neg_one
import Submission.Work.CFTLib.shafBound_of_fc
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.isUnramified_of_le
import Submission.Work.CFTLib.fiveTerm_finrank
import Submission.Work.CFTLib.invChar_le_invCharSubmodule
import Submission.Work.CFTLib.rankP_tate_le_invChar

/-! Guidance from the project lead (the requester):

# Guidance: glue — the relative Shafarevich bound (for infinite towers)
Definitions: `Submission/CFTLib/Interfaces.lean` (do not edit). Setting: K ⊆ K' finite Galois unramified p-extensions
of F, K' ⊇ every unramified abelian p-extension of K. G = Gal(K/F), G' = Gal(K'/F), N = Gal(K'/K) ◁ G'.
Claim: dim image(inf: H²(G,𝔽_p) → H²(G',𝔽_p)) ≤ dim H¹(G',𝔽_p) + ρ, ρ = r₁+r₂−1+δ_p(F).

## Decomposition (all pieces proved on disk)

With `G = Gal(K/F)`, `G' = Gal(K'/F)`, `N = ker (AlgEquiv.restrictNormalHom K) = Gal(K'/K)`:

* `Work.CFTLib.fiveTerm_finrank` (Hochschild–Serre): the inflation image satisfies
  `dim im(inf²) + dim H¹(N,𝔽_p)^{G'} + dim H¹(G,𝔽_p) = dim H²(G,𝔽_p) + dim H¹(G',𝔽_p)`;
* `Work.CFTLib.finrank_H2_eq_of_fc` (Tate–Nakayama + Schur):
  `dim H²(G,𝔽_p) = dim H¹(G,𝔽_p) + rank_p Ĥ⁻¹(G, C_K)`;
* `Work.CFTLib.rankP_tate_le_invChar` (Roquette's idèle computation, no class condition):
  `rank_p Ĥ⁻¹(G,C_K) ≤ (r₁+r₂−1) + δ_p(F) + c`, `c = dim (Cl_K ⊗ 𝔽_p)^G`;
* `Work.CFTLib.invChar_le_invCharSubmodule` (Hilbert `p`-class field / Artin):
  `c ≤ dim H¹(N,𝔽_p)^{G'}`;
* `Work.CFTLib.isUnramified_of_le`: unramifiedness descends to the subfield `K`.

The two middle statements combine to `rank_p Ĥ⁻¹(G,C_K) + dim H¹(G',𝔽_p) ≤ ρ + dim H¹(N)^{G'} + dim H¹(G',𝔽_p)`,
and `omega` then gives the claim.
-/

open NumberField CategoryTheory

namespace Work.CFTLib

/-- **(b) Tate + Schur.**  For a finite Galois extension `K/F` of number fields with `p`-group
`Gal(K/F)` and the fundamental-class hypothesis `hFC`, the relation-rank identity

`dim H²(G, 𝔽_p) = dim H¹(G, 𝔽_p) + rank_p Ĥ⁻¹(G, C_K)`,   `G = Gal(K/F)`,

holds: `H₂(G, ℤ) ≅ Ĥ⁻¹(G, C_K)` (Tate–Nakayama, `tate_neg_one`) and the Schur bridge
`dim H²(G, 𝔽_p) = dim H¹(G, 𝔽_p) + rank_p H₂(G, ℤ)`. -/
theorem finrank_H2_eq_of_fc (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (K ≃ₐ[F] K)) :
    Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) 2) =
      Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) 1)
        + Work.CFT.ClassFormation.rankP p
            ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1)) := by
  have hCFA : NK.GlobalCFT.CohomologicalFieldAxiom F K := classFormation_of_fc hFC
  obtain ⟨α, hα⟩ := hCFA.fundamentalClass
  obtain ⟨e⟩ := tate_neg_one p hG (NK.GlobalCFT.IdeleClassGroup.rep F K)
    hCFA.h1_trivial hCFA.h2_card α hα
  have hrankP : Work.CFT.ClassFormation.rankP p ↑(Work.CFT.ClassFormation.HnZ (K ≃ₐ[F] K) 2)
      = Work.CFT.ClassFormation.rankP p
          ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1)) :=
    Work.CFT.ClassFormation.rankP_eq_of_addEquiv p e
  rw [Work.CFT.ClassFormation.Schur.schur_bridge p (K ≃ₐ[F] K), hrankP]

theorem relShafBound_of_fcA (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hHCF : CFTLib.PClassFieldArtin) (hUAD : CFTLib.UnramifiedAbelianDegreeLe) :
    CFTLib.RelShafBound := by
  intro F K K' hF hNF hK hNK hK' hNK' hAlgFK hAlgFK' hAlgKK' hST hFDK hFDK' hGalK hGalK'
    p hp hG' hUnr' hmax
  have hG : IsPGroup p (K ≃ₐ[F] K) :=
    hG'.of_surjective (AlgEquiv.restrictNormalHom K)
      (AlgEquiv.restrictNormalHom_surjective K')
  have hUnr : CFTLib.IsUnramified F K := isUnramified_of_le hUnr'
  have hL1 := fiveTerm_finrank (F := F) (K := K) (K' := K') p
  have hL2 := rankP_tate_le_invChar hFC p hG hUnr
  have hL3 := invChar_le_invCharSubmodule hHCF hUAD (F := F) (K := K) (K' := K') p hG' hmax
  have hb := finrank_H2_eq_of_fc hFC p hG
  omega

end Work.CFTLib
