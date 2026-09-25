import Mathlib
import Submission.CFTLib.NKProps
import Submission.Work.CFTLib.tate_neg_one
import Submission.Work.CFT.ClassFormation.Schur.Main
import Submission.Work.CFT.ClassFormation.rankP_eq_of_addEquiv

/-! Guidance from the project lead (the requester):

# Guidance: glue — ShafBound from the fundamental class and Roquette's bound
Definitions: `Submission/CFTLib/Interfaces.lean`, `Submission/CFTLib/NKProps.lean` (do not edit).
For K/F finite Galois with p-group G = Gal(K/F):
1. Class-formation hypotheses for C := `NK.GlobalCFT.IdeleClassGroup.rep F K`: H¹(H, res C) = 0 for every subgroup H
   (`NK.GlobalCFTdeep.H1All.*`, including the restriction lemmas there), |H²(H, res C)| = |H| and a class of order
   |G| — from `hFC` applied to K/K^H (fixed field) and to K/F, plus `natCard_groupCohomology_two_le_card`, and the
   transport res_H (rep F K) ≅ rep (K^H) K (look in `NK.GlobalCFTdeep` for existing restriction/fixed-field
   transports, e.g. around `subsingleton_groupCohomology_one_res_ideleClassGroup`, `IndexTransport`, `Transport`).
2. `Work.CFTLib.tate_neg_one` (PROVED, `Submission/Work/CFTLib/tate_neg_one.lean`): H₂(G,ℤ) ≃+ Ĥ⁻¹(G,C).
3. `Work.CFT.ClassFormation.Schur.schur_bridge`: dim H²(G,𝔽_p) = dim H¹(G,𝔽_p) + rankP p (H₂(G,ℤ)); rankP is invariant
   under ≃+ (`Work.CFT.ClassFormation.rankP_eq_of_addEquiv`).
4. `hIC` bounds rankP of Ĥ⁻¹(G, C) (note `rankP p A = finrank (ZMod p) (ZMod p ⊗[ℤ] A)`).
Make step 1 a separate lemma `classFormation_of_fc` (it is reused elsewhere).
-/

namespace Work.CFTLib

open scoped TensorProduct

/-- **The class-formation hypotheses from the fundamental class** (step 1 of the plan).

For a finite Galois extension `L/K` of number fields, the fundamental class hypothesis
`NK.GlobalCFTdeep.FundamentalClassElement` produces the cohomological field axiom for the idèle
class group formation `C := IdeleClassGroup.rep K L`:

* `H¹(H, res C) = 0` for every subgroup `H ≤ Gal(L/K)` (this half is unconditional in the
  workspace: `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup`);
* `|H²(H, res C)| = |H|` for every subgroup `H`, obtained from `hFC` applied to `L / L^H`
  (whose Galois group is `H`) together with Milne's inequality
  `natCard_groupCohomology_two_le_card` and the transport `res_H C_L ≅ C_L` for `L/L^H`;
* a fundamental class `α ∈ H²(G, C_L)` of additive order `|G|`. -/
theorem classFormation_of_fc (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    NK.GlobalCFT.CohomologicalFieldAxiom K L :=
  NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement hFC

/-- **Instance bridge for the idèle computation.**  `rankP p A` is defined as
`finrank (ZMod p) (ZMod p ⊗[ℤ] A)`; for `A = Ĥ⁻¹(G, C)` the tensor product carries the
`ℤ`-module structure of the `ModuleCat` while `rankP` uses the canonical one induced by the
additive group.  All `ℤ`-module structures on a type are equal
(`AddCommMonoid.subsingletonIntModule`), so the two readings agree:

`rank_p Ĥ⁻¹(G, C) ≤ c` whenever `finrank (ZMod p) (𝔽_p ⊗[ℤ] Ĥ⁻¹(G, C)) ≤ c`. -/
theorem rankP_tate_le_of_finrank_tensor {p : ℕ} {G : Type} [Group G] [Fintype G] (C : Rep ℤ G)
    {c : ℕ}
    (h : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (tateCohomology C (-1))) ≤ c) :
    Work.CFT.ClassFormation.rankP p ↑(tateCohomology C (-1)) ≤ c := by
  rw [Work.CFT.ClassFormation.rankP]
  have hinst :
      (@AddCommGroup.toIntModule ↥(tateCohomology C (-1)) (ModuleCat.isAddCommGroup _)
        : Module ℤ ↥(tateCohomology C (-1)))
      = (@ModuleCat.isModule ℤ _ (tateCohomology C (-1))
        : Module ℤ ↥(tateCohomology C (-1))) := Subsingleton.elim _ _
  rw [hinst]
  exact h

/-- **Shafarevich's bound for finite unramified `p`-extensions from the global fundamental
class and Roquette's idèle computation.**

For `K/F` a finite Galois `p`-extension of number fields, `T` a finite set of primes of `F`
splitting completely in `K` and generating the `p`-part of `Cl_K`:

`dim H²(G, 𝔽_p) ≤ dim H¹(G, 𝔽_p) + (r₁ + r₂ − 1) + δ_p(F) + |T|`   (`G = Gal(K/F)`).

The proof is the one described in the guidance:

* the fundamental class gives the class-formation hypotheses
  (`classFormation_of_fc`), hence, by Tate–Nakayama in degree `−1` (`tate_neg_one`),
  `H₂(G, ℤ) ≅ Ĥ⁻¹(G, C_K)`;
* the Schur bridge `dim H²(G,𝔽_p) = dim H¹(G,𝔽_p) + rank_p H₂(G,ℤ)`;
* `rankP_eq_of_addEquiv` transports the isomorphism, and `hIC` bounds
  `rank_p Ĥ⁻¹(G, C_K)`. -/
theorem shafBound_of_fc (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (hIC : CFTLib.RoquetteBound) :
    CFTLib.ShafBound := by
  intro F K hF hNF hK hNK hAlg hFD hGal p hp T hG hUnr hSplits hCC
  -- the class-formation hypotheses for `C := C_K` over `G = Gal(K/F)`
  have hCFA : NK.GlobalCFT.CohomologicalFieldAxiom F K := classFormation_of_fc hFC
  -- a fundamental class of order `|G|`
  obtain ⟨α, hα⟩ := hCFA.fundamentalClass
  -- Tate–Nakayama in degree `-1`: `H₂(G, ℤ) ≅ Ĥ⁻¹(G, C_K)`
  obtain ⟨e⟩ := tate_neg_one p hG (NK.GlobalCFT.IdeleClassGroup.rep F K)
    hCFA.h1_trivial hCFA.h2_card α hα
  -- transport `rank_p` along that isomorphism
  have hrankP : Work.CFT.ClassFormation.rankP p
        ↑(Work.CFT.ClassFormation.HnZ (K ≃ₐ[F] K) 2)
      = Work.CFT.ClassFormation.rankP p
        ↑(tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep F K) (-1)) :=
    Work.CFT.ClassFormation.rankP_eq_of_addEquiv p e
  -- Roquette's bound on the `p`-rank of `Ĥ⁻¹(G, C_K)`
  have hbound : Work.CFT.ClassFormation.rankP p
        ↑(Work.CFT.ClassFormation.HnZ (K ≃ₐ[F] K) 2) ≤
      NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1
        + CFTLib.delta F p + T.card := by
    rw [hrankP]
    exact rankP_tate_le_of_finrank_tensor _
      (hIC F K p hG T hUnr hSplits hCC)
  -- the Schur bridge converts the bound on `rank_p H₂(G, ℤ)` into the relation-rank bound
  rw [Work.CFT.ClassFormation.Schur.schur_bridge p (K ≃ₐ[F] K)]
  -- the two readings of `H¹`: `H1Fp` is an abbreviation of the cohomology of the trivial
  -- representation, but `finrank` records the (definitionally equal) terms differently
  have hnorm : Module.finrank (ZMod p)
        ↑(groupCohomology (Rep.trivial (ZMod p) (K ≃ₐ[F] K) (ZMod p)) 1)
      = Module.finrank (ZMod p) ↑(Work.Tower.Shafarevich.H1Fp p (K ≃ₐ[F] K)) := rfl
  rw [hnorm]
  omega

end Work.CFTLib
