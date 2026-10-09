import Mathlib
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.PTembedding.hilbert90_decomp
import Submission.Work.SSGRoute.PTembedding.kummerUnits_decomp_eq_local
import Submission.Work.SSGRoute.Nakayama.kummerH2
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
import Submission.Work.SSGRoute.Nakayama.ptorsion_nested_cyclic
import Submission.Work.SSGRoute.PT.HomFormReduction
import Submission.Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup
import Submission.Work.SSGRoute.PTCore.h2loc_mup_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-! In this import closure a competing `Module`/`DistribMulAction` instance for
`Additive (rootsOfUnity p K)` shadows the triple whose `SMulCommClass` companion is available,
so that typeclass search fails on `SMulCommClass Gal(K/k) (ZMod p) (MuAdd p K)`.  Raising the
priorities of the three matching instances (the fix recorded in
`PTCore/h2loc_mup_finrank.lean`) resolves this. -/
attribute [local instance 10000] Work.SSGRoute.PTCore.instModuleAddRootsOfUnityOfField
attribute [local instance 10000] Work.SSGRoute.PTCore.instSMulCommClassAddRootsOfUnityOfField
attribute [local instance 10000] Work.SSGRoute.PTembedding.MupKummer.instDistribMulActionAddRootsOfUnityOfField

namespace Work.SSGRoute.Nakayama

open Work.AbsoluteKummer

/-- The p-torsion of the local Brauer group in the units model is the second cohomology with
coefficients in the group of p-th roots of unity. -/
theorem card_ptorsion_eq_card_h2_muAdd
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Nat.card {x : H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) // p • x = 0} =
      Nat.card (H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K)) := by
  obtain ⟨_, _, _, e⟩ := kummer_h2_muAdd_pTorsion (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ hζK A hA
  obtain ⟨e⟩ := e
  exact (Nat.card_congr e.toEquiv).symm

/-- **The arithmetic core, finite-coefficient form**: the second continuous cohomology of the
decomposition group of a finite place, with coefficients in the group of p-th roots of unity, has
exactly p elements.

Reduction (all ingredients present in the workspace):

* `card_ptorsion_eq_card_h2_muAdd` (above) reduces the requested statement about the p-torsion of
  H2(D_A, Ω-units) to this finite-coefficient statement (Kummer plus Hilbert 90 at D_A).
* Model bridge: `Work.SSGRoute.PT.H2locEquivH2_decomp` identifies the local model `H2loc` with the
  continuous cohomology of `D_A`.
* Transfer to the completion: `Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup` identifies
  `H2loc p k Ω K (μ_p) (decomp k A)` with `H2(G_κ, μ_p)` for the local field
  `κ = k_𝔭` at the prime `𝔭` of `k` below `A`.
* Arithmetic: `Work.SSGRoute.PTdualControl.natCard_H2_rootsOfUnity_adicCompletion` computes
  `Nat.card H2(G_κ, μ_p) = p` from the level structure of the units, whose three properties
  (injectivity, nesting, covering) are the node `Work.SSGRoute.PTCore.H2_units_level_structure`. -/
theorem h2_muAdd_card
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Nat.card (H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K)) = p := by
  classical
  have harith : Nat.card (H2 (G (PTembedding.localFieldOf k A hA))
      (Additive (rootsOfUnity p (AlgebraicClosure (PTembedding.localFieldOf k A hA))))) = p :=
    PTdualControl.natCard_H2_rootsOfUnity_adicCompletion (p := p) (K := k)
      (Submission.NeukirchUchida.primeOf A hA)
      (PTCore.H2LevelStructure_adicCompletion (K := k) (Submission.NeukirchUchida.primeOf A hA))
  obtain ⟨e2⟩ := PTCore.h2loc_equiv_localGal_mup p k Ω K ζ hζ hζK A hA
  have hcard : Nat.card (H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K))
      = Nat.card (SSGRoute.H2loc p k Ω K (PTembedding.MupCard.MuAdd p K)
          (SSGRoute.decomp k A)) :=
    Nat.card_congr (PT.H2locEquivH2_decomp p k Ω K (PTembedding.MupCard.MuAdd p K) A).symm.toEquiv
  rw [hcard, Nat.card_congr e2.toEquiv]
  exact harith

/-- **The p-torsion of the local Brauer group of a finite place is one-dimensional** - the
arithmetic content of the cyclotomic (M = mu_p) base case of local Tate duality, and the
p-torsion part of the class-formation axiom (Milne, ADT, 1.1b).

The local Brauer group of the completion κ = k_v of k below the finite place A is
Br(κ) = ℚ/ℤ, and it is computed by the continuous-cochain model
Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) (here Ωˣ stands for
κ̄ˣ: every cohomology class is carried by a finite level, see the reduction below).  Its
p-torsion is therefore (ℚ/ℤ)[p] = 𝔽_p, of order p.

Reduction route (for the prover): per finite level L over κ the group H²(Gal(L/κ), Lˣ) has
order [L:κ] (the fundamental class is in the tree as
Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units,
and the reciprocity shape as Commons.…ArtinMap.addEquiv_tateCohomology_of_fundamental_class);
the inflation maps H²(Gal(L/κ), Lˣ) → H²(D_A, Ωˣ) are injective by Hilbert 90
(Work.SSGRoute.PTembedding.MupCard.hilbert90_decompH1); every locally constant 2-cocycle with
values in the union of the Lˣ has finite image, hence values in a single Lˣ (compactness of
D_A), so H²(D_A, Ωˣ) is the filtered colimit of the H²(Gal(L/κ), Lˣ); and a filtered colimit
of copies of 𝔽_p with injective transition maps is 𝔽_p.  (Nat.card of an infinite type is
0, so finiteness is part of the content.)

Consumer: Work.SSGRoute.Nakayama.kummer_h2_muAdd_ker identifies H²(D_A, μ_p) with
ker (mapH2 powPi), i.e. with this p-torsion group; combined with the statement here it gives
H²(D_A, μ_p) ≅ 𝔽_p, i.e. Hom_{D_A}(μ_p, μ_p) ≅ H²(D_A, μ_p)^∨. -/
theorem br_pTorsion (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Nat.card {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
      p • x = 0} = p := by
  classical
  obtain ⟨K, ζ, hζ, hζK, hfin, hgal⟩ := PTembedding.exists_galois_adjoin_primitiveRoot p k Ω
  haveI := hfin
  haveI := hgal
  rw [card_ptorsion_eq_card_h2_muAdd p k Ω K ζ hζ hζK A hA]
  exact h2_muAdd_card p k Ω K ζ hζ hζK A hA

end Work.SSGRoute.Nakayama
