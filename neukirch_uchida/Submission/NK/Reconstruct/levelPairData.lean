import Submission.NK.Reconstruct.assemblyGen
import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.hausRank
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.ReconstructField.LevelCandidate

/-!
# The level-pair bridge of the reconstruction step, as an interface

This module packages, in a single predicate, the statement that Shimizu's Theorem 4.0
(`NK.Reconstruct.exists_theta_of_prop4f3_data_gen`, `Submission/Work/Reconstruct/assemblyGen.lean`)
delivers the level isomorphisms of the reconstruction step from the local correspondence (a), the
Frobenius correspondence (b), Čebotarev and the rank inputs — **in the case in which the base field
`K₁` has a complex prime**.

## The mathematical content

Let `Ω` be a separable closure of `ℚ`, `K₁, K₂ : NumFieldIn ℚ Ω` finite number-field levels, and
`ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)` a homeomorphic isomorphism.  Write `K₁ := ↥K₁.L`, `K₂ := ↥K₂.L`
so that `ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)`.  Then

`NK.ReconstructField.LevelIsoInput ψ hψ`

is the assertion that every finite level `L/K₁` inside `Ω` is isomorphic to the corresponding level
`levelMap ψ L` of `K₂` — i.e. the *weak Neukirch–Uchida theorem at the level pair* `(L, levelMap ψ L)`
(Uchida's theorem, in the form in which `Submission/Work/ReconstructField/` uses it; it is the single
hypothesis `hlev` of `NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIso`).

`LevelIsoInputOfLocalData K₁ K₂ ℓ` says that this assertion follows from

* the local correspondence `a : LocalCorrespondence ψ` (CoNF (12.1.9)), and
* the Frobenius correspondence `b : FrobeniusCorrespondencePlace ψ hψ a` (Shimizu's Lemma 2.1.5), and
* a complex prime of `K₁`,
* and the rank inputs `HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen` and the
  Čebotarev input.

Since a complex prime of `K₁` is inherited by every finite level `L/K₁`
(`NK.Reconstruct.numberField_complex_of_le`, `Submission/Work/Reconstruct/fourf5Gen.lean`), the
complex prime of `K₁` supplies the hypothesis `hcomplex` of Shimizu's Proposition 4f.5 at *every*
level simultaneously: this is why the hypothesis is placed on `K₁` and not on the levels.

## The proof

For a finite level `L : IntermediateField ↥K₁.L Ω`, apply
`NK.Reconstruct.exists_isomorphism_of_prop4f3_data_gen` (Shimizu's Theorem 4.0,
`Submission/Work/Reconstruct/assemblyGen.lean`) with the base fields

* `K₁ := L` (i.e. the level, as a `NumFieldIn ℚ Ω`: it is finite over `↥K₁.L` and hence over `ℚ`,
  and a number field since `K₁` is one), and
* `K₂ := levelMap ψ L`,

and the auxiliary finite Galois level `Lₐᵤₓ/ℚ` a Galois-over-`ℚ` level of `Ω` containing both (for
instance the normal closure of `L ⊔ levelMap ψ L` over `ℚ`, or any sufficiently large finite Galois
level of `Ω/ℚ`).  Its hypotheses are supplied by

* the *restriction* of `ψ` to `L`, which is a homeomorphism
  `Gal(Ω/L) ≃* Gal(Ω/levelMap ψ L)` (the homeomorphism `NK.Reconstruct.levelMapEquiv ψ hψ L`, whose
  continuity and continuity of inverse are immediate from `hψ`);
* the isomorphism `σbar : Γ_L ≃* Γ_{levelMap ψ L}` induced by it
  (`NK.Reconstruct.exists_gammaEquivOfPhi`, whose continuity is
  `NK.Reconstruct.exists_gammaEquivOfPhi_continuous`);
* the prime bijection `PrimeIdeal ↥L ≃ PrimeIdeal ↥(levelMap ψ L)` induced by `a`
  (`NK.ReconstructField.levelPrimeMap ψ hψ a L`);
* the Frobenius correspondence `hb` at the level, which is the *defining property* of
  `FrobeniusCorrespondencePlace ψ hψ a` read through `NK.Reconstruct.IsFrobElementAt`
  (`NK.Chebotarev.IsFrobAt`);
* the preservation of the rational prime, from `a` (the prime below a corresponding prime);
* the section `Θ : Gal(Lₐᵤₓ.L/ℚ) → Ω ≃ₐ[ℚ] Ω` of the restriction map, from
  `NK.Reconstruct.exists_ringEquiv_extends`;
* a complex prime of `L`, from the complex prime of `K₁` (`numberField_complex_of_le`);
* `hc` and `Fourf5InputGen Ω ℓ`, the latter from the rank inputs
  (`NK.Reconstruct.fourf5_gen_of_rankInputs`).

## What is *not* in this interface

The complex prime of `K₁`.  Shimizu's proof of Theorem 4.0 removes it by the *totally imaginary
twist* (his Proposition 4f.6): one replaces `K₁` by `K₁L₀` with `L₀/ℚ` totally imaginary, applies the
machinery of 4f.3–4f.5 to `L₁ = K₁L₀` and to `L₁' = K₁L₀'` *with the same* `τ ∈ G(Lₐᵤₓ/ℚ)` (which is
where the exposed field equality `K₁.L = (Θ τ)⁻¹(K₂.L)` of
`NK.Reconstruct.exists_theta_of_prop4f3_data_gen` is needed), and intersects:
`K₁ = L₁ ∩ L₁' = τ(L₂ ∩ L₂') = τ(K₂)`.  Formalising the twist needs (i) the Galois-theoretic
linear-disjointness statements making `L₁ ∩ L₁' = K₁`, and (ii) the compatibility of the `σ̄`'s of the
several pairs along the base-change maps `π_{M/K}` (which follows from the Frobenius correspondence
(b) together with the topological generation of `Γ_K` by the Frobenius elements,
`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`).

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4
(Theorem 4.0, Lemma 4f.4, Propositions 4f.3, 4f.5, 4f.6).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The level-pair bridge of the reconstruction step, with a complex prime on `K₁`.** -/
def LevelIsoInputOfLocalData (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    (a : LocalCorrespondence ψ) (b : FrobeniusCorrespondencePlace ψ hψ a),
    (∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v) →
    HausRankInput Ω ℓ → RankStrictMonoLevelInputGen Ω ℓ → ResRankInputGen Ω ℓ →
    ChebotarevInput ℚ Ω → NK.ReconstructField.LevelIsoInput ψ hψ

/-- **The level-pair bridge of the reconstruction step, in full generality** (no complex prime).

Same statement as `NK.Reconstruct.LevelIsoInputOfLocalData` with the complex-prime hypothesis
removed.  This is Shimizu's Theorem 4.0 *without* the complex-prime hypothesis of Proposition 4f.5,
i.e. the assertion whose proof needs the **totally imaginary twist**: one replaces `K₁` by `K₁L₀`
with `L₀/ℚ` totally imaginary, applies 4f.3–4f.5 to `L₁ = K₁L₀` and to `L₁' = K₁L₀'` with the *same*
`τ ∈ G(Lₐᵤₓ/ℚ)` (using the exposed field equality `K₁.L = (Θ τ)⁻¹(K₂.L)` of
`NK.Reconstruct.exists_theta_of_prop4f3_data_gen`), and intersects:
`K₁ = L₁ ∩ L₁' = τ(L₂ ∩ L₂') = τ(K₂)`.

The complex-prime case is
`NK.Reconstruct.levelIsoInput_of_localCorrespondence_complexPrime`; what remains is (i) the
Galois-theoretic linear-disjointness statements making `L₁ ∩ L₁' = K₁`, and (ii) the compatibility of
the `σ̄`'s of the several pairs along the base-change maps `π_{M/K}` (Shimizu's chain
`σ̄_{L₁} ∘ π_{M/L₁} = π_{M₂/L₂} ∘ σ̄_{M₁} ∘ π_{M/M₁}`), which follows from the Frobenius
correspondence (b) together with the topological generation of `Γ_K` by the Frobenius elements
(`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`). -/
def LevelIsoInputOfLocalCorrespondence (K₁ K₂ : NumFieldIn ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (ψ : Gal(Ω/↥K₁.L) ≃* Gal(Ω/↥K₂.L)) (hψ : IsHomeomorph ψ)
    (a : LocalCorrespondence ψ) (b : FrobeniusCorrespondencePlace ψ hψ a),
    HausRankInput Ω ℓ → RankStrictMonoLevelInputGen Ω ℓ → ResRankInputGen Ω ℓ →
    ChebotarevInput ℚ Ω → NK.ReconstructField.LevelIsoInput ψ hψ

end NK.Reconstruct
