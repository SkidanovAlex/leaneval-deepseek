import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.TameStructureDeep.Tame.zl2ResidueChar_of_localFieldInputs
import Submission.NK.PTorsionTop.Main
import Submission.NK.PTorsionTop.Basic
import Submission.NK.LocalCFT.Units.Invariants
import Submission.NK.LocalInputs.InputsOfUnits
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
import Submission.NK.Mine.ResidueCharAutomatic

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FiniteDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
Yamagata/Jarden–Ritter), `UchidaKummer.IsWeakUchida`, `CyclicPrimeReduction`.
The new wall is `NK.NUV2.ChaptersV2` (`Submission/Work/NUV2/Wall.lean`, do NOT edit): the four inputs of the proved
`NK.EndgameRepair.exists_sigma_of_correctedResiduals`. Library inputs being proved elsewhere in this workspace and
allowed as hypotheses where the statement has them: `NK.GlobalCFTdeep.FundamentalClassElement` (global
fundamental class ⇒ class-formation axioms, reciprocity C_K/N C_L ≅ Gal(L/K)ᵃᵇ via
`artinReciprocity_of_cohomologicalFieldAxiom`, Tate's theorem, Albert–Brauer–Hasse–Noether) and
`NK.LocalArtin.KernelCondition` at every completion (⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
Design rules: state every local isomorphism as a CONTINUOUS isomorphism (ϕ is a homeomorphism; this removes
Nikolov–Segal entirely); for Brauer arguments use an ODD prime p (Br(ℝ)[p] = 0). Instantiate every new sub-statement
at K = ℚ and at the quartic above as a satisfiability check before relying on it. Delegate; one lemma per step.
## This lemma: leaf 6. From G^ab: local CFT (`hKC` ⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`) gives G_κ^{ab} ≅ profinite completion of κ^×; then the residue characteristic p is the unique prime ℓ such that G^{ab} has a quotient ℤ_ℓ² (κ^× ≅ ℤ × μ × ℤ_p^d), and [κ:ℚ_p] = d = ℤ_p-rank − 1. A continuous ≃ₜ* induces a continuous iso of abelianisations. Do NOT use `LocalInputs.LocalGaloisInputs` (its `p_torsion_iff`/`HasPTorsionAbelianization` was refuted earlier); tower ranks / Nikolov–Segal are not needed.

## Implementation (this file)

Everything used here is *proved* in the workspace; the only hypothesis is `hKC`.

* `hKC` at a place gives `NK.LocalCFT.ArtinReciprocity κ κ̄`, hence (by
  `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion`) the infinite level reciprocity
  isomorphism `κˣ^{∧} ≃* Gal(κ^{ab}/κ)`;
* the residue characteristic: Shimizu's detector `NK.LocalTame.Zl2ResidueChar`
  (`NK.TameStructureDeep.Tame.zl2ResidueChar_of_localFieldInputs`), whose `ℓ ≠ p` half is
  unconditional (`not_hasZl2Quotient_of_ne_resCharAt`) and whose `ℓ = p` half is the `ℤ_p²`-detector
  for the units (`NK.Mine.hasZl2Quotient_completionUnits_iff`);
* the absolute degree: the `p`-Frattini rank of the topological abelianisation
  `Gal(κ̄/κ) ⧸ closure([G,G])` is `[κ:ℚ_p] + 1 + δ`, with `δ = 1 ⟺ ζ_p ∈ κ`; this is proved from the
  power-class count `|κˣ/(κˣ)^p| = p^{[κ:ℚ_p]+1+δ}` (discharged *unconditionally* for a genuine
  completion by `NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime`;
  `NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion`) transferred along reciprocity
  (`NK.LocalCFT.hasFrattiniRank_AbGal_of_datum`);
* `δ` itself is the `p`-torsion of the *topological* abelianisation
  (`NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta`), an invariant of a *homeomorphic*
  isomorphism (`NK.PTorsionTop.hasPTorsionAbelianizationTop_congr_iff`) — this is why the
  hypothesis is a continuous isomorphism.

No hypothesis of the refuted `LocalGaloisInputs` kind (Ivanov tower ranks, Nikolov–Segal openness,
abstract `HasPTorsionAbelianization`) is used anywhere.
-/

set_option linter.style.haveILetI false

namespace NK.NUV2.LC

open IsDedekindDomain

/-! ## Auxiliary facts about the topological abelianisation -/

/-- **Transport of the `p`-Frattini rank of the topological abelianisation along a homeomorphic
isomorphism.**  A two-sided continuous isomorphism carries the closure of the commutator subgroup
onto the closure of the commutator subgroup
(`NK.PTorsionTop.map_topologicalClosure_commutator_eq`), hence induces an isomorphism of the
topological abelianisations. -/
theorem hasFrattiniRank_topologicalAbelianization_congr {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T1Space G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T1Space H] (e : G ≃ₜ* H) {p r : ℕ}
    (h : NK.LocalAnabelian.HasFrattiniRank p r (G ⧸ (commutator G).topologicalClosure)) :
    NK.LocalAnabelian.HasFrattiniRank p r (H ⧸ (commutator H).topologicalClosure) :=
  NK.LocalAnabelian.hasFrattiniRank_congr
    (QuotientGroup.congr ((commutator G).topologicalClosure) ((commutator H).topologicalClosure)
      (e : G ≃* H) (NK.PTorsionTop.map_topologicalClosure_commutator_eq e)) h

/-- **The `p`-Frattini rank of the topological abelianisation from the rank of the maximal abelian
subextension**: `Gal(F'/F) ⧸ closure([G_F,G_F]) ≃* Gal(F^{ab}/F)`
(`NK.PTorsionTop.quotientTopologicalClosureCommEquivAbGal`). -/
theorem hasFrattiniRank_topologicalAbelianization_of_abGal {F : Type*} {F' : Type*} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] {p r : ℕ}
    (h : NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalCFT.AbGal F F')) :
    NK.LocalAnabelian.HasFrattiniRank p r
      (Gal(F'/F) ⧸ (commutator Gal(F'/F)).topologicalClosure) :=
  NK.LocalAnabelian.hasFrattiniRank_congr
    (NK.PTorsionTop.quotientTopologicalClosureCommEquivAbGal (F := F) (F' := F')).symm h

/-- **The `p`-Frattini rank of the topological abelianisation of `Gal(K'/κ)` is
`[κ : ℚ_p] + 1 + δ`,** where `δ = 1` iff `ζ_p ∈ κ`.

This is the `p`-rank invariant from which the absolute degree `[κ : ℚ_p]` is read off.  Its
arithmetic content is the power-class count `|κˣ/(κˣ)^p| = p^{[κ:ℚ_p]+1+δ}` — proved for a genuine
completion by `NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime` — and local reciprocity
`D`. -/
theorem hasFrattiniRank_topologicalAbelianization_adicCompletion {K : Type*} [Field K]
    [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (D : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K') :
    NK.LocalAnabelian.HasFrattiniRank p
      (NK.LocalInputs.localDegree K 𝔭 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K))
      (Gal(K'/𝔭.adicCompletion K) ⧸
        (commutator Gal(K'/𝔭.adicCompletion K)).topologicalClosure) := by
  haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
  exact hasFrattiniRank_topologicalAbelianization_of_abGal
    (NK.LocalCFT.hasFrattiniRank_AbGal_of_datum D
      (NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion 𝔭
        (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hchar)))

/-! ## The main theorem -/

theorem localArithInvariants (hKC : NK.NUV2.KCAll) : NK.NUV2.LocalArithInvariants := by
  intro K₁ K₂ _ _ _ _ 𝔭 𝔮 hΦ
  obtain ⟨Φ⟩ := hΦ
  -- the two residue characteristics, as explicit local definitions
  set p : ℕ := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) with hp_def
  set q : ℕ := ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) with hq_def
  have hp : p.Prime := by
    rw [hp_def]
    exact NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hq : q.Prime := by
    rw [hq_def]
    exact NK.Mine.prime_ringChar_residueField_adicCompletion 𝔮
  have hcharp : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p := by
    rw [hp_def]
    exact NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  have hcharq : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q := by
    rw [hq_def]
    exact NK.Mine.charP_ringChar_residueField_adicCompletion 𝔮
  -- local class field theory at the two places, from `hKC`
  have D₁ : NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
      (SeparableClosure (𝔭.adicCompletion K₁)) :=
    (NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion 𝔭 (hKC K₁ 𝔭).some).some
  have D₂ : NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
      (SeparableClosure (𝔮.adicCompletion K₂)) :=
    (NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion 𝔮 (hKC K₂ 𝔮).some).some
  haveI : IsGalois (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) :=
    IsSepClosure.isGalois
  haveI : IsGalois (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) :=
    IsSepClosure.isGalois
  -- Shimizu's detector of the residue characteristic at both places
  have Z₁ : NK.LocalTame.Zl2ResidueChar p (𝔭.adicCompletion K₁)
      (SeparableClosure (𝔭.adicCompletion K₁)) :=
    NK.TameStructureDeep.Tame.zl2ResidueChar_of_localFieldInputs 𝔭 hp hcharp
      (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hcharp) D₁
  have Z₂ : NK.LocalTame.Zl2ResidueChar q (𝔮.adicCompletion K₂)
      (SeparableClosure (𝔮.adicCompletion K₂)) :=
    NK.TameStructureDeep.Tame.zl2ResidueChar_of_localFieldInputs 𝔮 hq hcharq
      (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hq hcharq) D₂
  have hpq : p = q :=
    NK.LocalTame.residueChar_eq_of_zl2 Z₁ Z₂ (Φ : Gal(SeparableClosure (𝔭.adicCompletion K₁) /
      𝔭.adicCompletion K₁) ≃* Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂))
  refine ⟨hpq, ?_⟩
  -- the `p`-rank invariants of the two topological abelianisations
  have R₁ := hasFrattiniRank_topologicalAbelianization_adicCompletion 𝔭 hp hcharp D₁
  have R₂ := hasFrattiniRank_topologicalAbelianization_adicCompletion 𝔮 hq hcharq D₂
  -- transport of the first along the homeomorphism `Φ`
  have R₁' : NK.LocalAnabelian.HasFrattiniRank p
      (NK.LocalInputs.localDegree K₁ 𝔭 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁))
      (Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂) ⧸
        (commutator Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)).topologicalClosure) :=
    hasFrattiniRank_topologicalAbelianization_congr Φ R₁
  -- the second, rewritten at the common prime `p = q`
  have R₂' : NK.LocalAnabelian.HasFrattiniRank p
      (NK.LocalInputs.localDegree K₂ 𝔮 + 1 +
        NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂))
      (Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂) ⧸
        (commutator Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)).topologicalClosure) :=
    hpq.symm ▸ R₂
  have hrank : NK.LocalInputs.localDegree K₁ 𝔭 + 1 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁)
      = NK.LocalInputs.localDegree K₂ 𝔮 + 1 +
        NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) :=
    NK.LocalAnabelian.eq_of_hasFrattiniRank hp R₁' R₂'
  -- the `δ`-indicators: `δ = 1` iff the topological abelianisation has `p`-torsion
  have hδ₁ : (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) = 1) ↔
      NK.PTorsionTop.HasPTorsionAbelianizationTop p
        (Gal(SeparableClosure (𝔭.adicCompletion K₁) / 𝔭.adicCompletion K₁)) :=
    NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta 𝔭 hp hcharp _ D₁
  have hδ₂ : (NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) = 1) ↔
      NK.PTorsionTop.HasPTorsionAbelianizationTop q
        (Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)) :=
    NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta 𝔮 hq hcharq _ D₂
  have htor : NK.PTorsionTop.HasPTorsionAbelianizationTop p
        (Gal(SeparableClosure (𝔭.adicCompletion K₁) / 𝔭.adicCompletion K₁)) ↔
      NK.PTorsionTop.HasPTorsionAbelianizationTop p
        (Gal(SeparableClosure (𝔮.adicCompletion K₂) / 𝔮.adicCompletion K₂)) :=
    NK.PTorsionTop.hasPTorsionAbelianizationTop_congr_iff Φ p
  have hδeq : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) =
      NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) := by
    have key : (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) = 1) ↔
        (NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) = 1) := by
      rw [hδ₁, hδ₂, ← hpq]
      exact htor
    have h₁ : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) ≤ 1 :=
      NK.LocalInputs.zetaIndicator_le_one p (𝔭.adicCompletion K₁)
    have h₂ : NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) ≤ 1 :=
      NK.LocalInputs.zetaIndicator_le_one q (𝔮.adicCompletion K₂)
    rcases (by omega : NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) = 0 ∨
      NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K₁) = 1) with h | h <;>
      rcases (by omega : NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) = 0 ∨
        NK.LocalInputs.zetaIndicator q (𝔮.adicCompletion K₂) = 1) with h' | h' <;>
      omega
  omega

end NK.NUV2.LC
