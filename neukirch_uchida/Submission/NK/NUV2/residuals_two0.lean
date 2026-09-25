import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.NUV2.localUnits_two
import Submission.NK.NUV2.hausQuot_finrank_eq_dual_idele_of_artin
import Submission.NK.NUV2.ideleLeopoldt_two
import Submission.NK.NUV2.levelInfinity_sup_eq
import Submission.NK.NUV2.artinDualBridge_two

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FinitDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
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
## This lemma: `CorrectedResidualsDerived K₁ K₁' 2` (four fields; dispatch each separately)
- `localUnits` (LocalUnitDualRankInput): 𝒪_v^× has ℤ_ℓ-rank e·f — true, local.
- `artin` (ArtinDualBridge: dualRank Γ_K = dualRank of the idèle class group, continuous ℤ_ℓ-characters): from global
  reciprocity (hFC) + connectedness of the archimedean part.
- `leopoldt` (HausLeopoldtData): monotonicity of the Leopoldt defect holds for non-Galois inclusions by flatness of ℤ_ℓ.
- `resKernel` (ShimizuRank.ResKernelRankInput): believed true, UNVERIFIED — audit satisfiability first (instantiate at
  K = ℚ); needs transfer / inflation–restriction for Hom(Γ_L, ℚ_ℓ). README §6.2 of ShimizuRank records a negative on
  deriving it from the library. Highest risk item.

UNIVERSES: everything is in `Type 0`, matching the hypotheses. Missing mathematics is NOT a reason to stop: build it (delegate). Use declare_false only for a statement that is actually false, with a counterexample.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.NUV2

/-! ## The four fields of the corrected residual, at `ℓ = 2`, `Type 0`

Each of the four fields of `CorrectedResidualsDerived K₁ K₁' 2` is proved in its own module of this
directory, and assembled below:

* `localUnits` — `NUV2/localUnits_two` (`NK.RankTheoryDeep.LocalUnitDualRankInput 2`);
* `artin` — `NUV2/artinDualBridge_two` (`NK.RankTheoryDeep.ArtinDualBridge Ω 2`, from `hFC`);
* `leopoldt` — `NUV2/ideleLeopoldt_two` (the idèle-side rank formula of CoNF (10.3.7)/(10.3.20))
  composed with the bridge `NUV2/hausQuot_finrank_eq_dual_idele_of_artin` (below);
* `resKernel` — `NUV2/levelInfinity_sup_eq` (Shimizu's Prop. 4f.5 in field form) through
  `NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq` (below). -/

/-! ## The fallback route to the Leopoldt field

The `leopoldt` field of the corrected residual is the rank formula
`r_2(K) = r_ℂ(K) + 1 + δ_2(K)` with a monotone defect.  Rather than manufacture it in one
piece, it is the composite of

* `NUV2/ideleLeopoldt_two` — the idèle-side formula `finrank Hom_cts(C_K, ℤ_2) = r_ℂ(K) + 1 + δ K`
  with `δ` monotone (CoNF (10.3.7)/(10.3.20) on the idèle class group), and
* `NUV2/hausQuot_finrank_eq_dual_idele_of_artin` — the bridge
  `finrank (HausQuot K Ω 2) = finrank Hom_cts(C_K, ℤ_2)`, from ℓ-adic Artin reciprocity.

The short assembly is proved here. -/

/-- **The idèle-side rank formula with a monotone defect** (the conclusion of
`NUV2/ideleLeopoldt_two`, re-stated as an explicit hypothesis so that the assembly below can be
proved independently of it). -/
private def IdeleLeopoldt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : Prop :=
  ∃ δ : IntermediateField ℚ Ω → ℕ,
    (∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N → δ M ≤ δ N) ∧
      ∀ (K : IntermediateField ℚ Ω) [NumberField ↥K],
        Module.finrank (PadicInt 2)
            (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥K) 2)
          = NK.Reconstruct.rComplex ↥K + 1 + δ K

/-- **The bridge** (the conclusion of `NUV2/hausQuot_finrank_eq_dual_idele_two`). -/
private def HausQuotBridge (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω],
    Module.finrank (PadicInt 2) (NK.Reconstruct.HausQuot K Ω 2)
      = Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) 2)

/-- **The bridge, from the `Γ`-`C_K` Artin bridge.**  This is
`NUV2/hausQuot_finrank_eq_dual_idele_of_artin` in the `HausQuotBridge` form used by
`hausLeopoldtData_of_idele`. -/
private theorem hausQuotBridge_of_artin (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (hb : NK.RankTheoryDeep.ArtinDualBridge Ω 2) : HausQuotBridge Ω :=
  fun K _ _ _ _ => NK.NUV2.hausQuot_finrank_eq_dual_idele_of_artin Ω hb K

/-- **The Leopoldt field from the two idèle-side pieces.**  The defect function of
`HausLeopoldtData` is the one of the idèle-side formula, restricted to the finite levels of `Ω`
along `NumFieldIn.L`; monotonicity is inherited, and the rank formula is the bridge followed by
the idèle-side formula. -/
private theorem hausLeopoldtData_of_idele (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (hI : IdeleLeopoldt Ω) (hB : HausQuotBridge Ω) :
    NK.RankTheoryDeep.HausLeopoldtData Ω 2 := by
  obtain ⟨δ, hmono, hform⟩ := hI
  refine ⟨fun K => δ K.L, ?_, ?_⟩
  · intro M N hMN
    haveI := M.numberField
    haveI := N.numberField
    exact hmono M.L N.L hMN
  · intro K
    haveI := K.numberField
    show Module.finrank (PadicInt 2) (NK.Reconstruct.HausQuot ↥K.L Ω 2)
      = NK.Reconstruct.rComplex ↥K.L + 1 + δ K.L
    rw [hB ↥K.L, hform K.L]

/-- **The `leopoldt` field, from the idèle-side rank formula and ℓ-adic Artin reciprocity.**

This is the composite `hausLeopoldtData_of_idele` of

* `NUV2/ideleLeopoldt_two` — the idèle-side formula `finrank Hom_cts(C_K, ℤ_2) = r_ℂ(K) + 1 + δ K`
  with monotone `δ` (CoNF (10.3.7)/(10.3.20) on the idèle class group, proved in this workspace), and
* the bridge `finrank (HausQuot K Ω 2) = finrank Hom_cts(C_K, ℤ_2)`
  (`NUV2/hausQuot_finrank_eq_dual_idele_of_artin`, from `ArtinDualBridge Ω 2`). -/
private theorem hausLeopoldtData_two_of_artin (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (hb : NK.RankTheoryDeep.ArtinDualBridge Ω 2) :
    NK.RankTheoryDeep.HausLeopoldtData Ω 2 :=
  hausLeopoldtData_of_idele Ω (NK.NUV2.ideleLeopoldt_two Ω)
    (hausQuotBridge_of_artin Ω hb)

/-! ## The fallback route to the `resKernel` field

`NK.ShimizuRank.ResKernelRankInput Ω 2` is Shimizu's rank step of Proposition 4f.5.  By the sharp
criterion `NK.Reconstruct.hausPi_hausMk_galToGamma_eq_zero_iff` (an element of `HausQuot L` is
killed by `hausPi K L h ℓ` exactly when its representatives fix `K^{(∞,ℓ)}` pointwise) it is
*equivalent* to the field statement

  `K₁^{(∞,2)} ⊔ L.L = M^{(∞,2)} ⊔ L.L`  in Shimizu's situation,

where `M = K₁ ⊓ K₂` and `K₁^{(∞,2)} ⊔ L.L = L.L ⊔ K₂^{(∞,2)}`.  That field statement is
`NUV2/levelInfinity_sup_eq`; the reduction from it to `ResKernelRankInput` is the short argument
below, which uses the on-disk `NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`. -/

/-- **The `resKernel` field from the field statement.**  The two kernels of
`hausPi K₁ L h₁ 2` and `hausPi M L hM 2` agree by
`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq` applied to the field statement, and equal
kernels give syntactically equal quotients, hence equal ranks. -/
private theorem resKernel_two_of_levelInfinity (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω]
    (hFS : ∀ (K₁ K₂ M : NK.Reconstruct.NumFieldIn ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
      [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω]
      [IsSepClosure ↥L.L Ω],
      M.L = K₁.L ⊓ K₂.L → K₁.L ≤ L.L → K₂.L ≤ L.L → M.L ≤ L.L →
      (NK.Reconstruct.levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
        = L.L ⊔ NK.Reconstruct.levelInfinityOf K₂ 2 →
      (NK.Reconstruct.levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
        = NK.Reconstruct.levelInfinityOf M 2 ⊔ L.L) :
    NK.ShimizuRank.ResKernelRankInput Ω 2 := by
  intro K₁ K₂ M L _ _ _ _ hMsup h₁ h₂ hM hsup
  have hfield : (NK.Reconstruct.levelInfinityOf K₁ 2 ⊔ L.L : IntermediateField ℚ Ω)
      = NK.Reconstruct.levelInfinityOf M 2 ⊔ L.L :=
    hFS K₁ K₂ M L hMsup h₁ h₂ hM hsup
  have hker : LinearMap.ker (NK.Reconstruct.hausPi K₁ L h₁ 2)
      = LinearMap.ker (NK.Reconstruct.hausPi M L hM 2) :=
    NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq K₁ M L h₁ hM 2
      (by rw [hfield]; exact sup_comm _ _)
  rw [hker]

/-- **The Shimizu rank residuals, at `ℓ = 2`, in `Type 0`.**

This is the `residuals` input of the wall `NK.NUV2.ResAll`: for every number field `K₁` and every
separable closure `K₁'` of it, the corrected residual `CorrectedResidualsDerived K₁ K₁' 2` of the
Shimizu rank chapter (CoNF (10.3.7)/(10.3.20) plus Shimizu's Prop. 4f.5 rank step), in the derived
`ℚ`-algebra vocabulary of `NK.ReconstructEndgame`.

The four fields are supplied by the sibling modules of this directory, each proved separately
(`localUnits_two`, `artinDualBridge_two`, `ideleLeopoldt_two` + the Artin bridge,
`levelInfinity_sup_eq` through the kernel argument). -/
theorem residuals_two0 (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (hKC : NK.NUV2.KCAll) : NK.NUV2.ResAll0 := by
  intro K₁ K₁' _ _ _ _ _
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  letI : IsSepClosure ℚ K₁' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K₁ K₁'
  letI : IsGalois ℚ K₁' := NK.ReconstructEndgame.isGalois_rat_of_numberField K₁ K₁'
  exact ⟨NK.NUV2.localUnits_two, NK.NUV2.artinDualBridge_two hFC K₁',
    hausLeopoldtData_two_of_artin K₁' (NK.NUV2.artinDualBridge_two hFC K₁'),
    resKernel_two_of_levelInfinity K₁' (NK.NUV2.levelInfinity_sup_eq K₁')⟩

end NK.NUV2
