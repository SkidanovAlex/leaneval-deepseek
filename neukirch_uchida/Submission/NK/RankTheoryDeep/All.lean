import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.RankTheoryDeep.gamma_surjection_ellTower
import Submission.NK.RankTheoryDeep.gamma_surjection_ellTower_prime
import Submission.NK.RankTheoryDeep.exists_nontrivial_dual_rat
import Submission.NK.RankTheoryDeep.Refutation
import Submission.NK.RankTheoryDeep.Corrected
import Submission.NK.RankTheoryDeep.Unconditional
import Submission.NK.RankTheoryDeep.ResidualsDerived
import Submission.NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne
import Submission.NK.RankTheoryDeep.exists_finset_support_of_dual_pi_of_cofinite
import Submission.NK.RankTheoryDeep.rank_hausQuot_le_rank_dual
import Submission.NK.RankTheoryDeep.IdeleRank
import Submission.NK.RankTheoryDeep.CorrectedRank
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.RankTop
import Submission.NK.RankTheoryDeep.LocalDegree
import Submission.NK.RankTheoryDeep.PlacesOverEll
import Submission.NK.RankTheoryDeep.IdeleAssembly
import Submission.NK.RankTheoryDeep.IdeleFinal
import Submission.NK.RankTheoryDeep.InvisibleRefuted
import Submission.NK.RankTheoryDeep.CorrectedPackage
import Submission.NK.RankTheoryDeep.CorrectedResidualsDerived
import Submission.NK.RankTheoryDeep.CorrectedFourf5
import Submission.NK.RankTheoryDeep.tauStar_gamma_eq_one
import Submission.NK.RankTheoryDeep.dual_pi_surjective_finite_coordinates
import Submission.NK.RankTheoryDeep.dual_localUnits_infinite_eq_zero
import Submission.NK.RankTheoryDeep.rank_pi_le_sum
import Submission.NK.RankTheoryDeep.rank_dual_integralIdeles_le_pi
import Submission.NK.RankTheoryDeep.rank_dual_ideleClassGroup_le_integralIdeles

/-!
# `Submission/Work/RankTheoryDeep/` — umbrella

**Import this module to get the whole chapter:**

```lean
import Submission.NK.RankTheoryDeep.All
```

`NK.RankTheoryDeep` is the chapter of the Neukirch–Uchida development that owns the
**Iwasawa-theoretic rank theory of the Shimizu route** — the subproject that was supposed to supply
the residual structure `NK.ShimizuRank.Residuals Ω ℓ` (`Submission/Work/ShimizuRank/`), whose
`rankFinite` field is the finiteness of the `ℤ_ℓ`-rank of `Γ_K^{tf}`.

## The finding

**That residual is false, and this is proved here, `sorry`-free.**

`ProductRank.lean` proves that the inverse limit of finite `ℓ`-groups may have *infinite*
torsion-free `ℤ_ℓ`-rank: the `ℓ`-adic tower product `∏_n ℤ/ℓ^n` is such a limit (each finite
truncation has rank `0`), and its torsion-free quotient has rank `ℵ₀`; hence so does the
torsion-free quotient of *any* `ℤ_ℓ`-module admitting a surjective `ℤ_ℓ`-linear map onto it.
`gamma_surjection_ellTower.lean` supplies exactly such a map for `Γ_ℚ` — `Γ_ℚ ↠ ∏_n ℤ/2^n`, built
from the cyclotomic levels `ℚ(ζ_{q_0⋯q_N})` (CRT, cyclicity of `(ℤ/q)^×`, Fermat numbers) — and
`Unconditional.lean` assembles:

```lean
NK.RankTheoryDeep.not_gammaTFRankFinite   : ¬ NK.ShimizuRank.GammaTFRankFinite Ω 2   -- K = ℚ
NK.RankTheoryDeep.not_residuals           : ¬ NK.ShimizuRank.Residuals Ω 2
NK.RankTheoryDeep.not_rankFormulaInput_rat (δ) : ¬ NK.Reconstruct.RankFormulaInput ℚ Ω 2 δ
NK.RankTheoryDeep.rankGamma_rat_eq_zero_unconditional : rankGamma ℚ Ω 2 = 0
NK.RankTheoryDeep.not_hausRankInput      : ¬ NK.Reconstruct.HausRankInput Ω 2
```

and, for **every prime `ℓ`** (`gamma_surjection_ellTower_prime.lean`, proved):

```lean
NK.RankTheoryDeep.not_gammaTFRankFinite_prime (ℓ) : ¬ NK.ShimizuRank.GammaTFRankFinite Ω ℓ
NK.RankTheoryDeep.not_residuals_prime (ℓ)         : ¬ NK.ShimizuRank.Residuals Ω ℓ
NK.RankTheoryDeep.rankGamma_rat_eq_zero_prime (ℓ) : rankGamma ℚ Ω ℓ = 0
```

and, in the *derived* vocabulary in which the endgame consumes the residual
(`ResidualsDerived.lean`):

```lean
NK.RankTheoryDeep.not_residualsDerived (ℓ) : ¬ NK.Mine.ResidualsDerived K K' ℓ
NK.RankTheoryDeep.not_classicalChapters   : ¬ NK.Mine.ClassicalChapters K₁ K₂ K₁' K₂'
```

the second being the refutation of the *whole* classical-input wall
(`Submission/Work/Mine/ClassicalChapters.lean`), whose field `residuals` demands the (false) rank
structure at every prime.

**Consequently the rank residual of the live Shimizu route cannot be instantiated**: every theorem
of `Submission/Work/ShimizuRank/Package.lean` that consumes `Residuals` is vacuous.

`Corrected.lean` identifies the correct object — the **Hausdorff** (dual-faithful) quotient
`NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ invisible`, i.e. `Γ_K ⧸ (⋂_{χ : Γ_K → ℤ_ℓ} ker χ)`,
whose `ℤ_ℓ`-rank *is* Shimizu's `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) = rank Hom_cts(C_K, ℤ_ℓ)` — defines
the corrected residual `NK.RankTheoryDeep.HausQuotRankFinite Ω ℓ`, and shows the workspace's own
`NK.Reconstruct.HausRankInput Ω 2` to be false.

## Files

| module | content |
|---|---|
| `ProductRank.lean` | the engine: `∏_n ℤ/ℓ^n` has torsion-free rank `ℵ₀`; any `M` with a surjective `ℤ_ℓ`-linear map onto it has torsion-free rank `≥ ℵ₀` |
| `gamma_surjection_ellTower.lean` (+ the auxiliary modules `TowerArc`, `expHom_surjective`, `jointHom_surjective`, `levelCoordHom_ellRestrict`, `exists_linearMap_of_groupHom`, …) | the arithmetic crux: `Γ_ℚ ↠ ∏_n ℤ/2^n` as `ℤ_2`-modules |
| `gamma_surjection_ellTower_prime.lean` (+ the `PrimeTower/` subdirectory) | the general-`ℓ` form of the arithmetic crux: `Γ_ℚ ↠ ∏_n ℤ/ℓ^n` for every prime `ℓ` |
| `exists_nontrivial_dual_rat.lean` | the cyclotomic character: a non-zero continuous `Γ_ℚ → ℤ_2` (used for the refutation of `HausRankInput`) |
| `Refutation.lean` | the refutation, given the arithmetic surjection |
| `Corrected.lean` | the corrected object and residual, `rankGamma ℚ Ω 2 = 0`, and the refutation of `HausRankInput` |
| `Unconditional.lean` | the unconditional forms of the refutation |
| `IdeleRank.lean` | the corrected residual in the **idèle-side** form: `DualRankBound Ω ℓ` (`rank Hom_cts(Γ_K, ℤ_ℓ) = r_ℓ(K) ≤ [K : ℚ]`, CoNF (10.3.20)) and the proof that `DualRankBound → HausQuotRankFinite` |
| `CorrectedRank.lean` | the corrected residual fields in the vocabulary of `rank HausQuot`: `hausRank`, `LeopoldtDefectMonoHaus`, `HausRankStrictMono`, `ResRankInputHaus`, and **Shimizu's Lemma 4f.2 corrected** (`hausRankStrictMono_of_leopoldt`) |
| `rank_hausQuot_le_rank_dual.lean` | the duality step: `rank (HausQuot) ≤ rank (Dual Γ_K)` (the evaluation `HausQuot ↪ Dual^*` is injective by definition of `invisibleSubmodule`) |
| `dual_localUnits_eq_zero_of_residueChar_ne.lean` | **every continuous character of `𝒪_vˣ` is trivial when the residue characteristic is `≠ ℓ`** — the arithmetic core of the idèle-side computation, on the on-disk `card_dvd_of_isPGroup_quotient_adicUnits` |
| `ResidualsDerived.lean` | the consumer-facing corollaries: `ResidualsDerived K K' ℓ` and `ClassicalChapters K₁ K₂ K₁' K₂'` are unsatisfiable |
| `exists_finset_support_of_dual_pi_of_cofinite.lean` | a character of a product of compact groups factors through a finite subproduct, when all but finitely many factors have trivial dual (the unconditional form is *false* — see the counterexample recorded in `README.md` §4) |
| `IdeleRankDefs.lean` | the vocabulary of the idèle-side computation: `dualRank`, `LocalUnitDualRankInput` (the local unit structure at `v | ℓ`), `IdeleDualRankBound`, `ArtinDualBridge` (ℓ-adic Artin reciprocity) |
| `LocalDegree.lean` | `primesOver_span_iff_mem`, `exists_prime_charP_quotient_of_notMem`, **`sum_localDeg_eq_finrank`** (`∑_{q | ℓ} e_q f_q = [K : ℚ]`) |
| `PlacesOverEll.lean` | `primeOfOver`, `placesOverEll` (the finite set of places above `ℓ`), and the vanishing of `Dual (𝒪_vˣ)` away from it |
| `IdeleAssembly.lean` | **`rank_dual_integralIdeles_le`**: given `LocalUnitDualRankInput ℓ`, the rank of `Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)` is at most `[K : ℚ]` — the assembly of the finite-support decomposition, the vanishing away from `ℓ`, and the sum of local degrees |
| `IdeleFinal.lean` | **the interface**: `ideleDualRankBound_of_localUnits`, `dualRankBound_of_idele`, **`hausRank_le_finrank`**, **`hausQuotRankFinite_of_localUnits_and_artin`**, the corrected residual `CorrectedResidualsIdele`, and `correctedResidualsHaus_of_idele` |
| `dual_pi_surjective_finite_coordinates.lean` | a character of a finite product of groups is a finite sum of its coordinates, when all but finitely many factors have trivial dual |
| `dual_localUnits_infinite_eq_zero.lean` | every continuous character of an archimedean local unit group is trivial |
| `rank_pi_le_sum.lean` | the rank of a finite product of modules is at most the sum of the ranks (over a domain) |
| `rank_dual_integralIdeles_le_pi.lean` | the integral idèles are the full product of the local unit groups |
| `rank_dual_ideleClassGroup_le_integralIdeles.lean` | `C_K` has no more characters than `∏_v 𝒪_vˣ` (the exact sequence + finiteness of `Cl(K)`) |
| `InvisibleRefuted.lean` | **`not_invisibleSubgroupTorsion_of_localUnits_and_artin`**: the residual field `InvisibleSubgroupTorsion` is *false* (the invisible subgroup is not torsion), by the same `∏_n ℤ/ℓ^n` phenomenon |
| `CorrectedPackage.lean` | **`CorrectedResidualsDeep Ω ℓ`** — the corrected residual reduced to its four named classical inputs, with `hausQuotRankFinite`, `leopoldtDefectMonoHaus`, `hausRankStrictMono`, `resRankInputHaus` and `CorrectedResidualsHaus` all *proved* from it |
| `CorrectedResidualsDerived.lean` | `CorrectedResidualsDerived K K' ℓ` — the corrected residual in the **derived `ℚ`-algebra vocabulary** of `NK.Mine.ResidualsDerived`, with the transported forms `HausQuotRankFiniteDerived`, `HausRankStrictMonoDerived`, `ResRankInputHausDerived` and their proofs from it |
| `CorrectedFourf5.lean` | **the corrected endgame**: `fourf5Gen_of_correctedRankInputs`, `fourf5Input_of_correctedRankInputs`, `fourf5Gen_of_correctedResidualsDeep`, `fourf5Input_of_correctedResidualsDeep` (Shimizu's Proposition 4f.5 in the `FrobLevel` form) and `exists_isomorphism_of_prop4f3_data_of_correctedResiduals` (Shimizu's Theorem 4.0), all from the satisfiable hypothesis `CorrectedResidualsDeep` |
| `tauStar_gamma_eq_one.lean` | **step 4 of the duality argument (§9), first piece**: the conjugation action `NK.Reconstruct.tauStar` of `Gal(Ω/K)` on `Γ_K` is *trivial* |
| `README.md` | the full account, including the audit table (instantiations at `K = ℚ`, imaginary quadratic, `ℓ = 2, 3`) and the repair |

Everything in the import closure of this module is `sorry`-free and axiom-clean
(`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; see `Axioms.lean`).
-/
