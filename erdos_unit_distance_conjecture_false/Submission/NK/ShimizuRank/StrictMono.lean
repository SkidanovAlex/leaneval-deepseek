import Submission.NK.ShimizuRank.Basic
import Submission.NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt

/-!
# Shimizu's Lemma 4f.2 from the monotonicity of the Leopoldt defect

Shimizu (arXiv:2009.10431, Lemma 4f.2; CoNF (10.3.7)) shows that `r_ℓ(M) < r_ℓ(N)` for a nontrivial
finite extension `N/M` of number fields with `N` having a complex prime, and his proof has exactly
two ingredients:

1. `r_ℂ(M) < r_ℂ(N)` — the number of complex places strictly increases.  This is **elementary**
   number-field theory, proved unconditionally in `NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`.
2. `δ_ℓ(M) ≤ δ_ℓ(N)` — the **monotonicity of the Leopoldt defect** (CoNF (10.3.7) Corollary and
   the proof of (10.3.11) Corollary).

Together with CoNF (10.3.20) `r_ℓ = r_ℂ + 1 + δ`, these give the Lemma.  Since `δ_ℓ` is not
formalised in this development, ingredient 2 is carried as the *difference estimate*
`r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)`, i.e. as `NK.ShimizuRank.LeopoldtDefectMono`, and the main
result of this file is

  `NK.ShimizuRank.rankStrictMonoLevelInputGen_of_leopoldt`:
  `LeopoldtDefectMono Ω ℓ → NK.Reconstruct.RankStrictMonoLevelInputGen Ω ℓ`.

The passage from the difference estimate to the strict inequality is pure `ℕ`-arithmetic, so
`RankStrictMonoLevelInputGen` is *equivalent* to `LeopoldtDefectMono` together with
`rℂ`-strict-monotonicity restricted to levels with a complex prime.  No hypothesis on `δ_ℓ`
vanishing (Leopoldt's conjecture) is used anywhere.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.ShimizuRank

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Lemma 4f.2 from the monotonicity of the Leopoldt defect.**

For finite number-field levels `M ⊆ N` of `Ω/ℚ` with `M ≠ N` and `N` possessing a complex prime,
`r_ℓ(M) < r_ℓ(N)`.

The proof is Shimizu's: `r_ℂ(M) < r_ℂ(N)` (`NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`) and
`LeopoldtDefectMono` combine to `r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)`, which together with
`r_ℂ(M) < r_ℂ(N)` forbids `r_ℓ(N) ≤ r_ℓ(M)`. -/
theorem rankStrictMonoLevelInputGen_of_leopoldt {ℓ : ℕ} [Fact ℓ.Prime]
    (h : LeopoldtDefectMono Ω ℓ) : RankStrictMonoLevelInputGen Ω ℓ := by
  intro M N _ _ hMN hne hv
  have hrc : rComplex ↥M.L < rComplex ↥N.L :=
    ComplexPlace.rComplex_lt_of_lt M N hMN hne hv
  have hmono := h M N hMN
  by_contra hcon
  push Not at hcon
  omega

end NK.ShimizuRank
