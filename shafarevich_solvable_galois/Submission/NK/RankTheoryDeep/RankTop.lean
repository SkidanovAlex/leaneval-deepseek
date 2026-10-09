import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.rank_hausQuot_le_rank_dual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank statements **at the separable closure**

This file fixes the *level* at which the `Γ`-side rank statements of the Shimizu route are stated in
this chapter: `K' = Ω`, the separable closure.  The reason is recorded in `ArtinDualBridge`
(`IdeleRankDefs.lean`): at `K' = K` the group `Γ_{K/K}` is trivial, so a chain of equalities "for all
`K'`" between `Dual (Γ_K^{K'}) ℓ` and `Dual (C_K) ℓ` is false at that end.  All the statements the
Shimizu §4f endgame consumes (`hausRank ↥M.L Ω ℓ`, Lemma 4f.2, Proposition 4f.5) are of this form.

* `NK.RankTheoryDeep.DualRankBoundTop Ω ℓ` — `rank_{ℤ_ℓ} Hom_cts(Γ_K^{Ω}, ℤ_ℓ) ≤ [K : ℚ]`;
* `NK.RankTheoryDeep.HausQuotRankFiniteTop Ω ℓ` — the same for the Hausdorff quotient
  `Γ_K^{Ω} ⧸ invisible`, i.e. CoNF (10.3.20) at `K' = Ω`;
* `NK.RankTheoryDeep.hausQuotRank_le_rank_dual_top`,
  `NK.RankTheoryDeep.hausQuotRankFiniteTop_of_dualRankBoundTop` — the duality step between them.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField
open Cardinal

namespace NK.RankTheoryDeep

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The `Γ`-side rank bound at the separable closure**: `rank_{ℤ_ℓ} Hom_cts(Γ_K^{Ω}, ℤ_ℓ) ≤
[K : ℚ]` for every number field `K` with `Ω ⊇ K`. -/
def DualRankBoundTop (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω],
    Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
      ≤ (Module.finrank ℚ K : Cardinal)

/-- **The corrected finiteness statement at the separable closure**: the Hausdorff quotient of
`Γ_K^{Ω}` has finite `ℤ_ℓ`-rank for every number field `K ⊆ Ω`.  This is the form in which the
statement is proved and consumed; the version quantified over all `K'`
(`NK.RankTheoryDeep.HausQuotRankFinite Ω ℓ`, `Corrected.lean`) follows from it by descent for every
`K'` that is a level of `Ω/K`. -/
def HausQuotRankFiniteTop (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω],
    Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ) < ℵ₀

/-- **The duality step at the separable closure**: the rank of the Hausdorff quotient is bounded by
the rank of the dual (the evaluation `HausQuot ↪ Module.Dual (ℤ_ℓ) (Dual (Γ_K^{Ω} ℓ))` is injective
by the definition of `invisibleSubmodule`, `rank_hausQuot_le_rank_dual`). -/
theorem hausQuotRank_le_rank_dual_top {ℓ : ℕ} [Fact ℓ.Prime] (h : DualRankBoundTop Ω ℓ)
    (K : Type u) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω] :
    Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ)
      ≤ (Module.finrank ℚ K : Cardinal) := by
  have hle := h K
  have hfin : Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω ℓ) ℓ)
      < ℵ₀ := lt_of_le_of_lt hle (by exact_mod_cast Cardinal.natCast_lt_aleph0)
  exact le_trans (rank_hausQuot_le_rank_dual (ℓ := ℓ) hfin) hle

/-- **The finiteness at the separable closure, from the dual bound.** -/
theorem hausQuotRankFiniteTop_of_dualRankBoundTop {ℓ : ℕ} [Fact ℓ.Prime]
    (h : DualRankBoundTop Ω ℓ) : HausQuotRankFiniteTop Ω ℓ :=
  fun K _ _ _ _ =>
    lt_of_le_of_lt (hausQuotRank_le_rank_dual_top h K)
      (by exact_mod_cast Cardinal.natCast_lt_aleph0)

end NK.RankTheoryDeep
