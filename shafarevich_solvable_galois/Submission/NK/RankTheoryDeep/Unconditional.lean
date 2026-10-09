import Submission.NK.RankTheoryDeep.gamma_surjection_ellTower
import Submission.NK.RankTheoryDeep.gamma_surjection_ellTower_prime
import Submission.NK.RankTheoryDeep.exists_nontrivial_dual_rat
import Submission.NK.RankTheoryDeep.Refutation
import Submission.NK.RankTheoryDeep.Corrected
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The refutation, unconditionally

`gamma_surjection_ellTower.lean` supplies the arithmetic input — a surjective `ℤ_2`-linear map
`Γ_ℚ ↠ ∏_n ℤ/2^n` built from the cyclotomic levels `ℚ(ζ_{q_0⋯q_N})` — so the statements of
`Refutation.lean` become unconditional:

* `NK.RankTheoryDeep.not_gammaTFRankFinite` — `NK.ShimizuRank.GammaTFRankFinite Ω 2` is **false**
  (witness `K = ℚ`: `rank_{ℤ_2} (Γ_ℚ ⧸ torsion) = ℵ₀`);
* `NK.RankTheoryDeep.not_residuals` — hence `NK.ShimizuRank.Residuals Ω 2` is
  **unsatisfiable**;
* `NK.RankTheoryDeep.not_rankFormulaInput_rat` — `NK.Reconstruct.RankFormulaInput ℚ Ω 2 δ` is
  **unsatisfiable** for every `δ`;
* `NK.RankTheoryDeep.not_hausRankInput` — `NK.Reconstruct.HausRankInput Ω 2` is **false** as
  well: the Hausdorff quotient `Γ_ℚ ⧸ invisible` has positive rank, while the input forces it to be
  `↑(rankGamma ℚ Ω 2) = ↑0 = 0`;
* `NK.RankTheoryDeep.not_gammaTFRankFinite_prime`, `not_residuals_prime` — the same refutation for
  **every** prime `ℓ`, from the general surjection
  `NK.RankTheoryDeep.gamma_surjection_ellTower_prime`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Cardinal

namespace NK.RankTheoryDeep

universe u

/-- **`NK.ShimizuRank.GammaTFRankFinite Ω 2` is false** (`K = ℚ`). -/
theorem not_gammaTFRankFinite (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : ¬ NK.ShimizuRank.GammaTFRankFinite Ω 2 := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact not_gammaTFRankFinite_of_surjection Ω Φ hΦ

/-- **`NK.ShimizuRank.Residuals Ω 2` is unsatisfiable.** -/
theorem not_residuals (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : ¬ NK.ShimizuRank.Residuals Ω 2 := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact not_residuals_of_surjection Ω Φ hΦ

/-- **`NK.Reconstruct.RankFormulaInput ℚ Ω 2 δ` is unsatisfiable** for every `δ`. -/
theorem not_rankFormulaInput_rat (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (δ : ℕ) :
    ¬ NK.Reconstruct.RankFormulaInput (K := ℚ) (K' := Ω) 2 δ := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact not_rankFormulaInput_rat_of_surjection Ω Φ hΦ δ

/-- **`rankGamma ℚ Ω 2 = 0`** — the honest rank of `Γ_ℚ^{tf}` is infinite, and `rankGamma` is
`Module.finrank = Cardinal.toNat ∘ Module.rank`. -/
theorem rankGamma_rat_eq_zero_unconditional (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : NK.Reconstruct.rankGamma ℚ Ω 2 = 0 := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact rankGamma_rat_eq_zero Ω Φ hΦ

/-- **`NK.Reconstruct.HausRankInput Ω 2` is false** — unconditionally, combining the cyclotomic
character `NK.RankTheoryDeep.exists_nontrivial_dual_rat` with the degeneracy
`rankGamma ℚ Ω 2 = 0`.

`HausRankInput Ω 2` asserts `rank (HausQuot ℚ Ω 2) = ↑(rankGamma ℚ Ω 2)`; the right-hand side is
`↑0 = 0`, while the non-zero continuous character gives `0 < rank (HausQuot ℚ Ω 2)`
(`NK.RankTheoryDeep.rank_hausQuot_pos_of_dual_ne_zero`). -/
theorem not_hausRankInput (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] : ¬ NK.Reconstruct.HausRankInput Ω 2 := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact not_hausRankInput_of_dual Ω (exists_nontrivial_dual_rat Ω) Φ hΦ

/-- **The `ℤ_2`-rank of `Γ_ℚ^{tf}` is infinite.** -/
theorem aleph0_le_rank_gammaTF_rat_unconditional (Ω : Type u) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ℵ₀ ≤ Module.rank (PadicInt 2) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2) := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower Ω
  exact aleph0_le_rank_gammaTF_rat Ω Φ hΦ

/-- **`NK.ShimizuRank.GammaTFRankFinite Ω ℓ` is false for every prime `ℓ`** (`K = ℚ`). -/
theorem not_gammaTFRankFinite_prime (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] : ¬ NK.ShimizuRank.GammaTFRankFinite Ω ℓ := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower_prime ℓ Ω
  have h1 : ℵ₀ ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) ℓ) :=
    aleph0_le_rank_of_surjective_tower Φ hΦ
  intro h
  have h2 : Module.rank (PadicInt ℓ) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) ℓ)
      < Cardinal.aleph0 := h ℚ Ω
  exact absurd h2 (not_lt.mpr h1)

/-- **`NK.ShimizuRank.Residuals Ω ℓ` is unsatisfiable for every prime `ℓ`.** -/
theorem not_residuals_prime (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] : ¬ NK.ShimizuRank.Residuals Ω ℓ := fun h =>
  not_gammaTFRankFinite_prime ℓ Ω h.rankFinite

/-- **`rankGamma ℚ Ω ℓ = 0` for every prime `ℓ`.** -/
theorem rankGamma_rat_eq_zero_prime (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] : NK.Reconstruct.rankGamma ℚ Ω ℓ = 0 := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower_prime ℓ Ω
  have h1 : ℵ₀ ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) ℓ) :=
    aleph0_le_rank_of_surjective_tower Φ hΦ
  rw [NK.Reconstruct.rankGamma, Module.finrank]
  exact Cardinal.toNat_eq_zero.mpr (Or.inr h1)

end NK.RankTheoryDeep
