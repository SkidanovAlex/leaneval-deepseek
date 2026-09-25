import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.ShimizuRank.All
import Submission.NK.Reconstruct.All

/-!
# The refutation of `NK.ShimizuRank.GammaTFRankFinite` (and hence of `Residuals`)

**This is the main finding of this chapter.**  The rank input

  `NK.ShimizuRank.GammaTFRankFinite Ω ℓ` :
  `∀ K K', Module.rank (ℤ_ℓ) (Γ_K^{tf}) < ℵ₀`,

i.e. "the torsion-free quotient of the `ℓ`-adic abelianisation `Γ_K = lim_L ℓ-part(Gal(L/K)^{ab})` has
finite `ℤ_ℓ`-rank", is **false** — for `K = ℚ` and `ℓ = 2` (and, by the same argument, for every
prime `ℓ`) the rank is `ℵ₀`.

The mechanism is recorded in `ProductRank.lean`: the `ℤ_ℓ`-rank of an inverse limit of finite
`ℓ`-groups is *not* controlled by the ranks of the finite levels (each of which is `0`), because the
limit contains the diagonal coherent families.  Concretely, `Γ_ℚ` has the profinite group

  `∏_{p odd} ℤ/2^{v₂(p-1)}`  —  also written  `∏_n ℤ/2^n`

as a quotient (the `2`-parts of the abelianisations of the cyclotomic levels `ℚ(ζ_{q_0⋯q_N})`, whose
Galois groups are `∏_{i≤N}(ℤ/q_i)^× ≅ ∏_{i≤N} ℤ/(q_i - 1)` by CRT), and the torsion-free quotient of
that product has `ℤ_2`-rank `ℵ₀` (`NK.RankTheoryDeep.aleph0_le_rank_of_surjective_tower`).  Rank cannot
increase along a quotient, so `rank_{ℤ_2} Γ_ℚ^{tf} ≥ ℵ₀`.

**Consequences**, all formalised below:

* `NK.RankTheoryDeep.not_gammaTFRankFinite_of_surjection` — the refutation from the arithmetic
  surjection `Γ_ℚ ↠ ∏_n ℤ/2^n` (`NK.RankTheoryDeep.gamma_surjection_ellTower`);
* `NK.RankTheoryDeep.not_residuals_of_surjection` — hence `NK.ShimizuRank.Residuals Ω 2` is
  **unsatisfiable**, so the Shimizu-rank route as currently wired cannot be instantiated;
* `NK.RankTheoryDeep.not_rankFormulaInput_rat_of_surjection` — the sibling chapter's input
  `NK.Reconstruct.RankFormulaInput ℚ Ω 2 δ` is likewise **unsatisfiable** (its `finite` field fails
  for `K = ℚ`, `K' = Ω`; note this is the *opposite* direction from the refutation
  `NK.ShimizuRank.not_rankFormulaInput_self`, which kills it for small `K'`).

The *correct* object whose rank is Shimizu's `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` is the **Hausdorff**
(dual-faithful) quotient `NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ (the subgroup invisible to every
continuous character `Γ_K → ℤ_ℓ`)`, not the torsion-free quotient `GammaTF`: the two differ
precisely by the invisible non-torsion elements exhibited here.  Equivalently,
`r_ℓ(K) = rank_{ℤ_ℓ} Hom_cts(Γ_K, ℤ_ℓ) = rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ)`, the *idèle-class-group*
invariant, and the residual list of the Shimizu route must be restated with `HausQuot` in place of
`GammaTF` (see `README.md` and `Corrected.lean`).

The file below is *conditional* on the arithmetic surjection `Φ : Γ_ℚ ↠ ∏_n ℤ/2^n`;
`Unconditional.lean` discharges that hypothesis using
`NK.RankTheoryDeep.gamma_surjection_ellTower`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Cardinal

namespace NK.RankTheoryDeep

universe u

/-- **The rank of `Γ_ℚ^{tf}` is infinite**, from the arithmetic surjection `Γ_ℚ ↠ ∏_n ℤ/2^n`. -/
theorem aleph0_le_rank_gammaTF_rat
    (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) :
    ℵ₀ ≤ Module.rank (PadicInt 2) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2) :=
  aleph0_le_rank_of_surjective_tower (ℓ := 2) Φ hΦ

/-- **`NK.ShimizuRank.GammaTFRankFinite Ω 2` is false**, from the arithmetic surjection
`Γ_ℚ ↠ ∏_n ℤ/2^n`.

Note the universes: `Ω` is a field of the *same* universe as the number field `ℚ` (i.e. `Type`), so
that `ℚ` is a legitimate witness for the universally quantified `K` of `GammaTFRankFinite`.  The
mathematics is universe-independent (the construction of the levels takes place inside `Ω`), and the
statement at an arbitrary universe follows by taking `K` to be a lift of `ℚ`. -/
theorem not_gammaTFRankFinite_of_surjection
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) :
    ¬ NK.ShimizuRank.GammaTFRankFinite Ω 2 := by
  intro h
  have h1 := aleph0_le_rank_gammaTF_rat Ω Φ hΦ
  have h2 : Module.rank (PadicInt 2) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2)
      < Cardinal.aleph0 := h ℚ Ω
  exact absurd h2 (not_lt.mpr h1)

/-- **`NK.ShimizuRank.Residuals Ω 2` is unsatisfiable**, from the arithmetic surjection.

Since `Residuals` bundles the falsified `GammaTFRankFinite` (`rankFinite`), the whole residual
structure of `Submission/Work/ShimizuRank/` is refuted. -/
theorem not_residuals_of_surjection
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) :
    ¬ NK.ShimizuRank.Residuals Ω 2 := fun h =>
  not_gammaTFRankFinite_of_surjection Ω Φ hΦ h.rankFinite

/-- **`NK.Reconstruct.RankFormulaInput ℚ Ω 2 δ` is unsatisfiable** for every `δ`, from the
arithmetic surjection: its `finite` field would force a finite `ℤ_2`-rank.  (The sibling refutation
`NK.ShimizuRank.not_rankFormulaInput_self` kills the input for *small* `K'`; this one kills it for
the *large* `K' = Ω`.) -/
theorem not_rankFormulaInput_rat_of_surjection
    (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) (δ : ℕ) :
    ¬ NK.Reconstruct.RankFormulaInput (K := ℚ) (K' := Ω) 2 δ := by
  intro h
  have h1 := aleph0_le_rank_gammaTF_rat Ω Φ hΦ
  have : Module.Finite (PadicInt 2)
      (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2) := h.finite
  haveI := this
  have h2 : Module.rank (PadicInt 2) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2)
      < Cardinal.aleph0 :=
    Module.rank_lt_aleph0 (PadicInt 2)
      (M := NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2)
  exact absurd h2 (not_lt.mpr h1)

end NK.RankTheoryDeep
