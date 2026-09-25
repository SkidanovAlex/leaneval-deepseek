import Submission.NK.RankTheoryDeep.Corrected
import Submission.NK.RankTheoryDeep.rank_hausQuot_le_rank_dual
import Submission.NK.Reconstruct.GammaDual

/-!
# The corrected rank theory: the **dual** rank bound, and `HausQuotRankFinite` from it

`Refutation.lean` shows that the rank of `Γ_ℚ ⧸ torsion` is `ℵ₀` while Shimizu's invariant
`r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` is finite; `Corrected.lean` identifies the correct object as the
Hausdorff quotient `HausQuot K K' ℓ = Γ_K ⧸ invisible`.  This file states the corrected input in the
form in which the *idèle-class-group* computation produces it, and reduces `HausQuotRankFinite` to
it.

## The two models of `r_ℓ(K)`, and the duality step

Shimizu's `r_ℓ(K)` is the `ℤ_ℓ`-rank of the **continuous dual**:

```
r_ℓ(K) = rank_{ℤ_ℓ} Hom_cts(Γ_K, ℤ_ℓ) = rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ)
```

(the second equality is ℓ-adic Artin reciprocity; the right-hand side is computed from the idèle
class group, CoNF Ch. X §10.3).  The two inequalities relating this dual to `HausQuot` are

* `rank (Dual (Γ_K) ℓ) ≤ rank (HausQuot K K' ℓ)` — from
  `Dual ⊆ Hom(HausQuot ⊗ ℚ_ℓ, ℚ_ℓ)`;
* `rank (HausQuot K K' ℓ) ≤ rank (Dual (Γ_K) ℓ)` — from the evaluation
  `HausQuot ↪ Module.Dual (ℤ_ℓ) (Dual (Γ_K) ℓ)`, which is injective because
  `invisibleSubmodule` is *defined* as the kernel of evaluation
  (`NK.RankTheoryDeep.rank_hausQuot_le_rank_dual`).

So the finite-rank statement for `HausQuot` is *equivalent* to the finite-rank statement for the
character module — which is exactly the classical CoNF (10.3.20), and exactly what the idèle class
group computes.

## The idèle-side bound, and how it is reduced here

The bound `rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ) ≤ [K : ℚ]` is proved from

* the exact sequence `𝒪_Kˣ → ∏_v 𝒪_vˣ → C_K → Cl(K) → 0`
  (`NK.GlobalCFT.IdeleClassGroup.local_global_exact_sequence`, on disk), together with
  `Cl(K)` finite (finiteness of the class group);
* `NK.RankTheoryDeep.exists_finset_support_of_dual_pi_of_cofinite` — a character of a product of
  compact groups factors through a *finite* subproduct **provided all but finitely many factors have
  trivial dual**, so `Dual (∏_v 𝒪_vˣ) ℓ = ⊕_v Dual (𝒪_vˣ) ℓ` (this is where the `ℓ`-adically
  *infinite* number of places is tamed).  The cofinite hypothesis is necessary: the *unconditional*
  statement is **false**, since `χ(x) = ∑_n ℓ^n x_n` is a continuous character of `∏_n ℤ_ℓ` which is
  not a finite sum of coordinate characters;
* `NK.RankTheoryDeep.dual_localUnits_eq_zero_of_residueChar_ne` — `Dual (𝒪_vˣ) ℓ = 0` whenever the
  residue characteristic is `≠ ℓ` (this is the arithmetic core, resting on the on-disk
  `NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits`), so only the finitely many `v | ℓ`
  contribute;
* the local structure at `v | ℓ`: `𝒪_vˣ ≅ μ_{q-1} × (1+𝔪)` with `1+𝔪 ≅ ℤ_ℓ^{[K_v : ℚ_ℓ]}`
  (equivalently `NK.LocalCFT.UnitsStructure`), giving `Dual (𝒪_vˣ) ℓ ≅ ℤ_ℓ^{[K_v : ℚ_ℓ]}` and
  hence total rank `∑_{v | ℓ} [K_v : ℚ_ℓ] = [K : ℚ]`.

The first three items are on disk or proved here; the fourth is the local unit structure (a named
classical input in this workspace, `NK.LocalCFT.UnitsStructure` /
`NK.LocalInputs.LocalFieldInputs`).  The corresponding statements for `Cl(K)` and `𝒪_Kˣ` are the
finiteness of the class group and Dirichlet's unit theorem
(`NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Cardinal

namespace NK.RankTheoryDeep

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The idèle-side rank bound** (CoNF (10.3.20), the half that does not need class field theory):
the `ℤ_ℓ`-rank of the continuous character module of `Γ_K` — equivalently, by ℓ-adic Artin
reciprocity, of the idèle class group `C_K` — is at most the degree `[K : ℚ]`.

This is the invariant Shimizu calls `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)`, and the statement is the
*correct* form of the finiteness input: the rank is finite, bounded by `[K : ℚ]`, and it is the rank
of the *dual* — not of `Γ_K ⧸ torsion`, which is `ℵ₀` (`Refutation.lean`). -/
def DualRankBound (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'],
    Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)
      ≤ (Module.finrank ℚ K : Cardinal)

/-- **The corrected rank theory reduces to the idèle-side bound.**  If the dual rank is bounded by
`[K : ℚ]` (the idèle computation of CoNF (10.3.20)) and the evaluation inequality
`rank HausQuot ≤ rank Dual` holds (`NK.RankTheoryDeep.rank_hausQuot_le_rank_dual`, proved from
the definition of `invisibleSubmodule`), then the *corrected* finiteness input
`NK.RankTheoryDeep.HausQuotRankFinite Ω ℓ` follows: `rank HausQuot ≤ [K : ℚ] < ℵ₀`.

This replaces the falsified `NK.ShimizuRank.GammaTFRankFinite` (which asserted the same
finiteness for the *torsion-free* quotient, and is false) by the correct object, and reduces the
corrected residual to the idèle-class-group computation — which is the half of input (iv) that does
not need class field theory. -/
theorem hausQuotRankFinite_of_dualRankBound {ℓ : ℕ} [Fact ℓ.Prime]
    (h : DualRankBound Ω ℓ) : HausQuotRankFinite Ω ℓ := by
  intro K _ _ K' _ _ _
  have hle := h K K'
  have hfin : Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual (NK.Reconstruct.Gamma K K' ℓ) ℓ)
      < ℵ₀ :=
    lt_of_le_of_lt hle (by exact_mod_cast Cardinal.natCast_lt_aleph0)
  exact lt_of_le_of_lt (rank_hausQuot_le_rank_dual (ℓ := ℓ) hfin) hfin

end NK.RankTheoryDeep
