import Submission.NK.RankTheoryDeep.IdeleRank
import Submission.NK.RankTheoryDeep.RankTop
import Submission.NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt

/-!
# The corrected rank statements, in the vocabulary of `rank HausQuot`

`Refutation.lean` shows that `rankGamma` (= `Module.finrank (ℤ_ℓ) (Γ_K ⧸ torsion)`) is *not* the
invariant `r_ℓ(K)` of Shimizu's §4; the correct object is the Hausdorff quotient
`HausQuot K K' ℓ` (`IdeleRank.lean`).  This file restates, in the same shape as the residual fields
`NK.ShimizuRank.LeopoldtDefectMono`, `NK.Reconstruct.RankStrictMonoLevelInputGen` and
`NK.Reconstruct.ResRankInputGen`, the three rank statements with `rank HausQuot` in place of
`rankGamma` — so that the Shimizu chapter can be re-wired onto the correct object without
re-deriving their shape.

The `ℕ`-valued invariant used here is

  `NK.RankTheoryDeep.hausRank K K' ℓ = Module.finrank (ℤ_ℓ) (HausQuot K K' ℓ)`,

which is the honest `r_ℓ(K)` **provided** the rank is finite — which is exactly the corrected
finiteness input `HausQuotRankFinite Ω ℓ` (`Corrected.lean`), now a theorem of the idèle-side bound
`DualRankBound Ω ℓ` (`hausQuotRankFinite_of_dualRankBound`).  As in `NK.ShimizuRank`, the pair
(finiteness, formula) is carried together; Leopoldt's conjecture is not assumed anywhere.

## Main results

* `NK.RankTheoryDeep.LeopoldtDefectMonoHaus`, `NK.RankTheoryDeep.HausRankStrictMono`,
  `NK.RankTheoryDeep.ResRankInputHaus` — the corrected residual fields;
* **`NK.RankTheoryDeep.hausRankStrictMono_of_leopoldt`** — Shimizu's Lemma 4f.2 in its corrected
  form, proved from the corrected defect monotonicity exactly as
  `NK.ShimizuRank.rankStrictMonoLevelInputGen_of_leopoldt` is proved from the original one (the
  same pure `ℕ`-arithmetic, the arithmetic half being the *proved*
  `NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.RankTheoryDeep

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- `r_ℓ(K)` computed on the **Hausdorff** quotient: `Module.finrank (ℤ_ℓ) (HausQuot K K' ℓ)`.

This is the honest `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` when the rank is finite — the finiteness being
the corrected input `HausQuotRankFinite Ω ℓ` — and it must *not* be confused with
`NK.Reconstruct.rankGamma = finrank (Γ_K ⧸ torsion)`, whose infinite-rank degeneration is the
subject of `Refutation.lean`. -/
noncomputable def hausRank (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : ℕ :=
  Module.finrank (PadicInt ℓ) (HausQuot K K' ℓ)

/-- **The corrected monotonicity of the Leopoldt defect** (CoNF (10.3.7) Corollary and the proof of
(10.3.11) Corollary), stated for the Hausdorff quotient: the difference
`r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)` of `NK.ShimizuRank.LeopoldtDefectMono`, with `r_ℓ` computed
on `HausQuot` instead of `Γ_K ⧸ torsion`.

Unlike `NK.ShimizuRank.LeopoldtDefectMono` — which, because `rankGamma` degenerates to `0`
whenever the honest rank is infinite, degenerates into the false assertion that the number of
complex places decreases (`README.md` §3, §6) — this statement is a theorem of CoNF (10.3.7), and it
is the form the corrected Shimizu chapter should consume. -/
def LeopoldtDefectMonoHaus (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω],
    M.L ≤ N.L →
      hausRank ↥M.L Ω ℓ + rComplex ↥N.L ≤ hausRank ↥N.L Ω ℓ + rComplex ↥M.L

/-- **Shimizu's Lemma 4f.2, corrected**: for finite levels `M ⊊ N` with `N` having a complex prime,
`r_ℓ(M) < r_ℓ(N)` for the Hausdorff quotient.  This is
`NK.Reconstruct.RankStrictMonoLevelInputGen` with `rankGamma` replaced by `hausRank`. -/
def HausRankStrictMono (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω], M.L ≤ N.L → M.L ≠ N.L →
    (∃ v : NumberField.InfinitePlace ↥N.L, NumberField.InfinitePlace.IsComplex v) →
      hausRank ↥M.L Ω ℓ < hausRank ↥N.L Ω ℓ

/-- **The corrected rank step of Shimizu's Proposition 4f.5**:
`NK.Reconstruct.ResRankInputGen` with `rankGamma` replaced by `hausRank`, i.e. the statement that
in the situation of Prop. 4f.5 (`K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`, `M = K₁ ∩ K₂`) one has
`r_ℓ(K₁) ≤ r_ℓ(M)` for the correct invariant. -/
def ResRankInputHaus (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω],
    M.L = (K₁.L ⊓ K₂.L) → (K₁.L ≤ L.L) → (K₂.L ≤ L.L) →
    (levelInfinityOf K₁ ℓ ⊔ L.L = L.L ⊔ levelInfinityOf K₂ ℓ) →
      hausRank ↥K₁.L Ω ℓ ≤ hausRank ↥M.L Ω ℓ

/-- **Shimizu's Lemma 4f.2 in its corrected form**, proved from the corrected defect monotonicity
exactly as `NK.ShimizuRank.rankStrictMonoLevelInputGen_of_leopoldt` is proved from the original
one: `r_ℂ` strictly increases (`NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`, unconditional),
and the defect monotonicity is pure `ℕ`-arithmetic. -/
theorem hausRankStrictMono_of_leopoldt {ℓ : ℕ} [Fact ℓ.Prime]
    (h : LeopoldtDefectMonoHaus Ω ℓ) : HausRankStrictMono Ω ℓ := by
  intro M N _ _ hMN hne hv
  have hrc : rComplex ↥M.L < rComplex ↥N.L := NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt M N hMN hne hv
  have hmono := h M N hMN
  by_contra hcon
  push Not at hcon
  omega

/-- **The fully corrected residual structure of the Shimizu rank chapter.**

All four fields are stated with the *correct* invariant (the Hausdorff quotient / the idèle-side
dual), as opposed to `NK.ShimizuRank.Residuals`, whose `rankFinite` field is refuted
(`Refutation.lean`) and whose `leopoldt` and `resKernel` fields are stated with the degenerating
`rankGamma` (`README.md` §3).  The finiteness field is the idèle-side bound
`NK.RankTheoryDeep.DualRankBound Ω ℓ` (CoNF (10.3.20)), from which the corrected finiteness
statement `NK.RankTheoryDeep.HausQuotRankFinite Ω ℓ` is *proved*
(`hausQuotRankFinite_of_dualRankBound`). -/
structure CorrectedResidualsHaus (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- CoNF (10.3.7) Cor. and the proof of (10.3.11) Cor., for `hausRank` -/
  leopoldt : LeopoldtDefectMonoHaus Ω ℓ
  /-- **the idèle-side rank bound** `rank Hom_cts(C_K, ℤ_ℓ) = r_ℓ(K) ≤ [K : ℚ]`, CoNF (10.3.20) -/
  dualRank : DualRankBoundTop Ω ℓ
  /-- the rank step of Proposition 4f.5, for `hausRank` -/
  resKernel : ResRankInputHaus Ω ℓ

/-- The corrected residual structure yields the corrected finiteness statement, and Shimizu's
Lemma 4f.2 in corrected form. -/
theorem hausQuotRankFinite_of_correctedResidualsHaus {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsHaus Ω ℓ) :
    HausQuotRankFiniteTop Ω ℓ ∧ HausRankStrictMono Ω ℓ :=
  ⟨hausQuotRankFiniteTop_of_dualRankBoundTop h.dualRank,
    hausRankStrictMono_of_leopoldt h.leopoldt⟩

end NK.RankTheoryDeep
