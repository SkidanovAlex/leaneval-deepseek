import Submission.NK.ShimizuRank.StrictMono
import Submission.NK.ShimizuRank.HausRank
import Submission.NK.ShimizuRank.ResRank

/-!
# The packaged rank inputs, and the consumer-facing corollaries

This file assembles the residual inputs of the chapter into a single structure and re-exports, in
the vocabulary the endgame (`Submission/Work/Reconstruct/`) consumes, the results that the
reconstruction needs:

* `NK.ShimizuRank.Residuals Ω ℓ` — the four residuals
  (`LeopoldtDefectMono`, `InvisibleSubgroupTorsion`, `GammaTFRankFinite`, `ResKernelRankInput`);
* `NK.ShimizuRank.rankInputs` — `HausRankInput Ω ℓ ∧ RankStrictMonoLevelInputGen Ω ℓ ∧
  ResRankInputGen Ω ℓ` from `Residuals Ω ℓ`, i.e. exactly the three named inputs of the endgame;
* `NK.ShimizuRank.rankStrictMono_of_complex` — Shimizu's Lemma 4f.2 as a standalone statement,
  from `Residuals`;
* `NK.ShimizuRank.fourf5InputGen_of_residual` / `NK.ShimizuRank.fourf5Input_of_residual` —
  Shimizu's **Proposition 4f.5** from `Residuals`;
* `NK.ShimizuRank.exists_isomorphism_of_prop4f3_data_of_residual` — Shimizu's Theorem 4.0
  (the assembly): from the data of Proposition 4f.3, the Čebotarev input and `Residuals`, the two
  base fields are isomorphic.  This is the strongest consumer-facing form delivered here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.ShimizuRank

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The four residual named inputs of the rank chapter.**

* `leopoldt` — the monotonicity of the Leopoldt defect, CoNF (10.3.7) Corollary and the proof of
  (10.3.11) Corollary;
* `invisible` — the invisible subgroup of `Γ_K` is a torsion group (the ℓ-adic structure theory of
  `G_K^{ab,(ℓ)}`);
* `rankFinite` — the first half of CoNF (10.3.20), `Γ_K^{tf}` has finite `ℤ_ℓ`-rank;
* `resKernel` — the rank (kernel) computation of Shimizu's proof of Proposition 4f.5 (the
  transfer/duality step).

Each is a theorem of the literature; see `Basic.lean` for the audit of each. -/
structure Residuals (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- CoNF (10.3.7) Cor. + the proof of (10.3.11) Cor. -/
  leopoldt : LeopoldtDefectMono Ω ℓ
  /-- `Γ_K ⧸ invisible = Γ_K ⧸ torsion`, i.e. CoNF (10.3.20) structure theory -/
  invisible : InvisibleSubgroupTorsion Ω ℓ
  /-- `Γ_K^{tf}` has finite `ℤ_ℓ`-rank: the first half of CoNF (10.3.20) -/
  rankFinite : GammaTFRankFinite Ω ℓ
  /-- the rank computation of Shimizu's Proposition 4f.5 -/
  resKernel : ResKernelRankInput Ω ℓ

/-- **The three rank inputs of the endgame from the residuals.**  This is the packaged form asked
for by the reconstruction: `HausRankInput Ω ℓ ∧ RankStrictMonoLevelInputGen Ω ℓ ∧
ResRankInputGen Ω ℓ`. -/
theorem rankInputs {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) :
    HausRankInput Ω ℓ ∧ RankStrictMonoLevelInputGen Ω ℓ ∧ ResRankInputGen Ω ℓ :=
  ⟨hausRankInput_of_residual h.invisible h.rankFinite,
    rankStrictMonoLevelInputGen_of_leopoldt h.leopoldt,
    resRankInputGen_of_residual (hausRankInput_of_residual h.invisible h.rankFinite) h.resKernel⟩

/-- **The three rank inputs in the `FrobLevel` form** that
`Submission/Work/Reconstruct/fourf5Rank.lean` consumes (`NK.Reconstruct.Fourf5Input` is proved
there from `HausRankInput`, `RankStrictMonoLevelInput ℚ Ω ℓ` and `ResRankInput Ω ℓ`). -/
theorem rankInputsLevel {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) :
    HausRankInput Ω ℓ ∧ RankStrictMonoLevelInput ℚ Ω ℓ ∧ ResRankInput Ω ℓ :=
  ⟨(rankInputs h).1, rankStrictMonoLevelInput_of_gen (rankInputs h).2.1,
    resRankInput_of_gen (rankInputs h).2.2⟩

/-- **`NK.Reconstruct.RankStrictMonoLevelInput ℚ Ω ℓ` from the residuals** — the Galois-over-`ℚ`
form of Shimizu's Lemma 4f.2. -/
theorem rankStrictMonoLevelInput_of_residual {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) :
    RankStrictMonoLevelInput ℚ Ω ℓ :=
  (rankInputsLevel h).2.1

/-- **`NK.Reconstruct.ResRankInput Ω ℓ` from the residuals** — the `FrobLevel` form of the rank
computation of Shimizu's Proposition 4f.5. -/
theorem resRankInput_of_residual {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) : ResRankInput Ω ℓ :=
  (rankInputsLevel h).2.2

/-- **Shimizu's Lemma 4f.2** (`M ⊊ N` with `N` having a complex prime implies `r_ℓ(M) < r_ℓ(N)`),
as a standalone statement from the residuals: this is the form in which the proof of
Proposition 4f.5 and the reconstruction consume the strict monotonicity of the ℓ-rank. -/
theorem rankStrictMono_of_complex {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ)
    (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω]
    (hMN : M.L ≤ N.L) (hne : M.L ≠ N.L)
    (hv : ∃ v : NumberField.InfinitePlace ↥N.L, NumberField.InfinitePlace.IsComplex v) :
    rankGamma ↥M.L Ω ℓ < rankGamma ↥N.L Ω ℓ :=
  (rankInputs h).2.1 M N hMN hne hv

/-- **Shimizu's Proposition 4f.5 from the residuals** (arbitrary number fields inside `Ω`). -/
theorem fourf5InputGen_of_residual {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) :
    Fourf5InputGen Ω ℓ :=
  fourf5_gen_of_rankInputs ℓ (rankInputs h).1 (rankInputs h).2.1 (rankInputs h).2.2

/-- **Shimizu's Proposition 4f.5 from the residuals** (Galois-over-`ℚ` levels), the form consumed
by the reconstruction. -/
theorem fourf5Input_of_residual {ℓ : ℕ} [Fact ℓ.Prime] (h : Residuals Ω ℓ) : Fourf5Input Ω ℓ :=
  fourf5Input_of_gen (fourf5InputGen_of_residual h)

/-- **Shimizu's Theorem 4.0 (the assembly) from the residuals**: from the data of
Proposition 4f.3, the Čebotarev input and the four residuals, the two base fields `K₁`, `K₂` are
isomorphic.  This is `NK.Reconstruct.exists_isomorphism_of_prop4f3_data` with its four rank
hypotheses discharged by `NK.ShimizuRank.Residuals`. -/
theorem exists_isomorphism_of_prop4f3_data_of_residual {ℓ : ℕ} [Fact ℓ.Prime]
    {K₁ K₂ L : FrobLevel ℚ Ω} (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (σbar : Gamma ↥K₁.L Ω ℓ ≃* Gamma ↥K₂.L Ω ℓ) (hσbar : Continuous ⇑σbar)
    (primeMap : NK.Chebotarev.PrimeIdeal ↥K₁.L ≃ NK.Chebotarev.PrimeIdeal ↥K₂.L)
    (hb : ∀ (𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L) (g₁ : Gal(Ω/↥K₁.L)) (g₂ : Gal(Ω/↥K₂.L)),
        IsFrobElementAt 𝔭 g₁ → IsFrobElementAt (primeMap 𝔭) g₂ →
        σbar (galToGamma (K := ↥K₁.L) (K' := Ω) ℓ g₁) =
          galToGamma (K := ↥K₂.L) (K' := Ω) ℓ g₂)
    (hchar : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥K₁.L,
        Ideal.under ℤ (primeMap 𝔭).asIdeal = Ideal.under ℤ 𝔭.asIdeal)
    (Θ : Gal(↥L.L/ℚ) → Ω ≃ₐ[ℚ] Ω)
    (hΘmem : ∀ τ, ∀ x : Ω, x ∈ L.L ↔ Θ τ x ∈ L.L)
    (hΘres : ∀ τ (x : ↥L.L), Θ τ (x : Ω) = (τ x : Ω))
    (hcomplex : ∃ v : NumberField.InfinitePlace ↥K₁.L, NumberField.InfinitePlace.IsComplex v)
    (hc : ChebotarevInput ℚ Ω) (h : Residuals Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), Nonempty (↥K₁.L ≃+* ↥K₂.L) :=
  exists_isomorphism_of_prop4f3_data_of_rankInputs h₁ h₂ ℓ σbar hσbar primeMap hb hchar
    Θ hΘmem hΘres hcomplex hc (rankInputs h).1 (rankStrictMonoLevelInput_of_gen (rankInputs h).2.1)
    (resRankInput_of_gen (rankInputs h).2.2)

end NK.ShimizuRank
