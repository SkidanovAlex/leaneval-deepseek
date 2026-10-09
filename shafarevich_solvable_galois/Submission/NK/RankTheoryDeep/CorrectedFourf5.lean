import Submission.NK.RankTheoryDeep.CorrectedPackage
import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.fourf5Rank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shimizu's Proposition 4f.5 with a **satisfiable** hypothesis

`NK.Reconstruct.fourf5_gen_of_rankInputs` derives Proposition 4f.5 (`Fourf5InputGen Ω ℓ`) from the
three `rankGamma`-inputs `HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen` — of which
the first is **false** (`not_hausRankInput`) and the third is stated on the wrong invariant.  This
file proves the same theorem from the *corrected* inputs, in the shape the Shimizu §4f endgame
consumes:

```lean
fourf5Gen_of_correctedRankInputs : HausRankStrictMono Ω ℓ → ResRankInputHaus Ω ℓ → Fourf5InputGen Ω ℓ
fourf5Input_of_correctedRankInputs : ... → Fourf5Input Ω ℓ                      -- the FrobLevel form
fourf5Gen_of_correctedResidualsDeep : CorrectedResidualsDeep Ω ℓ → Fourf5InputGen Ω ℓ
fourf5Input_of_correctedResidualsDeep : CorrectedResidualsDeep Ω ℓ → Fourf5Input Ω ℓ
```

The proof is Shimizu's, verbatim from `fourf5_gen_of_rankInputs`, with `hausRank` (the rank of the
Hausdorff quotient) in place of `rankGamma` — the only simplification is that the identification of
the two models of `Γ_K` (the false `HausRankInput`) is no longer needed, because `hausRank` *is* the
rank of `HausQuot` by definition.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField

namespace NK.RankTheoryDeep

open NK.Reconstruct

universe u

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **Shimizu's Proposition 4f.5 from the corrected rank inputs.**  With `M := K₁ ∩ K₂`:

1. `r_ℓ(K₁) = r_ℓ(K₂)`, because the kernels of `π_{L/K₁}` and `π_{L/K₂}` agree
   (`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`);
2. the Proposition 4f.5 rank step `ResRankInputHaus` gives `r_ℓ(K₁) ≤ r_ℓ(M)`, and Lemma 4f.2
   (`HausRankStrictMono`) applied to `M ⊆ K₁` (with `K₁` having a complex prime) forces `M = K₁`,
   i.e. `K₁ ⊆ K₂`;
3. `K₂` then has a complex prime (`NK.Reconstruct.numberField_complex_of_le`), and Lemma 4f.2
   applied to the strict inclusion `K₁ ⊆ K₂` contradicts the equality of ranks. -/
theorem fourf5Gen_of_correctedRankInputs (ℓ : ℕ) [Fact ℓ.Prime]
    (hM : HausRankStrictMono Ω ℓ) (hR : ResRankInputHaus Ω ℓ) : Fourf5InputGen Ω ℓ := by
  intro K₁ K₂ L hsep₁ hsep₂ h₁ h₂ hsup hcomplex
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  -- Step 1: the ℓ-ranks of `K₁` and `K₂` agree.
  have hker := ker_hausPi_eq_of_levelInfinity_eq K₁ K₂ L h₁ h₂ ℓ hsup
  have hrank : hausRank ↥K₁.L Ω ℓ = hausRank ↥K₂.L Ω ℓ := by
    rw [hausRank, hausRank]
    exact congrArg Cardinal.toNat (rank_hausQuot_eq_of_ker_eq K₁ K₂ L h₁ h₂ ℓ hker)
  -- the meet `M = K₁ ∩ K₂`
  let M : NumFieldIn ℚ Ω := K₁.inf K₂
  have hMK₁ : M.L ≤ K₁.L := NumFieldIn.inf_le_left K₁ K₂
  have hMK₂ : M.L ≤ K₂.L := NumFieldIn.inf_le_right K₁ K₂
  have hMsup : M.L = (K₁.L ⊓ K₂.L) := NumFieldIn.inf_L K₁ K₂
  haveI : IsSepClosure ↥M.L Ω := isSepClosure_of_le M.L
  -- Step 2: the rank computation `r_ℓ(K₁) ≤ r_ℓ(M)` forces `M = K₁`.
  have hup : hausRank ↥K₁.L Ω ℓ ≤ hausRank ↥M.L Ω ℓ := hR K₁ K₂ M L hMsup h₁ h₂ hsup
  have hM₁ : M.L = K₁.L := by
    by_contra hne
    exact absurd hup (not_le.mpr (hM M K₁ hMK₁ hne hcomplex))
  have hle : K₁.L ≤ K₂.L := hM₁ ▸ hMK₂
  -- Step 3: Lemma 4f.2 on `K₁ ⊆ K₂` contradicts the equality of ranks.
  obtain ⟨w, hw⟩ := numberField_complex_of_le K₁ K₂ hle hcomplex
  by_contra hne
  exact (ne_of_lt (hM K₁ K₂ hle hne ⟨w, hw⟩)) hrank

/-- **Proposition 4f.5 in the `FrobLevel` form, from the corrected rank inputs.** -/
theorem fourf5Input_of_correctedRankInputs (ℓ : ℕ) [Fact ℓ.Prime]
    (hM : HausRankStrictMono Ω ℓ) (hR : ResRankInputHaus Ω ℓ) : Fourf5Input Ω ℓ :=
  fourf5Input_of_gen (fourf5Gen_of_correctedRankInputs ℓ hM hR)

/-- **Shimizu's Proposition 4f.5 from the corrected residual** — an endgame statement whose
hypothesis `CorrectedResidualsDeep Ω ℓ` has no formal obstruction (unlike the `Residuals` it
replaces, which is unsatisfiable). -/
theorem fourf5Gen_of_correctedResidualsDeep (ℓ : ℕ) [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : Fourf5InputGen Ω ℓ :=
  fourf5Gen_of_correctedRankInputs ℓ (hausRankStrictMono_of_correctedResidualsDeep h)
    (resRankInputHaus_of_correctedResidualsDeep h)

/-- **Proposition 4f.5 in the `FrobLevel` form, from the corrected residual.** -/
theorem fourf5Input_of_correctedResidualsDeep (ℓ : ℕ) [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : Fourf5Input Ω ℓ :=
  fourf5Input_of_correctedRankInputs ℓ (hausRankStrictMono_of_correctedResidualsDeep h)
    (resRankInputHaus_of_correctedResidualsDeep h)

/-- **Shimizu's Theorem 4.0 (the §4 assembly) from the corrected residual — an endgame statement
with a satisfiable hypothesis.**

This is `NK.Reconstruct.exists_isomorphism_of_prop4f3_data` — the conclusion of the Shimizu §4
route: from the data of Proposition 4f.3 (the `Gamma`-level isomorphism `σbar`, the prime map, the
Frobenius compatibility, the Chebotarev input) and Proposition 4f.5, two finite Galois levels `K₁`,
`K₂` of `Ω/ℚ` with `K₁` having a complex prime are isomorphic.  The on-disk version
(`NK.Reconstruct.exists_isomorphism_of_prop4f3_data_of_rankInputs`,
`NK.ShimizuRank.exists_isomorphism_of_prop4f3_data_of_residual`) requires the three
`rankGamma`-inputs, of which the first is false (`not_hausRankInput`); here Proposition 4f.5 is
supplied by the corrected residual `CorrectedResidualsDeep`, whose fields are named classical
theorems. -/
theorem exists_isomorphism_of_prop4f3_data_of_correctedResiduals {K₁ K₂ L : FrobLevel ℚ Ω}
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]
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
    (hc : ChebotarevInput ℚ Ω) (h : CorrectedResidualsDeep Ω ℓ) :
    ∃ τ : Gal(↥L.L/ℚ), Nonempty (↥K₁.L ≃+* ↥K₂.L) :=
  exists_isomorphism_of_prop4f3_data K₁ K₂ L h₁ h₂ ℓ σbar hσbar primeMap hb hchar Θ hΘmem hΘres
    hcomplex hc (fourf5Input_of_correctedResidualsDeep ℓ h)

end NK.RankTheoryDeep
