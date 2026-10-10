import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Submission.NK.RankTheoryDeep.IdeleFinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The **corrected residual** of the Shimizu rank chapter, with the rank theory reduced

`NK.ShimizuRank.Residuals Ω ℓ` has four fields, of which

* `rankFinite : GammaTFRankFinite` is **false** for every prime `ℓ` (`not_residuals_prime`),
* `invisible : InvisibleSubgroupTorsion` is **false** (`not_invisibleSubgroupTorsion_of_localUnits_and_artin`),
* `leopoldt : LeopoldtDefectMono` and `resKernel : ResKernelRankInput` are stated in the *degenerate*
  invariant `rankGamma = finrank (Γ_K ⧸ torsion)`.

This file assembles the corrected residual, in the form a consumer can import, with

* the falsified fields replaced by the correct invariant `rank (HausQuot K K' ℓ)` (the Hausdorff,
  dual-faithful quotient, whose rank is the classical `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)`),
* its rank finiteness **proved** from the two named classical inputs of the idèle-side computation
  (`LocalUnitDualRankInput`, `ArtinDualBridge`),
* its two rank statements reduced to their classical granular inputs — the Leopoldt defect data of
  CoNF (10.3.7)/(10.3.20) and Shimizu's kernel-rank duality input `ResKernelRankInput` — with every
  derivation **proved** here,
* and the false field deleted.

The single boundary structure is `NK.RankTheoryDeep.CorrectedResidualsDeep Ω ℓ`, and the
consumer-facing theorems are `hausQuotRankFinite_of_correctedResidualsDeep`,
`leopoldtDefectMonoHaus_of_correctedResidualsDeep`, `hausRankStrictMono_of_correctedResidualsDeep`,
`resRankInputHaus_of_correctedResidualsDeep` and `correctedResidualsHaus_of_correctedResidualsDeep`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField
open Cardinal

namespace NK.RankTheoryDeep

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The Leopoldt defect data of CoNF (10.3.7)/(10.3.20)**, for the correct invariant `r_ℓ`:
there is a "defect" function `δ` on the number-field levels of `Ω` such that

* `r_ℓ(K) = r_ℂ(K) + 1 + δ(K)` for every level `K` (the rank formula (10.3.20)), and
* `δ` is monotone along inclusions (CoNF (10.3.7) Corollary).

The *finiteness* of `r_ℓ(K)` — the field `finite` of the on-disk `NK.Reconstruct.RankFormulaInput`,
which makes the on-disk version unsatisfiable because it is stated for `rankGamma` — is **not** part
of this input: for the corrected invariant it is a theorem
(`hausQuotRankFinite_of_localUnits_and_artin`).  The upper bound `r_ℓ(K) ≤ [K : ℚ]` is likewise a
theorem (`hausRank_le_finrank`). -/
def HausLeopoldtData (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ δ : NumFieldIn ℚ Ω → ℕ,
    (∀ (M N : NumFieldIn ℚ Ω), M.L ≤ N.L → δ M ≤ δ N) ∧
      ∀ (K : NumFieldIn ℚ Ω), hausRank ↥K.L Ω ℓ = rComplex ↥K.L + 1 + δ K

/-- **`LeopoldtDefectMonoHaus` from the defect data**: the difference estimate
`r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)` of CoNF (10.3.7) is the `ℕ`-arithmetic consequence of the rank
formula and the monotonicity of `δ`, exactly as
`NK.ShimizuRank.leopoldtDefectMono_of_rankFormula` derives the `rankGamma` version. -/
theorem leopoldtDefectMonoHaus_of_data {ℓ : ℕ} [Fact ℓ.Prime] (h : HausLeopoldtData Ω ℓ) :
    LeopoldtDefectMonoHaus Ω ℓ := by
  obtain ⟨δ, hmono, hform⟩ := h
  intro M N _ _ hMN
  rw [hform M, hform N]
  have := hmono M N hMN
  omega

/-- **`ResRankInputHaus` from Shimizu's kernel-rank computation** `ResKernelRankInput`.

This is the corrected counterpart of `NK.ShimizuRank.resRankInputGen_of_residual`, and it is
*sharper*: the on-disk reduction from `ResKernelRankInput` to `ResRankInputGen` needed the extra
hypothesis `HausRankInput` (the identification `rankGamma = rank HausQuot`), because `rankGamma`
computes the rank of the wrong group; for the corrected invariant `hausRank = rank (HausQuot)` the
identification is the definition, and the base-change calculus alone gives the reduction.

The two ranks involved are the `ℤ_ℓ`-ranks of the same quotient
`Γ_L^{tf} ⧸ ker π` (`rank_hausQuot_eq_rank_quot_ker`), so the inequality of
cardinals of `ResKernelRankInput` transfers to the `finrank`s `hausRank`. -/
theorem resRankInputHaus_of_resKernel {ℓ : ℕ} [Fact ℓ.Prime]
    (hfin : HausQuotRankFiniteTop Ω ℓ) (hK : NK.ShimizuRank.ResKernelRankInput Ω ℓ) :
    ResRankInputHaus Ω ℓ := by
  intro K₁ K₂ M L _ _ _ hMsup h₁ h₂ hsup
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  have hM : M.L ≤ L.L := by rw [hMsup]; exact le_trans inf_le_left h₁
  have hr₁ := rank_hausQuot_eq_rank_quot_ker K₁ L h₁ ℓ
  have hrM := rank_hausQuot_eq_rank_quot_ker M L hM ℓ
  have h := hK K₁ K₂ M L hMsup h₁ h₂ hM hsup
  have hfinM : Module.rank (PadicInt ℓ) (HausQuot ↥L.L Ω ℓ ⧸
      LinearMap.ker (hausPi M L hM ℓ)) < ℵ₀ := by
    rw [← hrM]
    exact hfin ↥M.L
  show hausRank ↥K₁.L Ω ℓ ≤ hausRank ↥M.L Ω ℓ
  simp only [hausRank, Module.finrank, hr₁, hrM]
  exact Cardinal.toNat_le_toNat h hfinM

/-- **The corrected residual of the Shimizu rank chapter, deep form.**  All four fields of the
on-disk `NK.ShimizuRank.Residuals` have been dealt with:

* the falsified `rankFinite` is replaced by the *two named classical inputs* of the idèle-side
  computation (`localUnits`, `artin`), from which the correct finiteness statement
  `HausQuotRankFinite Ω ℓ` is a theorem (`hausQuotRankFinite_of_localUnits_and_artin`);
* the falsified `invisible` is deleted (`not_invisibleSubgroupTorsion_of_localUnits_and_artin`);
* `leopoldt` is replaced by the granular `HausLeopoldtData` (CoNF (10.3.7)/(10.3.20) for the correct
  invariant), from which `LeopoldtDefectMonoHaus` is a theorem;
* `resKernel` is kept, in the kernel form `ResKernelRankInput` in which the mathematics sits, from
  which `ResRankInputHaus` is a theorem. -/
structure CorrectedResidualsDeep (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- the local unit structure at the places above `ℓ` (CoNF Ch. X §10.3 local unit theorem) -/
  localUnits : LocalUnitDualRankInput.{u} ℓ
  /-- ℓ-adic Artin reciprocity (`G_K^{ab,(ℓ)} ≅ (C_K)^{pro-ℓ}` in dual form) -/
  artin : ArtinDualBridge Ω ℓ
  /-- CoNF (10.3.7) Corollary + (10.3.20), in the form of the defect data -/
  leopoldt : HausLeopoldtData Ω ℓ
  /-- Shimizu's kernel-rank duality input (the rank step of Proposition 4f.5) -/
  resKernel : NK.ShimizuRank.ResKernelRankInput Ω ℓ

/-- **The rank finiteness of the corrected residual is a theorem.** -/
theorem hausQuotRankFiniteTop_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : HausQuotRankFiniteTop Ω ℓ :=
  hausQuotRankFiniteTop_of_localUnits_and_artin h.localUnits h.artin

/-- **The Leopoldt defect monotonicity of the corrected residual is a theorem.** -/
theorem leopoldtDefectMonoHaus_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : LeopoldtDefectMonoHaus Ω ℓ :=
  leopoldtDefectMonoHaus_of_data h.leopoldt

/-- **Shimizu's Lemma 4f.2 in corrected form, from the corrected residual.** -/
theorem hausRankStrictMono_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : HausRankStrictMono Ω ℓ :=
  hausRankStrictMono_of_leopoldt (leopoldtDefectMonoHaus_of_correctedResidualsDeep h)

/-- **The rank step of Shimizu's Proposition 4f.5, corrected, from the corrected residual.** -/
theorem resRankInputHaus_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : ResRankInputHaus Ω ℓ :=
  resRankInputHaus_of_resKernel (hausQuotRankFiniteTop_of_correctedResidualsDeep h) h.resKernel

/-- **The corrected residual, in the shape the Shimizu chapter consumes**: the three corrected rank
statements, with the finiteness proved from the two idèle-side inputs. -/
theorem correctedResidualsHaus_of_correctedResidualsDeep {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsDeep Ω ℓ) : CorrectedResidualsHaus Ω ℓ :=
  ⟨leopoldtDefectMonoHaus_of_correctedResidualsDeep h,
    dualRankBoundTop_of_idele h.artin (ideleDualRankBound_of_localUnits h.localUnits),
    resRankInputHaus_of_correctedResidualsDeep h⟩

end NK.RankTheoryDeep
