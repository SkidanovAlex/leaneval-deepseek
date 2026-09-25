import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.IdeleAssembly
import Submission.NK.RankTheoryDeep.rank_dual_ideleClassGroup_le_integralIdeles
import Submission.NK.RankTheoryDeep.CorrectedRank
import Submission.NK.RankTheoryDeep.RankTop

/-!
# The idèle-side rank theory, assembled: from the local unit structure to `HausQuotRankFiniteTop`

This is the interface of the idèle-side computation of `r_ℓ(K)` (CoNF (10.3.20)) in the form in
which the Shimizu rank theory consumes it, **stated at the separable closure** (see
`ArtinDualBridge` in `IdeleRankDefs.lean` for why the level was too generous: at `K' = K` the
group `Γ_{K/K}` is trivial, so an identification with `Dual (C_K) ℓ` can only hold at `K' = Ω`).

Two inputs are carried, both classical and named:

* `NK.RankTheoryDeep.LocalUnitDualRankInput ℓ` — the **local unit structure** at the places above
  `ℓ` (`𝒪_vˣ ≅ μ_{q-1} × (1 + 𝔪)`, `1 + 𝔪 ≅ ℤ_ℓ^{[K_v : ℚ_ℓ]}`, equivalently
  `NK.LocalCFT.UnitsStructure`): `rank_{ℤ_ℓ} Hom_cts(𝒪_vˣ, ℤ_ℓ) ≤ e_v f_v`.  Everything else in
  the *idèle* half is proved in this directory (`IdeleAssembly.lean`).
* `NK.RankTheoryDeep.ArtinDualBridge Ω ℓ` — **ℓ-adic Artin reciprocity** at `K' = Ω`:
  `Dual (Γ_K^{Ω}) ℓ ≅ Dual (C_K) ℓ`.

From these two, the finiteness of the `ℤ_ℓ`-rank of the Hausdorff quotient at the separable closure —
`HausQuotRankFiniteTop Ω ℓ` — is a **theorem**, as is the sharp rank bound `rank (HausQuot K Ω ℓ) ≤
[K : ℚ]`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField
open Cardinal

namespace NK.RankTheoryDeep

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The idèle-side rank bound, from the local unit structure.**  `rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ) =
r_ℓ(K) ≤ [K : ℚ]`: the local unit structure at the places above `ℓ` bounds the character module of
`∏_v 𝒪_vˣ` by `∑_{v | ℓ} e_v f_v = [K : ℚ]` (`IdeleAssembly.lean`), and the class group is finite,
so `C_K` — a quotient of `∏_v 𝒪_vˣ` by `𝒪_Kˣ` with finite cokernel `Cl(K)` — has no more
characters.  This is the half of input (iv) of the request that does not need class field theory. -/
theorem ideleDualRankBound_of_localUnits {ℓ : ℕ} [Fact ℓ.Prime]
    (h : LocalUnitDualRankInput.{u} ℓ) : IdeleDualRankBound.{u} ℓ := by
  intro K _ _
  exact le_trans (rank_dual_ideleClassGroup_le_integralIdeles K) (rank_dual_integralIdeles_le K h)

/-- **ℓ-adic Artin reciprocity converts the idèle-side bound into the `Γ`-side bound at `Ω`.** -/
theorem dualRankBoundTop_of_idele {ℓ : ℕ} [Fact ℓ.Prime] (hb : ArtinDualBridge Ω ℓ)
    (h : IdeleDualRankBound.{u} ℓ) : DualRankBoundTop Ω ℓ := by
  intro K _ _ _ _
  have h1 := hb K
  have h2 := h K
  simp only [dualRank] at h1 h2
  rw [h1]
  exact h2

/-- **The sharp rank bound**: `rank_{ℤ_ℓ} (Γ_K^{Ω} ⧸ invisible) ≤ [K : ℚ]`.  This is the form of
CoNF (10.3.20) that the Shimizu rank theory consumes (the rank is classically
`r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)`). -/
theorem hausRank_le_finrank {ℓ : ℕ} [Fact ℓ.Prime] (h : LocalUnitDualRankInput.{u} ℓ)
    (hb : ArtinDualBridge Ω ℓ) (K : Type u) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois K Ω] :
    Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K Ω ℓ)
      ≤ (Module.finrank ℚ K : Cardinal) :=
  hausQuotRank_le_rank_dual_top (dualRankBoundTop_of_idele hb (ideleDualRankBound_of_localUnits h)) K

/-- **The corrected finiteness statement at the separable closure, from the two classical inputs.** -/
theorem hausQuotRankFiniteTop_of_localUnits_and_artin {ℓ : ℕ} [Fact ℓ.Prime]
    (h : LocalUnitDualRankInput.{u} ℓ) (hb : ArtinDualBridge Ω ℓ) :
    HausQuotRankFiniteTop Ω ℓ :=
  fun K _ _ _ _ =>
    lt_of_le_of_lt (hausRank_le_finrank h hb K)
      (by exact_mod_cast Cardinal.natCast_lt_aleph0)

/-- **The corrected residual structure of the Shimizu rank chapter**, with the rank theory in the
idèle-side form: the falsified `NK.ShimizuRank.GammaTFRankFinite` is replaced by the
**idèle-side dual rank bound** `NK.RankTheoryDeep.IdeleDualRankBound ℓ` (CoNF (10.3.20)), and the
two rank fields are stated for the honest invariant `rank (HausQuot)` rather than the degenerate
`rankGamma`.  The field `InvisibleSubgroupTorsion` of the old residual is **not** present: it is
refuted (`NK.RankTheoryDeep.not_invisibleSubgroupTorsion_of_localUnits_and_artin`). -/
structure CorrectedResidualsIdele (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- CoNF (10.3.7) Cor. and the proof of (10.3.11) Cor., for the honest invariant `rank HausQuot` -/
  leopoldt : LeopoldtDefectMonoHaus Ω ℓ
  /-- **the idèle-side rank bound** `rank Hom_cts(C_K, ℤ_ℓ) = r_ℓ(K) ≤ [K : ℚ]`, CoNF (10.3.20) -
  the corrected replacement of the falsified `GammaTFRankFinite` -/
  dualRank : IdeleDualRankBound.{u} ℓ
  /-- the rank computation of Proposition 4f.5, for the honest invariant -/
  resKernel : ResRankInputHaus Ω ℓ

/-- The corrected idèle-side residual yields the corrected finiteness statement as soon as
ℓ-adic Artin reciprocity is available. -/
theorem hausQuotRankFiniteTop_of_correctedResidualsIdele {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResidualsIdele Ω ℓ) (hb : ArtinDualBridge Ω ℓ) : HausQuotRankFiniteTop Ω ℓ :=
  hausQuotRankFiniteTop_of_dualRankBoundTop (dualRankBoundTop_of_idele hb h.dualRank)

/-- **The corrected residual, with the rank finiteness proved from the local input.**  Given the
local unit structure at `v | ℓ`, ℓ-adic Artin reciprocity, and the two remaining residual fields
(Leopoldt defect monotonicity and Shimizu's Proposition 4f.5 rank step, both for the honest invariant
`rank HausQuot`), the corrected residual `NK.RankTheoryDeep.CorrectedResidualsHaus Ω ℓ` holds. -/
theorem correctedResidualsHaus_of_idele {ℓ : ℕ} [Fact ℓ.Prime]
    (h : LocalUnitDualRankInput.{u} ℓ) (hb : ArtinDualBridge Ω ℓ) (hl : LeopoldtDefectMonoHaus Ω ℓ)
    (hr : ResRankInputHaus Ω ℓ) : CorrectedResidualsHaus Ω ℓ :=
  ⟨hl, dualRankBoundTop_of_idele hb (ideleDualRankBound_of_localUnits h), hr⟩

end NK.RankTheoryDeep
