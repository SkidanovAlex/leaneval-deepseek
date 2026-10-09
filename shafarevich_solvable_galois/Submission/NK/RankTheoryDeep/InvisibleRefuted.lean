import Submission.NK.RankTheoryDeep.IdeleFinal
import Submission.NK.ShimizuRank.HausRank
import Submission.NK.RankTheoryDeep.Unconditional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `InvisibleSubgroupTorsion` is **false**: the invisible subgroup is not torsion

The residual field `NK.ShimizuRank.InvisibleSubgroupTorsion Ω ℓ` says that the invisible subgroup
`invisibleSubmodule K K' ℓ = ⨅_{χ : Dual (Γ_K) ℓ} ker χ` of `Γ_K` is a torsion group, equivalently
(`NK.ShimizuRank.invisibleSubgroupTorsion_iff_eq_torsion`, on disk) that
`invisibleSubmodule = GammaTorsion`, equivalently that the canonical surjection
`Γ_K ⧸ torsion ↠ Γ_K ⧸ invisible` is injective.

**It is false, by the same phenomenon that refutes `GammaTFRankFinite`.**  Since
`GammaTorsion ≤ invisibleSubmodule` holds unconditionally, `InvisibleSubgroupTorsion` forces
`GammaTF K K' ℓ = HausQuot K K' ℓ`; but at `K = ℚ` the torsion-free quotient has `ℤ_ℓ`-rank `ℵ₀`
(`Γ_ℚ ↠ ∏_n ℤ/ℓ^n`, `gamma_surjection_ellTower_prime`), while the Hausdorff quotient has rank at
most `[ℚ : ℚ] = 1` (the proved idèle-side bound `hausRank_le_finrank`, CoNF (10.3.20)).  So the two
quotients differ, exactly by the diagonal `∏_n ℤ/ℓ^n`-part: every continuous character of
`∏_n ℤ/ℓ^n` is trivial (`exists_finset_support_of_dual_pi_of_cofinite`, since each finite factor has
trivial dual), so that whole non-torsion part is invisible.

Consequently the two corrected residual structures `NK.RankTheoryDeep.CorrectedResidualsIdele` and
`NK.RankTheoryDeep.CorrectedResidualsHaus` carry **two**, not three, rank fields
(`dualRank`/`resKernel` and `leopoldt`/`resKernel`), and no theorem of the Shimizu route may use
`InvisibleSubgroupTorsion`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField
open Cardinal

namespace NK.RankTheoryDeep

universe u

/-- **`ℵ₀ ≤ rank (Γ_ℚ^{tf})` for every prime `ℓ`.** -/
theorem aleph0_le_rank_gammaTF_rat_prime (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω]
    [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ℵ₀ ≤ Module.rank (PadicInt ℓ) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) ℓ) := by
  obtain ⟨Φ, hΦ⟩ := gamma_surjection_ellTower_prime ℓ Ω
  exact aleph0_le_rank_of_surjective_tower Φ hΦ

/-- **`InvisibleSubgroupTorsion Ω ℓ` is false, given that the Hausdorff quotient of `Γ_ℚ` has finite
`ℤ_ℓ`-rank.**  (`Ω` is a field of the same universe as `ℚ`, so that `K = ℚ` is a legitimate witness
for the universally quantified `K`; the mathematics is universe-independent, as in the other
refutations of this directory.) -/
theorem not_invisibleSubgroupTorsion_of_finite {ℓ : ℕ} [Fact ℓ.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (hfin : Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) ℓ) < ℵ₀) :
    ¬ NK.ShimizuRank.InvisibleSubgroupTorsion Ω ℓ := by
  intro hI
  -- `InvisibleSubgroupTorsion` is the equality `invisible = torsion`
  have heq := (NK.ShimizuRank.invisibleSubgroupTorsion_iff_eq_torsion (Ω := Ω) (ℓ := ℓ)).mp hI
    ℚ Ω
  -- hence the two quotients coincide
  have hiso : Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) ℓ)
      = Module.rank (PadicInt ℓ) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) ℓ) := by
    dsimp only [NK.Reconstruct.HausQuot, NK.Reconstruct.GammaTF]
    rw [heq]
  -- but one of them has rank `ℵ₀` and the other has finite rank
  have hge := aleph0_le_rank_gammaTF_rat_prime ℓ Ω
  rw [← hiso] at hge
  exact absurd hfin (not_lt.mpr hge)

/-- **`InvisibleSubgroupTorsion Ω ℓ` is false**, from the two named classical inputs of the
idèle-side rank computation: the local unit structure at `v | ℓ` and ℓ-adic Artin reciprocity. -/
theorem not_invisibleSubgroupTorsion_of_localUnits_and_artin (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (h : LocalUnitDualRankInput.{0} ℓ) (hb : ArtinDualBridge Ω ℓ) :
    ¬ NK.ShimizuRank.InvisibleSubgroupTorsion Ω ℓ :=
  not_invisibleSubgroupTorsion_of_finite Ω
    (lt_of_le_of_lt (hausRank_le_finrank h hb ℚ)
      (by rw [Module.finrank_self]; exact Cardinal.one_lt_aleph0))

end NK.RankTheoryDeep
