/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.NUV2.ideleDefs

/-!
# The idèle-side rank data for `NK.NUV2.ideleRankFormula_attempt`

The vocabulary in which the idèle-side rank formula of CoNF (10.3.20) / (10.3.7) is proved:

* `idcDualRank K` — `a_K = finrank_{ℤ_2} Hom_cts(C_K, ℤ_2)`, the idèle-side rank of `K`;
* `intDualRank K` — `m_K = finrank_{ℤ_2} Hom_cts(𝕀_int K, ℤ_2)`;
* `unitsImgRank K` — `u_K`, the `ℤ_2`-rank of the image of the restriction
  `Dual (𝕀_int K) →ₗ (𝒪_Kˣ →+ ℤ_2)`;
* `defectRho K` — `ρ_K = r_1(K) + r_2(K) - 1`, the number of infinite places of `K` minus one.

The main arithmetic identity is `a_K = ρ_K + r_ℂ(K) + 1 - u_K`, whence the defect
`δ_K = a_K - r_ℂ(K) - 1 = ρ_K - u_K` is monotone as soon as `u_N - u_M ≤ ρ_N - ρ_M` for `M ⊆ N`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.NUV2

open NK.GlobalCFT

/-- `a_K = finrank_{ℤ_2} Hom_cts(C_K, ℤ_2)`: the idèle-side rank of the number field `K`. -/
noncomputable def idcDualRank (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2)

/-- `m_K = finrank_{ℤ_2} Hom_cts(𝕀_int K, ℤ_2)`: the rank of the character module of the
integral idèles `∏_v 𝒪_vˣ`. -/
noncomputable def intDualRank (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank (PadicInt 2) (NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) 2)

/-- `u_K`: the `ℤ_2`-rank of the image of the restriction of a continuous character of the
integral idèles to the global units `𝒪_Kˣ ⊆ 𝕀_int K`. -/
noncomputable def unitsImgRank (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank (PadicInt 2) (LinearMap.range (restrictUnits (K := K)))

/-- `ρ_K = r_1(K) + r_2(K) - 1`, the number of infinite places of `K` minus one: by Dirichlet this
is the rank of `𝒪_Kˣ`, and `[K : ℚ] = ρ_K + r_ℂ(K) + 1`. -/
noncomputable def defectRho (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K + NumberField.InfinitePlace.nrComplexPlaces K - 1

/-- **The arithmetic identity** `ρ_K + r_ℂ(K) + 1 = [K : ℚ]`: with `[K : ℚ] = r_1 + 2 r_2` and
`ρ_K = r_1 + r_2 - 1`. -/
theorem defectRho_add_rComplex_add_one (K : Type*) [Field K] [NumberField K] :
    defectRho K + NK.Reconstruct.rComplex K + 1 = Module.finrank ℚ K := by
  have h1 : NK.Reconstruct.rComplex K = NumberField.InfinitePlace.nrComplexPlaces K := by
    classical
    rw [NK.Reconstruct.rComplex, NumberField.InfinitePlace.nrComplexPlaces]
    exact Nat.card_eq_fintype_card
  have h2 : NumberField.InfinitePlace.nrRealPlaces K
      + 2 * NumberField.InfinitePlace.nrComplexPlaces K = Module.finrank ℚ K :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have h3 : 1 ≤ NumberField.InfinitePlace.nrRealPlaces K
      + NumberField.InfinitePlace.nrComplexPlaces K := by
    have hcard : 0 < Fintype.card (NumberField.InfinitePlace K) :=
      Fintype.card_pos_iff.mpr (inferInstance : Nonempty (NumberField.InfinitePlace K))
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces] at hcard
    exact hcard
  rw [defectRho, h1]
  omega

end NK.NUV2
