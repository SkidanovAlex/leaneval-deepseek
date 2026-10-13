/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkSq_JepsPz_le8Bump.lean`

The uniform `ℋᵏ`-bound of the correction profile `bump` up to order `8`
(`Work.FTS.EpsEngine.exists_HkNorm_bump_le8`), needed by the order-`8` assembly
`HkSq_JepsPz_le8_of_slot`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


namespace Work.FTS.EpsEngine

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The correction profile is uniformly bounded in `ℋᵏ`, up to order `8`.**  There is a single
constant `B` with `‖bump‖_{ℋᵏ} ≤ B` for every `α ∈ (0,1]` and every `k ≤ 8`.  This is
`Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le` (`k ≤ 6`, same proof) with the maximum of
the integrand taken at `k = 8` instead of `k = 6`. -/
theorem exists_HkNorm_bump_le8 :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 8 →
      Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := by
  obtain ⟨M, hMnn, hM⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump 1 8
  refine ⟨max 1 (Real.sqrt (M * (Real.pi / 2) * (1 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α hα k hk
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ ≤ M := by
    intro z hz θ hθ
    refine le_trans (le_trans ?_ (Work.FTS.OpenPkg.HkIntegrand_mono_le 1 hk _ z θ)) (hM z θ)
    exact Work.FTS.StrongEps.PZeroAux.HkIntegrand_gam_mono hα0 hα1 k _ hθ
  have hfg : ∀ z θ : ℝ, 1 < z → Work.FTS.StrongEps.bump z θ = 0 := by
    intro z θ hz
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    exact Or.inr (Or.inl (le_of_lt hz))
  have hsq := Work.Spaces.HkSq_le_of_bound α k Work.FTS.StrongEps.bump 1 M
    (by norm_num) hMnn hfg hbound
  rw [Work.Spaces.HkNorm]
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_max_right _ _)

end Work.FTS.EpsEngine
