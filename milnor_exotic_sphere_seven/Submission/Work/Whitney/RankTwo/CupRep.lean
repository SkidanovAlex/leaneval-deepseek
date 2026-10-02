import Mathlib
import Submission.Work.Whitney.RankTwo.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney.RankTwo
open Work.Thom
open Work.Cohomology

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-! ## The faces of a `1`-simplex as `0`-simplices -/

theorem map_succAbove0_eq_vertex (z : stdSimplex ℝ (Fin 1)) :
    stdSimplex.map (0 : Fin 2).succAbove z = stdSimplex.vertex (1 : Fin 2) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change (stdSimplex.map (0 : Fin 2).succAbove z) 0 = (stdSimplex.vertex (1 : Fin 2)) 0
    rw [map_succAbove0_zero]
    simp [stdSimplex.vertex]
  · change (stdSimplex.map (0 : Fin 2).succAbove z) 1 = (stdSimplex.vertex (1 : Fin 2)) 1
    rw [map_succAbove0_one]
    simp [stdSimplex.vertex]

theorem map_succAbove1_eq_vertex (z : stdSimplex ℝ (Fin 1)) :
    stdSimplex.map (1 : Fin 2).succAbove z = stdSimplex.vertex (0 : Fin 2) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · change (stdSimplex.map (1 : Fin 2).succAbove z) 0 = (stdSimplex.vertex (0 : Fin 2)) 0
    rw [map_succAbove1_zero]
    simp [stdSimplex.vertex]
  · change (stdSimplex.map (1 : Fin 2).succAbove z) 1 = (stdSimplex.vertex (0 : Fin 2)) 1
    rw [map_succAbove1_one]
    simp [stdSimplex.vertex]

theorem ssX_δ_zero_eq_ptSimp (σ : (ssX Y) _⦋1⦌) :
    (ssX Y).δ 0 σ = ptSimp Y ((sEquiv Y 1) σ (stdSimplex.vertex (1 : Fin 2))) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_ptSimp, ContinuousMap.const_apply, map_succAbove0_eq_vertex]

theorem ssX_δ_one_eq_ptSimp (σ : (ssX Y) _⦋1⦌) :
    (ssX Y).δ 1 σ = ptSimp Y ((sEquiv Y 1) σ (stdSimplex.vertex (0 : Fin 2))) := by
  apply (sEquiv Y 0).injective
  apply ContinuousMap.ext
  intro z
  rw [ssX_δ_apply, sEquiv_ptSimp, ContinuousMap.const_apply, map_succAbove1_eq_vertex]

/-! ## The differential of the sign cochain -/

/-- The differential of `alpha0` on a `1`-simplex is the difference of the signs at the two
endpoints. -/
theorem genEval_alpha_apply (σ : (ssX Y) _⦋1⦌) :
    genEval ℤ (ssX Y) (alpha Y) σ
      = genEval ℤ (ssX Y) (alpha0 Y) ((ssX Y).δ 0 σ)
        - genEval ℤ (ssX Y) (alpha0 Y) ((ssX Y).δ 1 σ) := by
  rw [alpha, cochainDiff_apply]
  exact alpha0_chain Y σ

/-- The value of `alpha = d alpha0` on a `1`-simplex, in terms of the fibre coordinate. -/
theorem genEval_alpha_eq_signs (σ : (ssX Y) _⦋1⦌) :
    genEval ℤ (ssX Y) (alpha Y) σ
      = posOf (coordA Y ((sEquiv Y 1) σ (stdSimplex.vertex (1 : Fin 2))))
        - posOf (coordA Y ((sEquiv Y 1) σ (stdSimplex.vertex (0 : Fin 2)))) := by
  rw [genEval_alpha_apply Y σ, ssX_δ_zero_eq_ptSimp, ssX_δ_one_eq_ptSimp]
  simp only [genEval_alpha0_ptSimp]

theorem genEval_beta_apply (σ : (ssX Y) _⦋1⦌) :
    genEval ℤ (ssX Y) (beta Y) σ
      = genEval ℤ (ssX Y) (beta0 Y) ((ssX Y).δ 0 σ)
        - genEval ℤ (ssX Y) (beta0 Y) ((ssX Y).δ 1 σ) := by
  rw [beta, cochainDiff_apply]
  exact beta0_chain Y σ

theorem genEval_beta_eq_signs (σ : (ssX Y) _⦋1⦌) :
    genEval ℤ (ssX Y) (beta Y) σ
      = posOf (coordB Y ((sEquiv Y 1) σ (stdSimplex.vertex (1 : Fin 2))))
        - posOf (coordB Y ((sEquiv Y 1) σ (stdSimplex.vertex (0 : Fin 2)))) := by
  rw [genEval_beta_apply Y σ, ssX_δ_zero_eq_ptSimp, ssX_δ_one_eq_ptSimp]
  simp only [genEval_beta0_ptSimp]

end
end Work.Whitney.RankTwo
