import Mathlib
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece

/-!
# The linear identification `ℝ ≅ ℝ¹` as a linear equivalence

`Work.Drive.logEucl : ℝ →L ℝ¹` (`Submission/Work/Drive/contMDiffAt_cappingSpace_configPiece.lean`)
is the identification of `ℝ` with the one-dimensional `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, i.e.
`logEucl t = fun _ => t`.  This file records that it is bijective
(`Work.Drive.logEuclEquiv : ℝ ≃L[ℝ] ℝ¹`), which is what allows the identification
`chart(0,∞)-pushed = logEucl ∘ log` of `Work.Drive.eventuallyEq_chartAt_expHomeo` to be transported
across `Work.Drive.TripleTransverseE`
(`Work.Drive.tripleTransverseE_prod_comp_continuousLinearEquiv`).
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

lemma logEucl_apply_coord (t : ℝ) (i : Fin 1) : (Work.Drive.logEucl t) i = t := by
  simp [Work.Drive.logEucl]

theorem logEucl_injective : Function.Injective (Work.Drive.logEucl : ℝ → EuclideanSpace ℝ (Fin 1)) := by
  intro a b hab
  have h := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) hab
  rwa [logEucl_apply_coord, logEucl_apply_coord] at h

theorem logEucl_ker : (Work.Drive.logEucl : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr logEucl_injective

theorem logEucl_surjective : Function.Surjective (Work.Drive.logEucl : ℝ → EuclideanSpace ℝ (Fin 1)) := by
  intro y
  refine ⟨y 0, ?_⟩
  ext i
  fin_cases i
  simp [logEucl_apply_coord]

theorem logEucl_range : (Work.Drive.logEucl : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)).range = ⊤ :=
  LinearMap.range_eq_top.mpr logEucl_surjective

/-- **The identification `ℝ ≅ ℝ¹` as a continuous linear equivalence.** -/
noncomputable def logEuclEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ContinuousLinearEquiv.ofBijective (Work.Drive.logEucl : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))
    logEucl_ker logEucl_range

@[simp] lemma coe_logEuclEquiv :
    ((logEuclEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) = Work.Drive.logEucl := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearEquiv.coe_coe]
  exact congrFun (ContinuousLinearEquiv.coeFn_ofBijective
    (Work.Drive.logEucl : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) logEucl_ker logEucl_range) v

end

end Work.Drive
