/-
# Standard form of a complex structure on `ℂ`

Every real-linear complex structure `K` on `ℂ` (`K ∘ K = -1`) is *standard*: there is a
real-linear isomorphism `S : ℂ ≃L[ℝ] ℂ` conjugating `K` to multiplication by `i`,
`S (K v) = i * S v`.  This is the `n = 1` case of `Work.Complex.standardForm`, transported from
`E 1 = ℝ²` to `ℂ` along the isometry `eC`.
-/
import Mathlib
import Submission.Work.Core.Defs
import Submission.Work.Complex.standardForm
import Submission.Work.Beltrami.Transfer

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission

noncomputable section

/-- `zF` as an `ℝ`-linear continuous equivalence `F 1 ≃L[ℝ] ℂ`. -/
def zFR : F 1 ≃L[ℝ] ℂ :=
  ((zF : F 1 ≃ₗ[ℂ] ℂ).restrictScalars ℝ).toContinuousLinearEquiv

theorem zFR_apply (x : F 1) : zFR x = zF x := by
  show (((zF : F 1 ≃ₗ[ℂ] ℂ).restrictScalars ℝ) : F 1 → ℂ) x = zF x
  rw [LinearEquiv.restrictScalars_apply]
  rfl

/-- `zFR` is complex linear, i.e. it intertwines the standard structures on `F 1` and `ℂ`. -/
theorem zFR_smul_I (y : F 1) : zFR (Complex.I • y) = Complex.I * zFR y := by
  show (((zF : F 1 ≃ₗ[ℂ] ℂ).restrictScalars ℝ) : F 1 → ℂ) (Complex.I • y)
      = Complex.I * (((zF : F 1 ≃ₗ[ℂ] ℂ).restrictScalars ℝ) : F 1 → ℂ) y
  rw [LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply]
  change (zF : F 1 →L[ℂ] ℂ) (Complex.I • y) = Complex.I * (zF : F 1 →L[ℂ] ℂ) y
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-- **Standard form of a complex structure on `ℂ`.**  For any `K : ℂ →L[ℝ] ℂ` with
`K (K v) = -v` there is `S : ℂ ≃L[ℝ] ℂ` with `S (K v) = i * S v` for all `v`. -/
theorem standardFormC (K : ℂ →L[ℝ] ℂ) (hK : ∀ v : ℂ, K (K v) = -v) :
    ∃ S : ℂ ≃L[ℝ] ℂ, ∀ v : ℂ, S (K v) = Complex.I * S v := by
  set K' : E 1 →L[ℝ] E 1 :=
    (eC.symm : ℂ →L[ℝ] E 1).comp (K.comp (eC : E 1 →L[ℝ] ℂ)) with hK'def
  have hK'2 : ∀ v : E 1, K' (K' v) = -v := by
    intro v
    simp only [hK'def]
    simp [hK]
  obtain ⟨T, hT⟩ := Work.Complex.standardForm (n := 1) K' hK'2
  refine ⟨eC.symm.trans (T.trans zFR), ?_⟩
  intro v
  have hv : eC.symm (K v) = K' (eC.symm v) := by
    simp only [hK'def]
    simp
  have hfun : ∀ u : ℂ, (eC.symm.trans (T.trans zFR)) u = zFR (T (eC.symm u)) := by
    intro u
    rw [ContinuousLinearEquiv.trans_apply]
    rfl
  rw [hfun (K v), hfun v, hv, hT (eC.symm v), zFR_smul_I]

end

end Work.Beltrami
