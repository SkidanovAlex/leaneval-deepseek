import Mathlib
import Submission.Work.Drive.linearPlaneChart

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-!
# The standard plane `linStd` of the disk model is `3`-dimensional

`linStd = span ℝ (Set.range linVecC)` is the span of the sphere lift
`linVecC z = (z, 1 - ‖z‖²) ∈ ℂ² ≅ ℝ⁴`.  This file identifies it with the coordinate hyperplane
`{v : v 3 = 0}` and computes its dimension, which is the `finrank` hypothesis of
`Work.Drive.projective_planes_meet_oddly` for the planes `Work.Drive.linSub φ = φ(linStd)` of
`Work.Drive.linPlaneChart`.

The three vectors `linVecC 1 = e₀`, `linVecC Complex.I = e₁`, `linVecC 0 = e₂` are the standard
basis vectors of the hyperplane, so `linStd = {v : v 3 = 0} = ker (v ↦ v 3)`; the coordinate
functional `v ↦ v 3` is nonzero, so `Module.Dual.finrank_ker_add_one_of_ne_zero` and
`finrank ℝ (Eucl 3) = 4` give the answer.
-/

/-- The coordinate functional `v ↦ v 3` of `Eucl 3 = ℝ⁴ ≅ ℂ²`. -/
def linStdCoord : Eucl 3 →ₗ[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 3).toLinearMap

@[simp] lemma linStdCoord_apply (v : Eucl 3) : linStdCoord v = v 3 := rfl

/-- The coordinate functional `v ↦ v 3` is nonzero (it is `1` on the third basis vector). -/
lemma linStdCoord_ne_zero : linStdCoord ≠ 0 := by
  intro h
  have := congrArg (fun g : Eucl 3 →ₗ[ℝ] ℝ => g (PiLp.single 2 (3 : Fin 4) 1)) h
  simp at this

/-- Every lift `linVecC z = (z, 1 - ‖z‖²)` has vanishing last real coordinate, i.e. lies in the
hyperplane `{v : v 3 = 0}`. -/
lemma linVecC_apply_three (z : ℂ) : (linVecC z) 3 = 0 := by
  rw [linVecC, ofComplex, Complex.ofReal_im]; rfl

/-- Any vector of the hyperplane `{v : v 3 = 0}` is a linear combination of
`linVecC 1 = e₀`, `linVecC Complex.I = e₁` and `linVecC 0 = e₂`. -/
lemma eq_smul_linVecC (v : Eucl 3) (hv : v 3 = 0) :
    v = (v 0) • linVecC 1 + (v 1) • linVecC Complex.I + (v 2) • linVecC 0 := by
  ext i
  fin_cases i <;> simp [linVecC, ofComplex, hv]

/-- **The sharper identification**: the standard plane is the hyperplane `{v : v 3 = 0}`, i.e. the
kernel of the coordinate functional `v ↦ v 3`. -/
theorem linStd_eq_ker_coord : linStd = LinearMap.ker linStdCoord := by
  refine le_antisymm ?_ ?_
  · rw [linStd]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨z, rfl⟩
    show linStdCoord (linVecC z) = 0
    rw [linStdCoord_apply]
    exact linVecC_apply_three z
  · intro v hv
    have hv3 : v 3 = 0 := hv
    rw [eq_smul_linVecC v hv3]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (linVecC_mem_linStd 1))
        (Submodule.smul_mem _ _ (linVecC_mem_linStd Complex.I)))
      (Submodule.smul_mem _ _ (linVecC_mem_linStd 0))

/-- **The standard plane of the disk model is `3`-dimensional**: `linStd = span {z ↦ (z, 1-‖z‖²)}` is
the hyperplane `{v : v 3 = 0}` of `ℂ² ≅ ℝ⁴`, hence a projective plane of `ℝP³`
(`Work.Drive.projLine Work.Drive.linStd`).  This is the `finrank` hypothesis of
`Work.Drive.projective_planes_meet_oddly` for the planes built by
`Work.Drive.linPlaneChart` (`Submission/Work/Drive/linearPlaneChart.lean`).  (It may be useful to prove
along the way the sharper identification `Work.Drive.linStd = LinearMap.ker (fun v : Work.Drive.Eucl 3
=> v 3)`.) -/
theorem linStd_finrank : Module.finrank ℝ Work.Drive.linStd = 3 := by
  have hrk := Module.Dual.finrank_ker_add_one_of_ne_zero (f := linStdCoord) linStdCoord_ne_zero
  rw [linStd_eq_ker_coord]
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
  omega

end

end Work.Drive
