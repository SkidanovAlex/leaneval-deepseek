import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.Cyl
open Work.CoreResiduals.VorticityEquation

namespace Work.R1G

/-- **The pointwise identity behind the deficit scalar reduction.**  For a no-swirl axisymmetric
velocity `u = cylField (· · t) (· · t)` and a swirl vorticity `ω = W(radial ·, axial ·, t)·eTheta`,
the `ℝ³` vorticity-equation residual is *exactly* a function of `(radial x, axial x, t)` times
`eTheta x`:
`∂ₜω + (u·∇)ω - (ω·∇)u = (∂ₜW + u_r ∂_rW + u_z ∂_zW - (u_r/r)W) • eTheta`.
This is the "deficit" refinement of `vorticityEquation_cylField_iff_scalar` (its `= 0` case): it
gives the dictionary for an arbitrary deficit `Def = WD(radial ·, axial ·, t)·eTheta`.  It holds
unconditionally on the axis (where both sides vanish because `eTheta = 0`), so no side condition on
`radial x` is needed.

*Proof sketch.*  Off the axis (`0 < radial x`) rewrite with the three existing lemmas
`Work.CoreResiduals.VorticityEquation.timeDeriv_swirl`,
`...directionalDeriv_swirl_cylField` (uses `hW`) and `...directionalDeriv_cylField_swirl` (uses
`hu`), then `rw [← add_smul, ← sub_smul]` (or `← add_smul` twice) and `ring`.  On the axis
(`radial x = 0`) mimic the axis block of `vorticityEquation_cylField_iff_scalar`:
`Work.CoreResiduals.VorticityEquation.fderiv_apply_eZ_eq_zero`, `radial_add_smul_eZ`,
`cartesian_prod`, `ext_coord`, and finish with `simp`. -/
theorem vecResid_eq_scalar_smul {ur uz W : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hu : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => ur r z t) r z ∧ Work.Cyl.DiffAt2 (fun r z => uz r z t) r z)
    (x : Work.Cyl.R3) (t : ℝ) :
    FiniteTimeSingularity.timeDeriv
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
      + FiniteTimeSingularity.directionalDeriv
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
          (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t
      = FiniteTimeSingularity.directionalDeriv
          (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + (deriv (fun s : ℝ => W (Work.Cyl.radial x) (Work.Cyl.axial x) s) t
            + ur (Work.Cyl.radial x) (Work.Cyl.axial x) t
                * Work.Cyl.pdR (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x)
            + uz (Work.Cyl.radial x) (Work.Cyl.axial x) t
                * Work.Cyl.pdZ (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x)
            - (ur (Work.Cyl.radial x) (Work.Cyl.axial x) t / Work.Cyl.radial x)
                * W (Work.Cyl.radial x) (Work.Cyl.axial x) t) • Work.Cyl.eTheta x := by
  by_cases hr : 0 < radial x
  · rw [timeDeriv_swirl (W := W) x t,
        directionalDeriv_swirl_cylField (W := W) hW x t hr,
        directionalDeriv_cylField_swirl (W := W) hu x t hr]
    rw [← add_smul, ← add_smul]
    congr 1
    ring
  · have hr0 : radial x = 0 := le_antisymm (not_lt.mp hr) (radial_nonneg x)
    have hx01 : x 0 = 0 ∧ x 1 = 0 := (radial_eq_zero_iff x).mp hr0
    have hradVec : radialVec x = 0 := by
      apply ext_coord <;> simp [radialVec, hx01.1, hx01.2]
    have he0 : eTheta x = 0 := by simp [eTheta, hr0]
    have hu0 : cylField (fun r z => ur r z t) (fun r z => uz r z t) x
        = uz (radial x) (axial x) t • eZ := by
      show (ur (radial x) (axial x) t / radial x) • radialVec x
          + uz (radial x) (axial x) t • eZ = _
      rw [hradVec, smul_zero, zero_add]
    have hT1 : FiniteTimeSingularity.timeDeriv
        (fun x t => W (radial x) (axial x) t • eTheta x) x t = 0 := by
      rw [timeDeriv_swirl (W := W) x t, he0, smul_zero]
    have hT2 : FiniteTimeSingularity.directionalDeriv
        (fun x t => W (radial x) (axial x) t • eTheta x)
        (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t = 0 := by
      rw [FiniteTimeSingularity.directionalDeriv]
      rw [hu0, map_smul]
      have hz : (fderiv ℝ (fun y : R3 => W (radial y) (axial y) t • eTheta y) x) eZ = 0 :=
        fderiv_apply_eZ_eq_zero (F := fun y : R3 => W (radial y) (axial y) t • eTheta y)
          (by intro s
              have hrs : radial (x + s • eZ) = 0 := by rw [radial_add_smul_eZ, hr0]
              simp [eTheta, hrs])
      rw [hz, smul_zero]
    have hT3 : FiniteTimeSingularity.directionalDeriv
        (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
        (fun x t => W (radial x) (axial x) t • eTheta x) x t = 0 := by
      rw [FiniteTimeSingularity.directionalDeriv]
      have h0 : W (radial x) (axial x) t • eTheta x = 0 := by rw [he0, smul_zero]
      rw [h0]; simp
    rw [hT1, hT2, hT3]
    simp [he0]

end Work.R1G
