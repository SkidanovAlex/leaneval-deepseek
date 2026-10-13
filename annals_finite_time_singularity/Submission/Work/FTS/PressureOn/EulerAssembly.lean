/-
# `Work.FTS.PressureOn.EulerAssembly` — Step 5 of the assembly

This module contains the *algebraic* half of the assembly of `PressureReconstructionOn`
(Steps 4–5 of `NOTES_ASSEMBLY.md`), isolated from all analysis:

* `potOn ω` is the scalar potential `q x t = pressurePotential (lamb (physVel ω) ω · t) x`, so that
  `pressureOn ω x t = -‖u x t‖²/2 - potOn ω x t` (`pressureOn_eq`);
* `spaceGrad_potOn` converts the output of `weyl_pair` (`HasFDerivAt q (innerSL ℝ (Φ x t)) x`,
  where `Φ = ∂_t u - u×ω`) into the statement `∇q = Φ` for `spaceGrad`;
* `spaceGrad_pressureOn` computes `∇p` for `p = pressureOn ω = -‖u‖²/2 - q`;
* `euler_eq_of_gradient` then gives the Euler equation `∂_t u + (u·∇)u + ∇p = 0`, using only the
  vector identity `materialDeriv_eq_gradient_sub_cross`.

No analysis is used here: the two gradient facts are hypotheses.
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.materialDeriv_eq_gradient_sub_cross
import Submission.Work.FTS.Physical.Pressure

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Gradient InnerProductSpace
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- **The scalar potential of the reconstruction**, as a space-time field: the design's `q`,
`q x t = pressurePotential (lamb u ω · t) x` with `u = physVel ω`. -/
noncomputable def potOn (ω : R3 → ℝ → R3) : R3 → ℝ → ℝ :=
  fun x t => pressurePotential (lamb (physVel ω) ω · t) x

/-- `pressureOn ω = -‖u·‖²/2 - q`: the reconstructed pressure in terms of `potOn`. -/
theorem pressureOn_eq (ω : R3 → ℝ → R3) :
    pressureOn ω = fun x t => -(‖physVel ω x t‖ ^ 2 / 2) - potOn ω x t := by
  funext x t
  rw [pressureOn_apply, potOn]
  rfl

/-- The gradient of `-(a) - b`. -/
theorem gradient_neg_sub {a b : R3 → ℝ} {x : R3} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    gradient (fun y => -(a y) - b y) x = -(gradient a x) - gradient b x := by
  apply (toDual ℝ R3).injective
  rw [toDual_gradient, map_sub, map_neg, toDual_gradient, toDual_gradient]
  rw [show (fun y : R3 => -(a y) - b y) = (-a) - b from rfl]
  rw [fderiv_sub ha.neg hb, fderiv_neg]

/-- **From the Weyl step to `spaceGrad`.**  If (`weyl_pair`'s output) the slice of `q` has
`HasFDerivAt` with functional `innerSL ℝ (∂_t u - u×ω)`, then the spatial gradient of `q` is
`∂_t u - u×ω`. -/
theorem spaceGrad_potOn {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    spaceGrad (potOn ω) x t = timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t) := by
  refine Work.FTS.Physical.spaceGrad_eq_of_inner_eq (fun y => ?_)
  have h1 : inner ℝ (spaceGrad (potOn ω) x t) y = fderiv ℝ (potOn ω · t) x y := by
    rw [Work.FTS.Physical.fderiv_eq_innerSL_spaceGrad (potOn ω) x t]
    rfl
  rw [h1, hgq.fderiv]
  rfl

/-- **The spatial gradient of the reconstructed pressure.**  `∇p = -∇(‖u‖²/2) - ∇q`. -/
theorem spaceGrad_pressureOn {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hsq : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
    (hq : DifferentiableAt ℝ (potOn ω · t) x)
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    spaceGrad (pressureOn ω) x t
      = -(gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
        - (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t)) := by
  have hslice : (fun y => pressureOn ω y t)
      = fun y => -(‖physVel ω y t‖ ^ 2 / 2) - potOn ω y t := by
    funext y
    rw [pressureOn_apply, potOn]
    rfl
  have hgrad := gradient_neg_sub (a := fun y => ‖physVel ω y t‖ ^ 2 / 2)
    (b := fun y => potOn ω y t) hsq hq
  have hpot : spaceGrad (potOn ω) x t = gradient (fun y => potOn ω y t) x := rfl
  rw [spaceGrad, hslice, hgrad, ← hpot]
  exact congrArg (fun v => -(gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x) - v)
    (spaceGrad_potOn hgq)

/-- **Step 5: the Euler equation for the reconstructed pressure.**  Given the pointwise vector
identity for `u = physVel ω` (from `C¹` in space), the gradient identity `∇q = ∂_t u - u×ω`
(Step 4, i.e. `weyl_pair` for the pair `(q, ∂_t u - u×ω)`) and the differentiability of the two
pieces, the pressure `p = pressureOn ω` satisfies `∂_t u + (u·∇)u + ∇p = 0`. -/
theorem euler_eq_of_gradient {ω : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hu : HasFDerivAt (fun y => physVel ω y t)
      (fderiv ℝ (fun y => physVel ω y t) x) x)
    (hcurl : ∀ z, vorticity (fun y => physVel ω y t) z = ω z t)
    (hsq : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2 / 2) x)
    (hq : DifferentiableAt ℝ (potOn ω · t) x)
    (hgq : HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x) :
    timeDeriv (physVel ω) x t + directionalDeriv (physVel ω) (physVel ω) x t
      + spaceGrad (pressureOn ω) x t = 0 := by
  have hp := spaceGrad_pressureOn hsq hq hgq
  have hmv := materialDeriv_eq_gradient_sub_cross hu
  rw [hcurl x] at hmv
  -- hmv : fderiv u x (u x) = ∇(‖u‖²/2) x - u×ω
  have hsq' : gradient (fun y => ‖physVel ω y t‖ ^ 2 / 2) x
      = fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
        + crossVec (physVel ω x t) (ω x t) := sub_eq_iff_eq_add.mp hmv.symm
  rw [hp, hsq']
  show timeDeriv (physVel ω) x t + fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
      + (-(fderiv ℝ (fun y => physVel ω y t) x (physVel ω x t)
            + crossVec (physVel ω x t) (ω x t))
          - (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) = 0
  abel

end Work.FTS.PressureOn
