import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS.PressureOn.secondDerivTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_nonneg_of_max` (leaf E4a of the SB2/SB5 plan)

The coordinatewise maximum principle for the ground-state-transformed operator

`Lgs α u = -(α²) ∂_z²u - 5α ∂_z u - ∂_θ²u - (4cos 2θ / sin 2θ - tan θ) ∂_θu`
(here `DzIter 2 u = z ∂_z u + z² ∂_z²u`, since `D_z = z ∂_z`),

in the form used in the SB5 comparison argument: if `v` is `C²` at an interior point `(z₀,θ₀)` of
the quadrant which is a local maximum of both one-dimensional slices, then `0 ≤ Lgs α v z₀ θ₀`.

The pointwise proof is the classical Fermat argument: at a local maximum each first partial
vanishes and each pure second partial is `≤ 0`; the second-order fact
`Work.FTS.PressureOn.secondDerivTest` supplies `∂_z²v ≤ 0`, `∂_θ²v ≤ 0`, hence every term of
`Lgs α v z₀ θ₀` is `≥ 0` independently of the sign (or vanishing) of `α`.
-/

namespace Work.FTS_StreamBdry.SB25

/-- The operator `DzIter 2 = D_z ∘ D_z` evaluated at a point, in terms of the `z`-slice and its
first two derivatives: `DzIter 2 v z θ = z ∂_zv + z² ∂_z²v`.

The only hypothesis is the differentiability at `z` of `∂_zv(·,θ)`, which is exactly what the
product rule for `z ↦ z · ∂_zv(z,θ)` needs. -/
lemma dzIter_two_eq (v : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : DifferentiableAt ℝ (fun z' => deriv (fun z'' => v z'' θ) z') z) :
    Work.Spaces.DzIter 2 v z θ
      = z * deriv (fun z' => v z' θ) z + z ^ 2 * deriv (deriv (fun z' => v z' θ)) z := by
  have hd : HasDerivAt (fun z' => deriv (fun z'' => v z'' θ) z')
      (deriv (deriv (fun z' => v z' θ)) z) z := h.hasDerivAt
  have hp : HasDerivAt (fun z' => z' * deriv (fun z'' => v z'' θ) z')
      (deriv (fun z' => v z' θ) z + z * deriv (deriv (fun z' => v z' θ)) z) z := by
    have h1 : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
    have h2 := h1.mul hd
    have hc : (fun x : ℝ => x) * (fun z' => deriv (fun z'' => v z'' θ) z')
        = (fun z' => z' * deriv (fun z'' => v z'' θ) z') := by
      funext x; rfl
    rw [hc] at h2
    simpa using h2
  have hfun : Work.Spaces.DzIter 2 v z θ
      = z * deriv (fun z' => z' * deriv (fun z'' => v z'' θ) z') z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  rw [hfun, hp.deriv]
  ring

theorem Lgs_nonneg_of_max (α : ℝ) (v : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.LgsNonnegOfMax α v := by
  intro z0 θ0 hz0 hθ0 hv hmz0 hmθ0
  -- rename the slice variables so that the statements below match syntactically
  have hmz : IsLocalMax (fun z' => v z' θ0) z0 := hmz0
  have hmθ : IsLocalMax (fun θ' => v z0 θ') θ0 := hmθ0
  -- the two slices are `C²` at the maximum point
  have hcz : ContDiffAt ℝ 2 (fun z' => v z' θ0) z0 := by
    have h1 : ContDiffAt ℝ 2 (fun z : ℝ => (z, θ0)) z0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h2 := hv.comp z0 h1
    simpa [Function.comp_def] using h2
  have hct : ContDiffAt ℝ 2 (fun θ' => v z0 θ') θ0 := by
    have h1 : ContDiffAt ℝ 2 (fun θ : ℝ => (z0, θ)) θ0 :=
      contDiffAt_const.prodMk contDiffAt_id
    have h2 := hv.comp θ0 h1
    simpa [Function.comp_def] using h2
  -- Fermat: the first derivatives vanish
  have hdz : deriv (fun z' => v z' θ0) z0 = 0 := hmz.deriv_eq_zero
  have hdt : deriv (fun θ' => v z0 θ') θ0 = 0 := hmθ.deriv_eq_zero
  -- the pure second derivatives are nonpositive at a local maximum
  have hzz : deriv (deriv (fun z' => v z' θ0)) z0 ≤ 0 :=
    Work.FTS.PressureOn.secondDerivTest hmz hcz
  have htt : deriv (deriv (fun θ' => v z0 θ')) θ0 ≤ 0 :=
    Work.FTS.PressureOn.secondDerivTest hmθ hct
  -- the `z`-slice derivative is differentiable at `z0` (needed for the product rule)
  have hdiff : DifferentiableAt ℝ (fun z' => deriv (fun z'' => v z'' θ0) z') z0 :=
    (hcz.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- evaluate the four operators appearing in `Lgs`
  have hDzIter := dzIter_two_eq v z0 θ0 hdiff
  have hDz : Work.Spaces.Dz v z0 θ0 = 0 := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hdz, mul_zero]
  have hpth : Work.Spaces.pth v z0 θ0 = 0 := by
    simpa only [Work.Spaces.pth] using hdt
  have hpthIter : Work.Spaces.pthIter 2 v z0 θ0 = deriv (deriv (fun θ' => v z0 θ')) θ0 := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  -- every term of `Lgs` is nonnegative: `-α² z₀² ∂_z²v ≥ 0`, the first-order terms vanish, and
  -- `-∂_θ²v ≥ 0`.
  simp only [Work.FTS_StreamBdry.SB25.Lgs]
  rw [hDzIter, hDz, hpthIter, hpth, hdz]
  nlinarith [hzz, htt, sq_nonneg (α * z0)]

end Work.FTS_StreamBdry.SB25
