/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second difference quotient tends to `D_z (D_z ·)`

Two pieces:

* `dq_dq_apply`: the unfolded form `dq c (dq c f) z θ = (f (c²z) θ - 2 f (c z) θ + f z θ)/(c-1)²`
  (an identity valid for every real `c`, both sides being `0` at `c = 1`);
* `tendsto_dqq_DzDz`: for `g` of class `C^∞` on the open quadrant and `(z,θ)` in it,
  `dq c (dq c g) z θ ⟶ D_z (D_z g) z θ` as `c → 1⁺` — the convergence hypothesis of the Fatou
  step for the second difference-quotient datum.  It is `SecondDiffQuot` (`C²` Taylor at the
  point `z > 0` of the `θ`-slice) combined with the slot identity
  `D_z (D_z g) = z ∂_z g + z² ∂_z² g`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilSlots
import Submission.Work.FTS.EllipticEst.Cores.Dil.SecondDiffQuot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem dq_dq_apply (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    dq c (dq c f) z θ = (f (c ^ 2 * z) θ - 2 * f (c * z) θ + f z θ) / (c - 1) ^ 2 := by
  by_cases hc : c = 1
  · subst hc
    simp [dq_apply]
  · have hne : c - 1 ≠ 0 := sub_ne_zero.mpr hc
    simp only [dq_apply]
    field_simp
    ring

/-- `dq c` only sees the values of its argument on `Ioi 0` (both evaluation points are
positive when `c > 0` and `z > 0`). -/
theorem dq_congr_of_pos {c : ℝ} {f g : ℝ → ℝ → ℝ} (hc : 0 < c) {θ : ℝ}
    (h : ∀ y : ℝ, 0 < y → f y θ = g y θ) {z : ℝ} (hz : 0 < z) :
    dq c f z θ = dq c g z θ := by
  simp only [dq_apply, h (c * z) (by positivity), h z hz]

theorem tendsto_dqq_DzDz {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (fun c : ℝ => dq c (dq c g) z θ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Work.Spaces.Dz (Work.Spaces.Dz g) z θ)) := by
  have hcurry : ContDiffOn ℝ 2 (fun y : ℝ => g y θ) (Set.Ioi 0) :=
    (hg.curry_z hθ).of_le (by norm_num)
  have hmain := SecondDiffQuot hz hcurry
  have hlim : z * deriv (fun y : ℝ => g y θ) z + z ^ 2 * deriv (deriv (fun y : ℝ => g y θ)) z
      = Work.Spaces.Dz (Work.Spaces.Dz g) z θ := by
    have h1 : deriv (fun y : ℝ => g y θ) z = Work.Spaces.pz g z θ := rfl
    have h2 : deriv (deriv (fun y : ℝ => g y θ)) z = Work.Spaces.pzIter 2 g z θ := rfl
    rw [h1, h2, Work.Spaces.Dz]
    rw [pz_Dz_eq hg z θ hz hθ]
    ring
  have hgoal : Filter.Tendsto
      (fun c : ℝ => (g (c ^ 2 * z) θ - 2 * g (c * z) θ + g z θ) / (c - 1) ^ 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.Dz (Work.Spaces.Dz g) z θ)) := by
    rw [← hlim]
    exact hmain
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun c => (dq_dq_apply c g z θ).symm) hgoal

end Work.FTS.EllipticEst.Cores.Dil
