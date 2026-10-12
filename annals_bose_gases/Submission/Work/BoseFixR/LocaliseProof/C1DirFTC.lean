import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.acube_axis_ftoc_c1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The whole-space directional fundamental theorem of calculus, `C¹` version

For a `C¹` map `g : ℝ³ → ℝ` with compact support and a coordinate direction `kcStdBasis j`,

    ∫_{ℝ³} ∂_j g = 0.

This is the `C¹` refinement of `Work.BSKinetic.integral_fderiv_kcStdBasis_eq_zero` (which
assumes `ContDiff ℝ ∞`).  The proof is the same: choose a centred cube `acube s` strictly
containing the support of `g`, apply the axis fundamental theorem of calculus on the cube
(`Work.SmallBoxA0.acube_axis_ftoc_c1`, `C¹` version), and note that both the integrand and the
boundary face contributions vanish outside the cube.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases

namespace Work.BoseFixR.LocaliseProof

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The divergence / fundamental-theorem identity on `ℝ³` (`C¹` version).**  For a `C¹`
compactly supported `g : ℝ³ → ℝ` and any coordinate direction `kcStdBasis j`, the integral of
the partial derivative vanishes: `∫_{ℝ³} ∂_j g = 0`. -/
theorem integral_fderiv_kcStdBasis_eq_zero {g : ℝ³ → ℝ}
    (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (j : Fin 3) :
    ∫ x : ℝ³, fderiv ℝ g x (kcStdBasis j) = 0 := by
  obtain ⟨r, hr⟩ := (show Bornology.IsBounded (tsupport g) from
    (show IsCompact (tsupport g) from hcs).isBounded).subset_closedBall (0 : ℝ³)
  have hr' : ∀ x ∈ tsupport g, ‖x‖ ≤ r := by
    intro x hx
    have h := hr hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  set s : ℝ := 2 * (max r 0 + 1) with hsdef
  have hs : 0 < s := by
    rw [hsdef]; have := le_max_right r (0 : ℝ); linarith
  have hs2 : 0 < s / 2 := by linarith
  have hrs : r < s / 2 := by
    rw [hsdef]; have := le_max_left r (0 : ℝ); linarith
  have face : ∀ z ∈ acube s, z j = s / 2 → g z = 0 := by
    intro z _ hzj
    have hnot : z ∉ tsupport g := by
      intro hzts
      have h1 : ‖z‖ ≤ r := hr' z hzts
      have h2 : s / 2 ≤ ‖z‖ := by
        have h3 : ‖z j‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
        have h4 : ‖z j‖ = s / 2 := by rw [hzj, Real.norm_eq_abs, abs_of_pos hs2]
        linarith
      linarith
    exact Function.notMem_support.mp (fun hmem => hnot (subset_tsupport g hmem))
  have face' : ∀ z ∈ acube s, z j = -(s / 2) → g z = 0 := by
    intro z _ hzj
    have hnot : z ∉ tsupport g := by
      intro hzts
      have h1 : ‖z‖ ≤ r := hr' z hzts
      have h2 : s / 2 ≤ ‖z‖ := by
        have h3 : ‖z j‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
        have h4 : ‖z j‖ = s / 2 := by rw [hzj, Real.norm_eq_abs, abs_neg, abs_of_pos hs2]
        linarith
      linarith
    exact Function.notMem_support.mp (fun hmem => hnot (subset_tsupport g hmem))
  have hcube : ∫ z in acube s, fderiv ℝ g z (kcStdBasis j) = 0 :=
    Work.SmallBoxA0.acube_axis_ftoc_c1 hs j hg face face'
  have hsub : tsupport g ⊆ acube s := by
    intro x hx
    have hxr : ‖x‖ ≤ r := hr' x hx
    have hxs : ‖x‖ < s / 2 := lt_of_le_of_lt hxr hrs
    intro m
    have h3 : ‖x m‖ ≤ ‖x‖ := PiLp.norm_apply_le x m
    rw [Real.norm_eq_abs] at h3
    rw [Set.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.mp (le_trans h3 (le_of_lt hxs))
    exact ⟨by linarith, h2⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := acube s)
      (f := fun z : ℝ³ => fderiv ℝ g z (kcStdBasis j)) (fun z hz => by
        have hzts : z ∉ tsupport g := fun h => hz (hsub h)
        rw [fderiv_of_notMem_tsupport ℝ hzts]
        simp)] at hcube
  exact hcube

end Work.BoseFixR.LocaliseProof
