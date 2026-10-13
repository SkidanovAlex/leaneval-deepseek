/-
Copyright: work module for the Elgindi finite-time singularity project.

# The difference quotient tends to the radial derivative

For `g` of class `C^∞` on the open quadrant, `z > 0` and `θ ∈ (0,π/2)`,

  `dq c g z θ = (g (c z) θ - g z θ)/(c-1)  ⟶  D_z g z θ = z ∂_z g z θ`   as `c → 1⁺`,

which is the convergence hypothesis of the Fatou step (`HkSq_zero_le_liminf`) that passes the
level-`0` estimate for the difference-quotient data to the radially differentiated data.

Proof: for `c ≠ 1`, `dq c g z θ = z * slope (g · θ) z (c z)`, and `HasDerivAt.tendsto_slope`
sends the slope to `∂_z g z θ` along `𝓝[≠] z`; since `c ↦ c z` maps `nhdsWithin 1 (Ioi 1)` to
`𝓝[≠] z` (as `z ≠ 0`), the conclusion follows.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic

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

theorem tendsto_dq_Dz {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (fun c : ℝ => dq c g z θ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Work.Spaces.Dz g z θ)) := by
  have hslope : Filter.Tendsto (fun y : ℝ => (y - z)⁻¹ * (g y θ - g z θ))
      (nhdsWithin z {z}ᶜ) (nhds (Work.Spaces.pz g z θ)) := by
    have h := (hg.hasDerivAt_slice hθ hz).tendsto_slope
    have hfun : slope (fun z' : ℝ => g z' θ) z
        = fun y : ℝ => (y - z)⁻¹ * (g y θ - g z θ) := by
      funext y
      rw [slope_def_module]
      simp [smul_eq_mul]
    rwa [hfun] at h
  have hmap : Filter.Tendsto (fun c : ℝ => c * z) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin z {z}ᶜ) := by
    rw [nhdsWithin, nhdsWithin, Filter.tendsto_inf]
    refine ⟨?_, ?_⟩
    · have hcont : Filter.Tendsto (fun c : ℝ => c * z) (nhds 1) (nhds (1 * z)) :=
        (continuousAt_id.mul continuousAt_const).tendsto
      simpa using hcont.mono_left inf_le_left
    · rw [Filter.tendsto_principal]
      filter_upwards [self_mem_nhdsWithin] with c hc
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hceq
      have h1 : c * z = 1 * z := by rw [hceq, one_mul]
      have hc1 : c = 1 := mul_right_cancel₀ (ne_of_gt hz) h1
      exact absurd hc1 (ne_of_gt hc)
  have hcomp : Filter.Tendsto (fun c : ℝ => (c * z - z)⁻¹ * (g (c * z) θ - g z θ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.pz g z θ)) :=
    hslope.comp hmap
  have hmul : Filter.Tendsto (fun c : ℝ => z * ((c * z - z)⁻¹ * (g (c * z) θ - g z θ)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (z * Work.Spaces.pz g z θ)) :=
    tendsto_const_nhds.mul hcomp
  have hev : (fun c : ℝ => z * ((c * z - z)⁻¹ * (g (c * z) θ - g z θ)))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun c : ℝ => dq c g z θ) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [dq_apply]
    have hcgt : (1 : ℝ) < c := hc
    have hc1 : c - 1 ≠ 0 := ne_of_gt (by linarith : 0 < c - 1)
    have hz1 : z ≠ 0 := ne_of_gt hz
    field_simp
  have hgoal : Filter.Tendsto (fun c : ℝ => z * ((c * z - z)⁻¹ * (g (c * z) θ - g z θ)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.Dz g z θ)) := by
    simpa only [Work.Spaces.Dz] using hmul
  exact Filter.Tendsto.congr' hev hgoal

end Work.FTS.EllipticEst.Cores.Dil
