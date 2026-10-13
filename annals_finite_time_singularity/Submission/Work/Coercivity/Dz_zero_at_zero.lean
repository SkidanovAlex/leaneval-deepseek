/-
Copyright: work module for the Elgindi finite-time singularity project.

# `∂_z f(0,θ) = 0` from the boundary condition `z (D_z f · w)² → 0`

If `f` is smooth on a neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and,
for some angle `θ ∈ [0,π/2]`, the boundary quantity

  `z · (D_z f(z,θ) · w(z))²`,   `D_z f = z ∂_z f`,  `w(z) = (1+z)²/z²`,

tends to `0` as `z → 0⁺`, then the radial derivative of the slice vanishes at the
origin: `∂_z f(0,θ) = 0`.

The proof is the algebraic identity `Work.Coercivity.zw_sq_factor` of `Dz_alg`,

  `z (D_z f z θ · w z)² = (∂_z f z θ)² (1+z)^4 / z`   `(z ≠ 0)`,

which turns the boundary condition into `(∂_z f z θ)² (1+z)^4 / z → 0`.  Multiplying
by the (continuous, vanishing at `0`) factor `z/(1+z)^4` shows `(∂_z f z θ)² → 0`, hence
`|∂_z f z θ| = √((∂_z f z θ)²) → 0`; the value at `z = 0` follows from the continuity on
`(-1,∞)` of the derivative of the slice (`Spaces.hardyZ_continuousOn_pz_slice`) by
uniqueness of limits along the non-trivial filter `𝓝[>] 0`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Dz_alg
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set

namespace Work.Coercivity

set_option autoImplicit false

/-- **Vanishing of the radial derivative at the origin.**  For a function `f` smooth on a
neighbourhood of the closed quadrant whose boundary quantity `z (D_z f · w)²` tends to `0`
at `0⁺`, the radial derivative of the slice `z ↦ f z θ` vanishes at `z = 0`. -/
theorem Dz_zero_at_zero (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0 := by
  intro θ hθ
  have hself : Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
  -- Step 1: rewrite the hypothesis using `zw_sq_factor`.
  have heq1 : (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z) := by
    filter_upwards [hself] with z hz
    exact zw_sq_factor f (by simp only [Set.mem_Ioi] at hz; linarith)
  have h1 : Filter.Tendsto (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := (hbd θ hθ).congr' heq1
  -- The auxiliary factor `z/(1+z)^4` is continuous at `0` with value `0`.
  have hzcont : Filter.Tendsto (fun z : ℝ => z / (1 + z) ^ 4)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℝ => z / (1 + z) ^ 4) 0 :=
      continuousAt_id.div (by fun_prop) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  -- Step 2: multiply back to recover `(∂_z f ·)²`.
  have heq2 : (fun z => (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z * (z / (1 + z) ^ 4))
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)] (fun z => (Spaces.pz f z θ) ^ 2) := by
    filter_upwards [hself] with z hz
    have hz0 : z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
    have h1z : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 (by simp only [Set.mem_Ioi] at hz; linarith)
    have h1z' : 1 + z ≠ 0 := by simp only [Set.mem_Ioi] at hz; linarith
    field_simp
  have h2 : Filter.Tendsto (fun z => (Spaces.pz f z θ) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (h1.mul hzcont).congr' heq2
  -- Step 3: take square roots: `|∂_z f| → 0`.
  have h3 : Filter.Tendsto (fun z => Real.sqrt ((Spaces.pz f z θ) ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp h2
  have h4 : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using h3
  -- Step 4: continuity of the slice derivative at `0` identifies the limit.
  have hcont : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi (-1))) (nhds (Spaces.pz f 0 θ)) :=
    (Spaces.hardyZ_continuousOn_pz_slice f hsm hθ).continuousWithinAt (by simp)
  have hcont' : Filter.Tendsto (fun z => Spaces.pz f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Spaces.pz f 0 θ)) :=
    hcont.mono_left (nhdsWithin_mono 0 (fun z hz => by
      simp only [Set.mem_Ioi] at hz ⊢; linarith))
  have hnb : (nhdsWithin (0:ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique hcont' h4

end Work.Coercivity
