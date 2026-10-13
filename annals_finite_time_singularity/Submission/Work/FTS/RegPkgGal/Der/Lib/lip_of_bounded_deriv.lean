import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.FTS.RegPkgGal.Der.Lib

/-- **Mean-value bound on the half line.**  If `f` is differentiable on `(0, ∞)` with
`|deriv f| ≤ M` there and is continuous at `0`, then `f` is `M`-Lipschitz on `[0, ∞)`.

The proof is the mean value theorem on `[a, b]` for `0 < a`, together with an
`ε → 0⁺` limit argument on `[ε, b]` in the case `a = 0`, where differentiability at the
endpoint `0` is replaced by continuity there. -/
theorem lip_of_bounded_deriv {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ f x)
    (hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |deriv f x| ≤ M)
    (hcont : ContinuousAt f 0) :
    ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → |f z - f z'| ≤ M * |z - z'| := by
  have hderivAt : ∀ x : ℝ, 0 < x → HasDerivAt f (deriv f x) x :=
    fun x hx => (hdiff x hx).hasDerivAt
  have hbound : ∀ x : ℝ, 0 < x → ‖deriv f x‖ ≤ M :=
    fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |f a - f b| ≤ M * |a - b| := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with hab' | hlt
    · subst hab'; simp
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`: apply the mean value theorem on `[ε, b]` and let `ε → 0⁺`.
      subst ha0
      have hb : 0 < b := hlt
      have h1 : Filter.Tendsto (fun ε : ℝ => |f ε - f b|) (𝓝[Set.Ioi 0] 0)
          (𝓝 (|f 0 - f b|)) :=
        (((ContinuousAt.tendsto hcont).mono_left nhdsWithin_le_nhds).sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => f b) (𝓝[Set.Ioi 0] 0) (𝓝 (f b)))).abs
      have h2 : Filter.Tendsto (fun ε : ℝ => M * (b - ε)) (𝓝[Set.Ioi 0] 0) (𝓝 (M * b)) := by
        have hb' : Filter.Tendsto (fun ε : ℝ => b - ε) (𝓝[Set.Ioi 0] 0) (𝓝 (b - 0)) := by
          simpa using Filter.Tendsto.sub
            (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => b) (𝓝[Set.Ioi 0] 0) (𝓝 b))
            (Filter.tendsto_id.mono_left nhdsWithin_le_nhds :
              Filter.Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi 0] 0) (𝓝 (0 : ℝ)))
        simpa using Filter.Tendsto.const_mul M hb'
      have h3 : ∀ᶠ ε in 𝓝[Set.Ioi 0] 0, |f ε - f b| ≤ M * (b - ε) := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
        have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := ε) (b := b)
          (f' := fun x => deriv f x) (C := M)
          (fun x hx => (hderivAt x (lt_of_lt_of_le hε hx.1)).hasDerivWithinAt)
          (fun x hx => hbound x (lt_of_lt_of_le hε hx.1))
          b (right_mem_Icc.mpr hεb.le)
        simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt
      have h4 := le_of_tendsto_of_tendsto h1 h2 h3
      simpa [abs_of_pos hb] using h4
    · -- `0 < a`: the mean value theorem on `[a, b]`.
      have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := a) (b := b)
        (f' := fun x => deriv f x) (C := M)
        (fun x hx => (hderivAt x (lt_of_lt_of_le hapos hx.1)).hasDerivWithinAt)
        (fun x hx => hbound x (lt_of_lt_of_le hapos hx.1))
        b (right_mem_Icc.mpr hab)
      rw [Real.norm_eq_abs] at hmvt
      have hgoal : M * |a - b| = M * (b - a) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
      rw [hgoal, abs_sub_comm (f a) (f b)]
      exact hmvt
  intro z z' hz hz'
  rcases le_total z z' with h | h
  · exact key z z' hz h
  · have hh := key z' z hz' h
    rw [abs_sub_comm (f z) (f z'), abs_sub_comm z z']
    exact hh

end Work.FTS.RegPkgGal.Der.Lib
