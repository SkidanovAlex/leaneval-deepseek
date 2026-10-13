import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Linear vanishing of `u` at the right endpoint.**  If `u` is `C¹` on `(0, π/2)` with
`|u'| ≤ M` there, and `u → 0` as `θ → (π/2)⁻`, then `|u θ| ≤ M (π/2 - θ)` on all of `(0, π/2)`.

Proof route: fix `θ ∈ (0, π/2)`; for `θ' ∈ (θ, π/2)` Newton–Leibniz on `[θ, θ']`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt` on the closed segment, where `u' = deriv u` is
continuous) gives `|u θ - u θ'| ≤ M (θ' - θ)`; then `θ' ↦ u θ' + M (θ' - θ)` and
`θ' ↦ u θ' - M (θ' - θ)` tend to `M (π/2 - θ)` and `-M (π/2 - θ)` along `𝓝[<] (π/2)`, so
`Filter.le_of_tendsto` gives both `u θ ≤ M (π/2 - θ)` and `u θ ≥ -M (π/2 - θ)`, i.e. the claim.
Note `(0, π/2) ∈ 𝓝[<] (π/2)`, so the pointwise hypothesis `hM` is available eventually.

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceULinearRight`. -/
theorem SliceULinearRight (u : ℝ → ℝ) {M : ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ) := by
  intro θ hθ
  obtain ⟨hθ0, hθpi⟩ := hθ
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) := hsm.differentiableOn (by norm_num)
  -- Newton–Leibniz on `[θ, θ']`: the mean value inequality for a differentiable function whose
  -- derivative is bounded by `M` on the segment.
  have hkey : ∀ θ' ∈ Set.Ioo θ (Real.pi / 2), |u θ' - u θ| ≤ M * (θ' - θ) := by
    intro θ' hθ'
    obtain ⟨hθ'1, hθ'2⟩ := hθ'
    have hf : ∀ x ∈ Set.Icc θ θ', HasDerivWithinAt u (deriv u x) (Set.Icc θ θ') x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hθ'2⟩
      exact ((hdiff x hx').differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt.hasDerivWithinAt
    have hb : ∀ x ∈ Set.Ico θ θ', ‖deriv u x‖ ≤ M := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_lt_of_le hθ0 hx.1, lt_trans hx.2 hθ'2⟩
      simpa [Real.norm_eq_abs] using hM x hx'
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hf hb θ' (Set.right_mem_Icc.mpr hθ'1.le)
    simpa [Real.norm_eq_abs] using h
  -- `(θ, π/2)` is a neighbourhood of `π/2` within `(-∞, π/2)`.
  have hIoo : Set.Ioo θ (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [show Set.Ioo θ (Real.pi / 2) = Set.Ioi θ ∩ Set.Iio (Real.pi / 2) from rfl]
    exact Filter.inter_mem (nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hθpi)) self_mem_nhdsWithin
  have hphi : Filter.Tendsto (fun θ' : ℝ => M * (θ' - θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (M * (Real.pi / 2 - θ))) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto (Real.pi / 2)).mono_left
      nhdsWithin_le_nhds
  have hupper : u θ ≤ M * (Real.pi / 2 - θ) := by
    have hlim1 : Filter.Tendsto (fun θ' : ℝ => u θ' + M * (θ' - θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (M * (Real.pi / 2 - θ))) := by
      have h := hpi.add hphi
      simpa using h
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim1 ?_
    filter_upwards [hIoo] with θ' hθ'
    have h2 := (abs_le.mp (hkey θ' hθ')).1
    linarith
  have hlower : -(M * (Real.pi / 2 - θ)) ≤ u θ := by
    have hlim3 : Filter.Tendsto (fun θ' : ℝ => u θ' - M * (θ' - θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-(M * (Real.pi / 2 - θ)))) := by
      have h := hpi.sub hphi
      simpa using h
    refine le_of_tendsto_of_tendsto hlim3 tendsto_const_nhds ?_
    filter_upwards [hIoo] with θ' hθ'
    have h2 := (abs_le.mp (hkey θ' hθ')).2
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

end Work.FTS.EllipticEst.Honest.SelfAux
