import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

-- `u` smooth on the open interval, `u → 0` and `u' → L` at π/2^-  ⟹  u/cos θ → -L.
-- Route: u θ = -∫_θ^{π/2} u' (FTC on (θ, π/2-ε) for a fixed θ, then let ε→0 using u → 0), and
-- u' = L + (u'-L) with |∫_θ^{π/2}(u'-L)| ≤ δ·sup_{t>θ}|u'(t)-L| = o(δ), δ := π/2-θ; so
-- u θ/cos θ = -L·δ/cos θ - o(δ)/cos θ → -L, using δ/cos θ = δ/sin δ → 1.
theorem divCos_tendsto_of_tendsto_deriv {u : ℝ → ℝ} {L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hzero : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hL : Filter.Tendsto (deriv u) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-L)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdiff : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm 1).differentiableOn (by norm_num)
  have hff' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    exact ((hdiff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hgg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt Real.cos ((fun x => -Real.sin x) x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (fun x => -Real.sin x) x ≠ 0 := by
    intro x hx
    have hπx : x < Real.pi := by linarith [Real.pi_pos, hx.2]
    have hpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 hπx
    simp only
    intro h
    linarith
  have hgb : Filter.Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    have h : Filter.Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (Real.cos (Real.pi / 2))) :=
      Real.continuous_cos.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [Real.cos_pi_div_two] using h
  have hdiv : Filter.Tendsto (deriv u / fun x => -Real.sin x)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-L)) := by
    have hsin : Filter.Tendsto (fun x : ℝ => -Real.sin x)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (-1)) := by
      have h : Filter.Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.sin (Real.pi / 2))) :=
        Real.continuous_sin.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h' := h.neg
      simpa [Real.sin_pi_div_two] using h'
    have hd := hL.div hsin (by norm_num : (-1 : ℝ) ≠ 0)
    have hLdiv : L / (-1 : ℝ) = -L := by ring
    rwa [hLdiv] at hd
  exact HasDerivAt.lhopital_zero_left_on_Ioo (f := u) (g := Real.cos)
    (f' := deriv u) (g' := fun x => -Real.sin x) (l := nhds (-L))
    hπ hff' hgg' hg' hzero hgb hdiv

end Work.FTS.EllipticEst.Honest
