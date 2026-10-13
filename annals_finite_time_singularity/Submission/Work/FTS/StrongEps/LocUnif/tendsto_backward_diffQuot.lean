import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem tendsto_backward_diffQuot {f : ℝ → ℝ} {x : ℝ} (hx : DifferentiableAt ℝ f x)
    {s : ℕ → ℝ} (hs : Filter.Tendsto s Filter.atTop (nhds 0)) (hspos : ∀ j, 0 < s j) :
    Filter.Tendsto (fun j => (f x - f (x - s j)) / s j) Filter.atTop (nhds (deriv f x)) := by
  -- `x - s j → x` and stays away from `x`, since `s j > 0`.
  have h1 : Filter.Tendsto (fun j => x - s j) Filter.atTop (nhdsWithin x {x}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds.sub hs)
    · filter_upwards with j
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      linarith [hspos j]
  -- Rewrite the backward difference quotient as the slope at `x - s j`.
  have h2 : Filter.Tendsto (fun j => slope f x (x - s j)) Filter.atTop (nhds (deriv f x)) :=
    (hx.hasDerivAt.tendsto_slope).comp h1
  have hfun : (fun j => slope f x (x - s j)) = fun j => (f x - f (x - s j)) / s j := by
    funext j
    rw [slope_def_field]
    ring_nf
  rwa [hfun] at h2

end Work.FTS.StrongEps.LocUnif
