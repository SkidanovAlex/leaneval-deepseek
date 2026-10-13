import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.HardyTwoDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `htU f θ = f θ / sin (2θ)` is of class `C²` at every *interior* point `θ ∈ (0, π/2)`, where
`sin (2θ) ≠ 0`; note that on the closed interval the endpoints `0` and `π/2` are precisely the
zeros of the denominator, which is why only interior points are covered by the standing
hypothesis `hf`. -/
theorem htU_contDiffAt (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 (Work.Elliptic.htU f) θ := by
  -- `θ` is an interior point of `[0, π/2]`, so `f` is `C²` at `θ`.
  have hmem : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hθ) Ioo_subset_Icc_self
  have hfθ : ContDiffAt ℝ 2 f θ := hf.contDiffAt hmem
  -- the denominator `θ ↦ sin (2θ)` is smooth at `θ` and nonvanishing there.
  have hsin : ContDiffAt ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
  have hne : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < π := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  change ContDiffAt ℝ 2 (fun θ => f θ / Real.sin (2 * θ)) θ
  exact hfθ.div hsin hne

end Work.Elliptic
