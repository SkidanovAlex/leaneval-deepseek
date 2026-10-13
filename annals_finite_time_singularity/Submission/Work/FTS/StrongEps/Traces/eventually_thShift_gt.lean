import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.Traces

open scoped Real Topology
open Filter

/-- As `θ → π/2⁻`, the shift `thShift θ p = arctan (tan θ · e^{-p})` tends to `π/2` uniformly
for `p` in a bounded set: `tan θ · e^{-p} → +∞` (for `p ≤ ε` bounded below by `-ε`, the factor
`e^{-p}` is bounded below by `e^{-ε}`), and `arctan → π/2` at `+∞`.  Monotonicity of `thShift`
in `p` shows that the worst case is `p = ε`. -/
theorem eventually_thShift_gt (ε δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ θ in 𝓝[<] (Real.pi / 2), ∀ p : ℝ, |p| ≤ ε →
      Real.pi / 2 - δ < Work.FTS.StrongEps.thShift θ p := by
  -- `tan θ · e^{-ε} → +∞` as `θ → π/2⁻`
  have htan : Tendsto (fun θ : ℝ => Real.tan θ * Real.exp (-ε)) (𝓝[<] (Real.pi / 2)) atTop :=
    Real.tendsto_tan_pi_div_two.atTop_mul_const (Real.exp_pos (-ε))
  -- hence `thShift θ ε = arctan (tan θ · e^{-ε}) → π/2`
  have hcomp : Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-ε)))
      (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp htan
  have hmem : Real.pi / 2 ∈ Set.Ioi (Real.pi / 2 - δ) := by
    show Real.pi / 2 - δ < Real.pi / 2
    linarith
  have h2 : ∀ᶠ θ in 𝓝[<] (Real.pi / 2),
      Real.pi / 2 - δ < Work.FTS.StrongEps.thShift θ ε := by
    filter_upwards [hcomp.eventually (isOpen_Ioi.mem_nhds hmem)] with θ hθ
    simpa only [Work.FTS.StrongEps.thShift] using hθ
  -- and eventually `θ ∈ (0, π/2)`, where `p ↦ thShift θ p` is antitone
  have h1 : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2)),
      (self_mem_nhdsWithin : Set.Iio (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2))] with θ hgt hlt
    exact ⟨hgt, hlt⟩
  filter_upwards [h1, h2] with θ hθ hlt p hp
  exact lt_of_lt_of_le hlt
    (Work.FTS.StrongEps.thShift_anti hθ (le_trans (le_abs_self p) hp))

end Work.FTS.StrongEps.Traces
