import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Support and smoothness facts for the shrinking angular cut-off `angCut`

`angCut n θ = smoothTransition (θ/δ_n - 1) · smoothTransition ((π/2 - θ)/δ_n - 1)` with
`δ_n = 1/(n+1)` is the cut-off used to localise the zero-mode argument: it equals `1` on the
middle of `(0, π/2)`, vanishes off `[δ_n, π/2 - δ_n]`, and is `C^∞`.

This file proves `AngCutSupportFacts`, the bundle of the four analytic properties of `angCut`
(support control, eventual equality to `1` in the interior, `C^1`- and `C²`-smoothness) together
with the two definitional facts about its layer indicator `layerInd`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-! ## The length scale `δ_n = 1/(n+1)` -/

lemma delta_pos (n : ℕ) : 0 < delta n := by
  rw [delta]
  positivity

lemma delta_tendsto_zero : Tendsto delta Filter.atTop (𝓝 0) := by
  unfold delta
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-! ## Support of the cut-off -/

/-- The (plain) support of `angCut n` lies in `[δ_n, π/2 - δ_n]`: each factor vanishes once its
argument is `≤ 0`. -/
lemma angCut_support_subset (n : ℕ) :
    Function.support (angCut n) ⊆ Set.Icc (delta n) (Real.pi / 2 - delta n) := by
  intro θ hθ
  rw [Function.mem_support] at hθ
  have hδ : 0 < delta n := delta_pos n
  have hθ1 : 0 < θ / delta n - 1 := by
    by_contra h
    rw [not_lt] at h
    exact hθ (by rw [angCut, Real.smoothTransition.zero_of_nonpos h, zero_mul])
  have hθ2 : 0 < (Real.pi / 2 - θ) / delta n - 1 := by
    by_contra h
    rw [not_lt] at h
    exact hθ (by rw [angCut, Real.smoothTransition.zero_of_nonpos h, mul_zero])
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have hh : 1 * delta n < θ := (lt_div_iff₀ hδ).mp (by linarith)
    linarith
  · have hh : 1 * delta n < Real.pi / 2 - θ := (lt_div_iff₀ hδ).mp (by linarith)
    linarith

/-- The topological support of `angCut n` lies in the closed interval `[δ_n, π/2 - δ_n]`. -/
lemma angCut_tsupport_subset (n : ℕ) :
    tsupport (angCut n) ⊆ Set.Icc (delta n) (Real.pi / 2 - delta n) :=
  closure_minimal (angCut_support_subset n) isClosed_Icc

/-! ## Eventual equality to `1` in the interior -/

/-- For every interior angle `θ ∈ (0, π/2)` the cut-off is eventually `1` at `θ`: both arguments
of `smoothTransition` eventually exceed `1` because `δ_n → 0`. -/
lemma angCut_eventually_eq_one (θ : ℝ) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) :
    ∀ᶠ n in Filter.atTop, angCut n θ = 1 := by
  have hev1 : ∀ᶠ n in Filter.atTop, delta n < θ / 2 :=
    delta_tendsto_zero.eventually (eventually_lt_nhds (by linarith))
  have hev2 : ∀ᶠ n in Filter.atTop, delta n < (Real.pi / 2 - θ) / 2 :=
    delta_tendsto_zero.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hδn : 0 < delta n := delta_pos n
  have hle1 : (1 : ℝ) ≤ θ / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδn]
    linarith
  have hle2 : (1 : ℝ) ≤ (Real.pi / 2 - θ) / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδn]
    linarith
  rw [angCut, Real.smoothTransition.one_of_one_le hle1,
    Real.smoothTransition.one_of_one_le hle2, mul_one]

/-! ## Smoothness -/

/-- `angCut n` is `C²`: a product of two composites of the `C^∞` profile
`Real.smoothTransition` with affine maps. -/
lemma contDiff_two_angCut (n : ℕ) : ContDiff ℝ 2 (angCut n) := by
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => Real.smoothTransition (θ / delta n - 1)) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).comp (by fun_prop)
  have h2 : ContDiff ℝ 2
      (fun θ : ℝ => Real.smoothTransition ((Real.pi / 2 - θ) / delta n - 1)) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).comp (by fun_prop)
  exact h1.mul h2

/-! ## The layer indicator -/

lemma layerInd_eq_one_of_mem (n : ℕ) {θ : ℝ} (hθ : θ ∈ layer n) : layerInd n θ = 1 := by
  rw [layerInd, Set.indicator_of_mem hθ]

lemma layerInd_eq_zero_of_notMem (n : ℕ) {θ : ℝ} (hθ : θ ∉ layer n) : layerInd n θ = 0 :=
  Set.indicator_of_notMem hθ _

/-! ## The bundle -/

theorem AngCutSupportFacts :
    (∀ n : ℕ, tsupport (Work.FTS.StrongEps.EComparison.angCut n)
        ⊆ Set.Icc (Work.FTS.StrongEps.EComparison.delta n)
            (Real.pi / 2 - Work.FTS.StrongEps.EComparison.delta n)) ∧
    (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      ∀ᶠ n in Filter.atTop, Work.FTS.StrongEps.EComparison.angCut n θ = 1) ∧
    (∀ n : ℕ, Differentiable ℝ (Work.FTS.StrongEps.EComparison.angCut n)) ∧
    (∀ n : ℕ, Differentiable ℝ (deriv (Work.FTS.StrongEps.EComparison.angCut n))) ∧
    (∀ n : ℕ, ∀ θ : ℝ, θ ∈ Work.FTS.StrongEps.EComparison.layer n →
      Work.FTS.StrongEps.EComparison.layerInd n θ = 1) ∧
    (∀ n : ℕ, ∀ θ : ℝ, θ ∉ Work.FTS.StrongEps.EComparison.layer n →
      Work.FTS.StrongEps.EComparison.layerInd n θ = 0) := by
  refine ⟨angCut_tsupport_subset, angCut_eventually_eq_one, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (contDiff_two_angCut n).differentiable (by norm_num)
  · intro n
    exact ContDiff.differentiable_deriv_two (contDiff_two_angCut n)
  · intro n θ hθ
    exact layerInd_eq_one_of_mem n hθ
  · intro n θ hθ
    exact layerInd_eq_zero_of_notMem n hθ

end Work.FTS.StrongEps.EComparison
