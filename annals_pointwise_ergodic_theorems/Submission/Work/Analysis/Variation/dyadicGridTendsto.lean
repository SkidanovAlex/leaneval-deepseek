import Mathlib
import Submission.Work.Analysis.Variation.DyadicGrid

namespace Work.Analysis.Variation

open scoped Topology
open Filter

/-- **The level-`L` dyadic variation of `h` along a chain converges to the exact variation.**

For a continuous `h : ℝ → ℂ`, a chain `t : Fin (J+1) → ℝ` with values in `[0,1]`, and any real `r`,
the `ℓ^r` norm of the jumps of `h` along the chain of dyadic roundings `dyadPt L (t i)` converges,
as `L → ∞`, to the `ℓ^r` norm of the exact jumps of `h` along `t`:

`(∑_i ‖h (dyadPt L (t_{i+1})) - h (dyadPt L (t_i))‖^r)^{1/r} → (∑_i ‖h (t_{i+1}) - h (t_i)‖^r)^{1/r}`

in `ℝ≥0∞`.  This is continuity of `h` plus the pointwise convergence `dyadPt L z → z` for `z ≥ 0`
(`Work.Analysis.Variation.dyadPt_tendsto`), through continuous operations on `ℝ≥0∞` (enorm,
`x ↦ x ^ r`, finite sums, `x ↦ x ^ (1/r)` -- note `ENNReal.continuous_rpow_const` holds for *every*
real exponent).  The file should be in namespace `Work.Analysis.Variation` and import
`Submission.Work.Analysis.Variation.DyadicGrid`. -/
theorem dyadicGridTendsto (r : ℝ) (h : ℝ → ℂ) (hc : Continuous h) {J : ℕ} (t : Fin (J + 1) → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    Filter.Tendsto
      (fun L : ℕ =>
        (∑ i : Fin J, ‖h (dyadPt L (t i.succ)) - h (dyadPt L (t i.castSucc))‖ₑ ^ r) ^ (1 / r))
      Filter.atTop
      (nhds ((∑ i : Fin J, ‖h (t i.succ) - h (t i.castSucc)‖ₑ ^ r) ^ (1 / r))) := by
  have _ht1 : ∀ i, t i ≤ 1 := ht1
  -- The functional `F` sending a chain `s` to the `ℓ^r` norm of the exact jumps of `h` along `s`.
  let F : (Fin (J + 1) → ℝ) → ENNReal := fun s =>
    (∑ i : Fin J, ‖h (s i.succ) - h (s i.castSucc)‖ₑ ^ r) ^ (1 / r)
  -- `F` is continuous: point evaluation, `h`, subtraction, `enorm`, `rpow`, finite sum, `rpow`.
  have hF : Continuous F := by
    unfold F; fun_prop
  -- The rounded chain tends to the exact chain coordinatewise, hence in the product topology.
  have hg : Tendsto (fun L : ℕ => fun i : Fin (J + 1) => dyadPt L (t i)) atTop (𝓝 t) :=
    tendsto_pi_nhds.mpr (fun i => dyadPt_tendsto (ht0 i))
  -- Compose continuity of `F` at `t` with this convergence.
  have := (hF.tendsto t).comp hg
  simpa [F, Function.comp_def] using this

end Work.Analysis.Variation
