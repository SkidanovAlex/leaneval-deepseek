import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.powSeries_hasDerivAt_of_majorant
import Submission.Work.CPull.summable_deriv_powSeries_of_majorant

namespace Work.CPull

/-- **Term-by-term differentiation of a pullback series.** If `Σ aₙ Ψ(w)ⁿ = F w` for `w` in an open
neighbourhood `U` of `0`, and on the disc `‖z‖ < δ` the values `Ψ z` stay inside a disc of radius
`s` on which the derivative series is absolutely dominated (`Summable (fun n ↦ ‖a n‖ * n * s ^ n)`),
and `deriv Ψ` does not vanish there, then for `‖z‖ < δ` the pullback of the derivative series
converges with value `deriv F z / deriv Ψ z`.

*Sketch.* `d/dz (Σ aₙ Ψ(z)ⁿ) = deriv Ψ z · Σ (n+1) aₙ₊₁ Ψ(z)ⁿ` by termwise differentiation
(`hasDerivAt_tsum_of_isPreconnected` on the disc, with majorant `‖a n‖ * n * s ^ n * C` coming from
`hsum`, `hΨb` and a bound `L` for `‖deriv Ψ‖` on the closed disc), and on `U` the pullback function
agrees with `F`, so its derivative is `deriv F z`; divide by `deriv Ψ z ≠ 0` (`hΨ'ne`). -/
theorem hasSum_deriv_series_of_majorant {a : ℕ → ℂ} {Ψ F : ℂ → ℂ} {U : Set ℂ} {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hδ1 : δ ≤ 1)
    (hUopen : IsOpen U) (hδU : ∀ z : ℂ, ‖z‖ < δ → z ∈ U)
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hΨb : ∀ z : ℂ, ‖z‖ < δ → ‖Ψ z‖ < s)
    (hΨ'ne : ∀ z : ℂ, ‖z‖ < δ → deriv Ψ z ≠ 0)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * n * s ^ n))
    (hF : DifferentiableOn ℂ F U)
    (hgerm : ∀ z ∈ U, HasSum (fun n : ℕ => a n * Ψ z ^ n) (F z)) :
    ∀ z : ℂ, ‖z‖ < δ →
      HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * Ψ z ^ n) (deriv F z / deriv Ψ z) := by
  intro z hz
  -- `z` lies in the open set `U` and in the unit disc
  have hzU : z ∈ U := hδU z hz
  have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz hδ1
  -- `Ψ` is differentiable at `z`, with derivative `deriv Ψ z`
  have hΨ_diff : DifferentiableAt ℂ Ψ z :=
    hΨ.differentiableAt (Metric.isOpen_ball.mem_nhds hz_ball)
  have hΨ_deriv : HasDerivAt Ψ (deriv Ψ z) z := hΨ_diff.hasDerivAt
  -- the power series `f = Σ aₙ wⁿ`
  set f : ℂ → ℂ := fun w => ∑' n : ℕ, a n * w ^ n with hfdef
  have hw : ‖Ψ z‖ < s := hΨb z hz
  -- `f` is differentiable at `Ψ z` with the termwise-differentiated series as derivative
  have hf_deriv : HasDerivAt f (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n) (Ψ z) := by
    rw [hfdef]; exact powSeries_hasDerivAt_of_majorant hs hsum (Ψ z) hw
  -- chain rule
  have hG : HasDerivAt (f ∘ Ψ)
      ((∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n) * deriv Ψ z) z :=
    hf_deriv.comp z hΨ_deriv
  -- on `U` the pullback series agrees with `F`, hence near `z` as well
  have hFG : F =ᶠ[nhds z] (f ∘ Ψ) := by
    refine Filter.eventually_of_mem (hUopen.mem_nhds hzU) ?_
    intro y hyU
    have hsum_y : HasSum (fun n : ℕ => a n * Ψ y ^ n) (F y) := hgerm y hyU
    rw [hfdef]
    simp only [Function.comp_apply]
    exact hsum_y.tsum_eq.symm
  have hF_deriv : HasDerivAt F
      ((∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n) * deriv Ψ z) z :=
    hG.congr_of_eventuallyEq hFG
  have hderivF : deriv F z
      = (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n) * deriv Ψ z :=
    hF_deriv.deriv
  -- the derivative series is summable at `Ψ z`
  have hsumm : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n) :=
    summable_deriv_powSeries_of_majorant hs hsum (Ψ z) hw
  have hval : deriv F z / deriv Ψ z
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n := by
    rw [hderivF]
    exact mul_div_cancel_right₀ _ (hΨ'ne z hz)
  have hgoal : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) * Ψ z ^ n)
      (deriv F z / deriv Ψ z) := by
    rw [hval]
    exact hsumm.hasSum
  simpa only [Nat.cast_add, Nat.cast_one] using hgoal

end Work.CPull
