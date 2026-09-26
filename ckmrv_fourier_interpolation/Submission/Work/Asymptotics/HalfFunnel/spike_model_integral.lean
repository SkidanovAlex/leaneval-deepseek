import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.spike_inv_integral_bound
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral_succ

namespace Work.Asymptotics.HalfFunnel

/-- **The signed model integral of a simple pole across the contour, uniformly in the pole's
distance from the integration interval.**

For `0 < ρ < y` and `m : ℕ` there is `C ≥ 0` with

`‖∫_u ∈ (-ρ,ρ), e^{-a(y+u)} · (u + iε)⁻¹ · u^m du‖ ≤ C`

for all `a > 0` and all `0 < |ε| ≤ 1/4`.

The modulus of the integrand blows up like `1/|ε|` at `u = 0`, and `∫_{-ρ}^{ρ} 1/|u + iε| du`
diverges logarithmically as `ε → 0`; the *signed* integral does not.  Since `u ∈ (-ρ,ρ)` and
`ρ < y` one has `y + u ≥ y - ρ > 0`, so the weight `g u = e^{-a(y+u)}` satisfies `0 < g ≤ 1` and
`|g'| ≤ a·g ≤ a`.

The proof is by induction on `m`.  The recursion
`u^{m+1}/(u+iε) = u^m - iε·u^m/(u+iε)` reduces `m + 1` to `m`, with the companion integral
`∫ e^{-a(y+u)} u^m du` bounded by `2ρ^{m+1}` because `|e^{-a(y+u)}| ≤ 1` and `|u| ≤ ρ`
(`spike_model_integral_succ`).  The base case `m = 0` splits
`(u+iε)⁻¹ = (u-iε)/(u²+ε²)`; the `u`-part is controlled by the odd antiderivative
`½ log(u²+ε²)` together with the mean-value bound `|e^{-a(y+u)} - e^{-ay}| ≤ a e^{-a(y-ρ)}|u|`,
and the `iε`-part by `|ε| ∫_{-ρ}^ρ (u²+ε²)⁻¹ du ≤ π` (`spike_inv_integral_bound`). -/
theorem spike_model_integral (m : ℕ) {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ) (hρy : ρ < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)‖ ≤ C := by
  induction m with
  | zero =>
      obtain ⟨C, hC, h⟩ := spike_inv_integral_bound hy hρ hρy
      refine ⟨C, hC, fun a ε ha hε hε4 => ?_⟩
      simpa using h a ε ha hε hε4
  | succ m ih =>
      obtain ⟨C, hC, h⟩ := ih
      exact spike_model_integral_succ m hy hρ hρy C hC h

end Work.Asymptotics.HalfFunnel
