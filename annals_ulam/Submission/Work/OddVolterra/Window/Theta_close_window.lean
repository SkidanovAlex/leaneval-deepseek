import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.Theta_close_aux
import Submission.Work.OddVolterra.Window.Kvec_deriv_close

/-!
# Closeness of the raw odd transition-slope kernel `Θ` to its unperturbed value

`Work.OddVolterra.Window.Theta_close_window`: on the transition window
`s ∈ [7/10, 19/20]`, `σ ∈ [7/10, 1]` and the state ball `‖z - baseState σ‖ ≤ 2/5`, the last
two rows of the paper's kernel `Θ n h s σ z` (the `s`-derivatives of the Abel average `G₂`)
differ from those of the unperturbed kernel `Θ n 0 s σ z` by at most `ε`, provided `h` is a
smooth bump supported in `[1 - 2τ, 1 - τ]` whose derivatives up to order `n + 2` are bounded
by `δ = δ(ε)`.

The proof is assembled in `Theta_close_aux`:

* for `s ≥ σ` both kernels' last two rows vanish identically
  (`Work.OddVolterra.Window.Theta_sub_Theta_eq_zero_of_le`), since the Abel average `G₂(·,σ,·)`
  vanishes to the right of `σ` (`G2_eq_zero_of_lt`) and a function vanishing on `(σ,∞)` has
  derivative `0` at `σ` (`deriv_eq_zero_of_eq_zero_on_Ioo`);
* for `s < σ` the rows are `-∫₀¹ (√(τ(1-τ)))⁻¹ (1-τ) ∂_a Kvec(s + τ(σ-s)) dτ`
  (`deriv_G2_eq_integral_of_lt`), and the kernel comparison
  `Work.OddVolterra.Window.Kvec_deriv_close` bounds the difference of `∂_a Kvec` by `C δ`;
  since `∫₀¹ (√(τ(1-τ)))⁻¹ = π` this gives `C δ π < ε` for `δ` small enough.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

theorem Theta_close_window (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ), ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1,
        ∀ z : Work.OddVolterra.St, ‖z - Work.OddVolterra.baseState σ‖ ≤ 2 / 5 →
        ‖Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n 0 s σ z‖ < ε :=
  Theta_close_window_of_kvec n hn (Kvec_deriv_close n hn)

end

end Work.OddVolterra.Window
