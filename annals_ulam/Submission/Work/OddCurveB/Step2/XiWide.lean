import Mathlib
import Submission.Work.Anchor.Xi_close

/-!
# `Ξ`-closeness on the wide transition window `[1/4, 19/20]`

`Work.Anchor.Xi_close` states the closeness `‖Ξ n h s - Ξ n 0 s‖ ≤ C δ` for `s ∈ [1/2, 19/20]`
(slope window of the narrow transition core).  This file proves the same statement on the *wide*
window `[1/4, 19/20]`, which is what the wide state/derivative closeness core
(`Submission.Work.OddCurveB.Step2.StateWide`) needs: the assembly `xi_close_assembly` is
parametric in the left end `a`, and the `E₁`/`E₂` bounds `xi_close_E1_E2_hundred` are parametric in
`c`; one simply instantiates them at `a = 1/4`, `c = 1/8 = a/2`.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **`Ξ`-closeness on the wide window.**  For every smooth bump `h` supported in the transition
window `[1-2τ, 1-τ]` whose derivatives up to order `n+2` are bounded by `δ ≤ 1/100`,
`‖Ξ n h s - Ξ n 0 s‖ ≤ C δ` for every `s ∈ [1/4, 19/20]`. -/
theorem w_Xi_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
        ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ ≤ C * δ := by
  obtain ⟨C₀, hC₀nn, hE⟩ := Work.OddVolterra.Existence.xi_close_E1_E2_hundred n hn
    (c := (1 / 4 : ℝ) / 2) (by norm_num)
    (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num)
  obtain ⟨K, hKpos, hK⟩ := Work.OddVolterra.Existence.xi_close_assembly n hn
    (a := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨K * (C₀ + 1), by positivity, ?_⟩
  intro h hh hsupp δ hδpos hδR hjet s hs
  have hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100 := by
    intro t
    have h1 : |iteratedDeriv 0 h t| ≤ δ := hjet 0 (by omega) t
    rw [iteratedDeriv_zero] at h1
    linarith
  obtain ⟨hE1b, hE1l, hE2b, hE2l⟩ := hE h δ hh hδpos hδR hjet
  have hmain := hK h (C₀ * δ) (mul_nonneg hC₀nn hδpos.le) hh hsupp hsmall
    hE1b hE1l hE2b hE2l s ⟨hs.1, by linarith [hs.2]⟩
  calc ‖Work.OddVolterra.Xi n h s - Work.OddVolterra.Xi n 0 s‖ ≤ K * (C₀ * δ) := hmain
    _ = K * C₀ * δ := by ring
    _ ≤ K * (C₀ + 1) * δ := by
        have h : 0 ≤ K * δ := mul_nonneg hKpos.le hδpos.le
        have he : K * (C₀ + 1) * δ = K * C₀ * δ + K * δ := by ring
        rw [he]; linarith

end

end Work.OddCurveB.Step2
