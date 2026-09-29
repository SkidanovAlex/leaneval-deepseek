import Mathlib
import Submission.Work.TMC16Core.Defs

set_option linter.unusedVariables false

namespace Work.TMC16Core.CF

/-- **Continued-fraction "saving" from `DiophBelow`.**

If `DiophBelow α b₀` holds (i.e. `fracDist (k α) ≥ e^{-b₀ k}` for all large `k`) and
`q` is strictly increasing with `fracDist (q m · α) < 1 / q (m+1)` for every `m`, then
for every `ε > 0` one has `q (m+1) ≤ exp ((b₀ + ε) q m)` for all large `m`.

The argument is direct: `StrictMono q` forces `q m ≥ m`, so the index `k = q m` is
eventually large and `DiophBelow` applies there; combining
`e^{-b₀ q m} ≤ fracDist (q m α) < 1/q(m+1)` with `q(m+1) > 0` gives
`q (m+1) < e^{b₀ q m} ≤ e^{(b₀+ε) q m}`. -/
theorem cf_saving {α b₀ : ℝ} (hb₀ : 0 ≤ b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ → ℕ} (hmono : StrictMono q)
    (h : ∀ m, Work.TMC16Core.fracDist ((q m : ℝ) * α) < 1 / ((q (m + 1) : ℝ))) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ((q (m + 1) : ℕ) : ℝ) ≤ Real.exp ((b₀ + ε) * (q m : ℝ)) := by
  -- `StrictMono q` for `q : ℕ → ℕ` gives `q m ≥ m`, in particular `q m → ∞`.
  have hqid : ∀ m, m ≤ q m := by
    intro m
    induction m with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hlt : q n < q (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  rw [Work.TMC16Core.DiophBelow] at hDioph
  rw [Filter.eventually_atTop] at hDioph ⊢
  obtain ⟨K, hK⟩ := hDioph
  refine ⟨K, fun m hm => ?_⟩
  have hmq : K ≤ q m := le_trans hm (hqid m)
  -- `DiophBelow` at the index `k = q m` (eventually valid since `q m ≥ m`).
  have h1 : Real.exp (-(b₀ * (q m : ℝ))) ≤ Work.TMC16Core.fracDist ((q m : ℝ) * α) :=
    hK (q m) hmq
  have h2 : Work.TMC16Core.fracDist ((q m : ℝ) * α) < 1 / ((q (m + 1) : ℝ)) := h m
  have h3 : Real.exp (-(b₀ * (q m : ℝ))) < 1 / ((q (m + 1) : ℝ)) := lt_of_le_of_lt h1 h2
  have hQpos : (0 : ℝ) < (q (m + 1) : ℝ) := by
    have : 0 < q (m + 1) := lt_of_lt_of_le (Nat.succ_pos m) (hqid (m + 1))
    exact_mod_cast this
  -- `e^{-b₀ q m} = 1 / e^{b₀ q m}`
  have h4 : (1 : ℝ) / Real.exp (b₀ * (q m : ℝ)) < 1 / ((q (m + 1) : ℝ)) := by
    simpa [Real.exp_neg, one_div] using h3
  -- inverting the positive quantities `e^{b₀ q m} > 0` and `q (m+1) > 0`
  have h5 : (q (m + 1) : ℝ) < Real.exp (b₀ * (q m : ℝ)) := by
    rw [one_div, one_div] at h4
    exact (inv_lt_inv₀ (Real.exp_pos _) hQpos).1 h4
  -- `e^{b₀ q m} ≤ e^{(b₀+ε) q m}` since `ε q m ≥ 0`
  exact le_trans (le_of_lt h5)
    (Real.exp_le_exp.2 (by
      nlinarith [hε, hb₀, mul_nonneg (le_of_lt hε) (Nat.cast_nonneg (q m))]))

end Work.TMC16Core.CF
