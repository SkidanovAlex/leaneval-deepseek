import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.pd_window_helpers
import Submission.Work.TMC16Core.Main.theta_refold
import Submission.Work.TMC16Core.Main.theta_residue_bound
import Submission.Work.TMC16Core.Assembly.fast_shift_arith

namespace Work.TMC16Core.Assembly

/-- **`theta_range_fast`.**  Fast-scale (Liouville) version of the index-range reduction.

The two `fracDist` lower bounds — `csm` below the cut-off `|k| < K₀` and `1/k²` above it —
hold at every residue `|r| ≤ q n/2` with constant `4/(q n)²` (`Main.theta_residue_bound`,
using `csm * (q n)² ≥ 10⁶`).  Re-folding the index range `|k| ≤ 4 (q(n+1))^{8/9} + 8 q n + 4`
around the near-period `q n` costs at most `(Y/(q n) + 1/2)·Δ n ≤ 2/(q n)²`, because
`Δ n < 1/q(n+1)` and `q(n+1) ≥ (8 q n)^9` (`fast_shift_arith`).  So the bound
`2/(q n)²` survives on the whole range (`Main.theta_refold`). -/
theorem theta_range_fast {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n : ℕ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hn : 1 ≤ n) (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2)
    (hfast : (8 * q n) ^ 9 ≤ q (n + 1)) :
    ∀ j : ℤ, |(j : ℝ)| ≤ 4 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4 →
      2 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
  have hqnpos : 0 < q n := hqpos n
  have ha1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqnpos
  -- `hfast` over the reals
  have hfastR : (8 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) := by exact_mod_cast hfast
  -- elementary facts about `Δ n`
  have hΔ0 : 0 ≤ Δ n := by rw [hΔeq n]; exact abs_nonneg _
  have hΔlt : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
  -- (1) reduced-index bound with constant `4/(q n)²`
  have hred : ∀ r : ℤ, ((|r| : ℤ) : ℝ) ≤ (q n : ℝ) / 2 →
      4 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (r : ℝ) * α) :=
    Main.theta_residue_bound hK₀1 hcsm h1 h2 hqnpos hbig
  have hc : (0 : ℝ) < 4 / (q n : ℝ) ^ 2 := by positivity
  -- (2) the shift cost
  have hshift :
      ((4 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4) / (q n : ℝ) + 1 / 2) * Δ n
        ≤ (4 / (q n : ℝ) ^ 2) / 2 := by
    have h1' := fast_shift_arith (a := (q n : ℝ)) (b := (q (n + 1) : ℝ)) (Δ := Δ n)
      ha1 hΔ0 hfastR hΔlt
    have he : (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 := by ring
    rw [he]; exact h1'
  -- (3) re-fold the index range
  have key := Main.theta_refold (α := α) (θ := θ) (Q := q n) (Δ := Δ n)
      (c := 4 / (q n : ℝ) ^ 2)
      (Y := 4 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 8 * (q n : ℝ) + 4)
      hqnpos hc (hΔeq n) hred hshift
  intro j hj
  have hj' := key j hj
  have he : (4 / (q n : ℝ) ^ 2) / 2 = 2 / (q n : ℝ) ^ 2 := by ring
  rw [he] at hj'
  exact hj'

end Work.TMC16Core.Assembly
