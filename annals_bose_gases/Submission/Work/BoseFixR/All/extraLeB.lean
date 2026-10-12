import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.All

/-- Pure scalar core of `extraLeB`.

With `ρ ≤ μ/10`, `g ≤ 16πa`, `0 ≤ x ≤ 1` and every quantity nonnegative, the
quantity `½ρ²g(2(1+x)−1)` is bounded by `4a(ρ−μ)²`: the left side is at most
`½(μ/10)²g·3 ≤ ½(μ²/100)(16πa)·3 = (6π/25)aμ²`, while the right side is at least
`4a(9μ/10)² = (81/25)aμ²`, and `6π < 81`.  The factor
`2(1+x)−1 = 1+2x` is the `1 + 2·(S(R/ℓ)²)` of the target, bounded by `3` because
`x ≤ 1`. -/
private lemma extraLeB_arith {a μ ρ g x : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hρ : 0 ≤ ρ)
    (hρμ : 10 * ρ ≤ μ) (hg0 : 0 ≤ g) (hg : g ≤ 16 * Real.pi * a)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 / 2) * ρ ^ 2 * g * (2 * (1 + x) - 1) ≤ 4 * a * (ρ - μ) ^ 2 := by
  have hx3 : 2 * (1 + x) - 1 ≤ 3 := by linarith
  have hx0' : 0 ≤ 2 * (1 + x) - 1 := by linarith
  -- `ρ² ≤ μ²/100`
  have hρ2 : ρ ^ 2 ≤ μ ^ 2 / 100 := by nlinarith
  -- `μ²/2 ≤ (ρ−μ)²`
  have hμm : μ ^ 2 / 2 ≤ (ρ - μ) ^ 2 := by nlinarith
  have h1 : ρ ^ 2 * (2 * (1 + x) - 1) ≤ (μ ^ 2 / 100) * 3 :=
    mul_le_mul hρ2 hx3 hx0' (by positivity)
  have h2 : (1 / 2 : ℝ) * g * (ρ ^ 2 * (2 * (1 + x) - 1))
      ≤ (1 / 2) * g * ((μ ^ 2 / 100) * 3) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (1 / 2 : ℝ) * g * ((μ ^ 2 / 100) * 3)
      ≤ (1 / 2) * (16 * Real.pi * a) * ((μ ^ 2 / 100) * 3) := by
    have hgg : (1 / 2 : ℝ) * g ≤ (1 / 2) * (16 * Real.pi * a) := by nlinarith
    exact mul_le_mul_of_nonneg_right hgg (by positivity)
  -- `½(16πa)(3μ²/100) ≤ 4a(μ²/2)` — the only place `π < 4` is used
  have hstep : (1 / 2 : ℝ) * (16 * Real.pi * a) * ((μ ^ 2 / 100) * 3)
      ≤ 4 * a * (μ ^ 2 / 2) := by
    have hY : (0 : ℝ) ≤ a * μ ^ 2 / 100 := by positivity
    have hp : (24 : ℝ) * Real.pi ≤ 200 := by nlinarith [Real.pi_lt_four]
    calc (1 / 2 : ℝ) * (16 * Real.pi * a) * ((μ ^ 2 / 100) * 3)
        = 24 * Real.pi * (a * μ ^ 2 / 100) := by ring
      _ ≤ 200 * (a * μ ^ 2 / 100) := mul_le_mul_of_nonneg_right hp hY
      _ = 4 * a * (μ ^ 2 / 2) := by ring
  have hR : 4 * a * (μ ^ 2 / 2) ≤ 4 * a * (ρ - μ) ^ 2 :=
    mul_le_mul_of_nonneg_left hμm (by positivity)
  nlinarith [h2, h3, hstep, hR]

theorem extraLeB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ ρ S g : ℝ}
    (hav : 0 < BoseGases.a v) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hρμ : 10 * ρ ≤ μ)
    (hS : 0 ≤ S) (hg0 : 0 ≤ g) (hg : g ≤ 16 * Real.pi * BoseGases.a v)
    (hS1 : S * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 1) :
    (1 / 2) * ρ ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 * g
        * (2 * (1 + S * (R / Work.BoseFixR.ell v μ) ^ 2) - 1)
      ≤ 4 * BoseGases.a v * (ρ - μ) ^ 2 * (Work.BoseFixR.ell v μ) ^ 3 := by
  have hLpos : 0 < Work.BoseFixR.ell v μ := Work.BoseBox.sideAt_pos hμ hav
  set L := Work.BoseFixR.ell v μ with hL
  have hLpos' : 0 < L := hL ▸ hLpos
  -- `x := S (R/L)² ∈ [0,1]`
  set x := S * (R / L) ^ 2 with hx
  have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg hS (sq_nonneg _)
  have hx1 : x ≤ 1 := hS1
  have hkey : (1 / 2) * ρ ^ 2 * g * (2 * (1 + x) - 1)
      ≤ 4 * BoseGases.a v * (ρ - μ) ^ 2 :=
    extraLeB_arith hav hμ hρ hρμ hg0 hg hx0 hx1
  have hL3 : (0 : ℝ) ≤ L ^ 3 := pow_nonneg (le_of_lt hLpos') 3
  calc (1 / 2) * ρ ^ 2 * L ^ 3 * g * (2 * (1 + x) - 1)
      = ((1 / 2) * ρ ^ 2 * g * (2 * (1 + x) - 1)) * L ^ 3 := by ring
    _ ≤ (4 * BoseGases.a v * (ρ - μ) ^ 2) * L ^ 3 :=
        mul_le_mul_of_nonneg_right hkey hL3
    _ = 4 * BoseGases.a v * (ρ - μ) ^ 2 * L ^ 3 := by ring

end Work.BoseFixR.All
