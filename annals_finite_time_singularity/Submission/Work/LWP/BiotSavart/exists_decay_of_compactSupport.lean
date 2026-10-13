/-
# `Work.LWP.BiotSavart.exists_decay_of_compactSupport` — the `1/(1+‖x‖)` decay of the
Biot–Savart field of a compactly supported, bounded vorticity

For a vorticity `ω` that is bounded by `M ≥ 0` and supported in the closed ball of radius `R ≥ 0`
about the origin, the Newtonian-potential Biot–Savart field decays at least like `‖x‖⁻¹`:

  `∃ C, ∀ x, ‖biotSavart ω x‖ ≤ C / (1 + ‖x‖)`.

This is the tail of the `C^{1,α}`-closure estimate for the Biot–Savart map: it is exactly the
`decay` field of `Work.LWP.EulerDataBS` (the velocity decays at infinity so that the Biot–Savart
law inverts `∇×`), and it is what the Lichtenstein–Gunther reconstruction consumes.

The proof glues together the two unconditional Biot–Savart estimates already established in this
directory:

* `Work.LWP.BiotSavart.norm_biotSavart_near` — for `‖x‖ ≤ 2R`, `‖biotSavart ω x‖ ≤ 3 M R`;
* `Work.LWP.BiotSavart.farField_decay_const` — for `2R ≤ ‖x‖`,
  `‖biotSavart ω x‖ ≤ (4/3) M R³ / ‖x‖²`.

Both are dominated by `C / (1 + ‖x‖)` with the single constant `C = 3 M R (1 + 2R)`:

* near field: `‖x‖ ≤ 2R` gives `1 + ‖x‖ ≤ 1 + 2R`, hence `3 M R ≤ C/(1 + ‖x‖)`;
* far field: with `n = ‖x‖ ≥ 2R`, the elementary inequality
  `(4/3) M R³ (1 + n) ≤ 3 M R (1 + 2R) n²` (proved below by substituting `n = 2R + s`, `s ≥ 0`,
  so that every coefficient is nonnegative) gives `(4/3) M R³/n² ≤ C/(1 + n)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.LWP.BiotSavart.farField_decay_const

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

theorem exists_decay_of_compactSupport {ω : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, ∀ x : R3, ‖biotSavart ω x‖ ≤ C / (1 + ‖x‖) := by
  refine ⟨3 * M * R * (1 + 2 * R), ?_⟩
  intro x
  -- the proposed constant is nonnegative
  have hC : (0 : ℝ) ≤ 3 * M * R * (1 + 2 * R) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hR) (by linarith)
  have hn0 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  rcases lt_or_ge (2 * R) ‖x‖ with hx | hx
  · -- **far field**: `2R ≤ ‖x‖`
    have hx' : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hb := farField_decay_const hR hM hω hsupp x hx'
    -- the elementary inequality `(4/3) R² (1+n) ≤ 3 (1+2R) n²` for `n ≥ 2R ≥ 0`
    have hbr : (4 / 3) * R ^ 2 * (1 + ‖x‖) ≤ 3 * (1 + 2 * R) * ‖x‖ ^ 2 := by
      set s := ‖x‖ - 2 * R with hsdef
      have hs : 0 ≤ s := by linarith
      have hn : ‖x‖ = 2 * R + s := by linarith
      rw [hn]
      nlinarith [hs, hR, mul_nonneg hR hs, mul_nonneg (mul_nonneg hR hR) hs,
        mul_nonneg hR (sq_nonneg s), sq_nonneg s]
    have hMR : 0 ≤ M * R := mul_nonneg hM hR
    -- multiply by `M R ≥ 0`
    have harith : (4 / 3) * M * R ^ 3 * (1 + ‖x‖)
        ≤ 3 * M * R * (1 + 2 * R) * ‖x‖ ^ 2 := by
      calc (4 / 3) * M * R ^ 3 * (1 + ‖x‖)
          = (M * R) * ((4 / 3) * R ^ 2 * (1 + ‖x‖)) := by ring
        _ ≤ (M * R) * (3 * (1 + 2 * R) * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hbr hMR
        _ = 3 * M * R * (1 + 2 * R) * ‖x‖ ^ 2 := by ring
    have key : (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2
        ≤ 3 * M * R * (1 + 2 * R) / (1 + ‖x‖) := by
      rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hnpos
      · -- `‖x‖ = 0` forces `R = 0` (and Lean's `a/0 = 0`); the bound is trivial
        rw [← h0]; simpa using hC
      · refine (le_div_iff₀ hn0).mpr ?_
        rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hnpos 2)]
        exact harith
    exact hb.trans key
  · -- **near field**: `‖x‖ ≤ 2R`
    have hb := norm_biotSavart_near hR hM hω hsupp hx
    have key : 3 * M * R ≤ 3 * M * R * (1 + 2 * R) / (1 + ‖x‖) := by
      rw [le_div_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ 3 * M * R by positivity)]
    exact hb.trans key

end Work.LWP.BiotSavart
