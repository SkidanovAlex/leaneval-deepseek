import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Main

/-- Residue/Diophantine bound on the points `2θ + rα` for `|r| ≤ q/2`:
if all `2θ + kα` with `|k| < K₀` are at distance `≥ csm` from `ℤ`, and all others are at
distance `≥ 1/|k|²`, then for `|r| ≤ q/2` the distance is at least `4/q²`, provided
`csm * q² ≥ 10^6`. -/
theorem theta_residue_bound {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {n : ℕ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤
      Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqposn : 0 < q n)
    (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2) :
    ∀ r : ℤ, |r| ≤ (q n : ℝ) / 2 →
      4 / (q n : ℝ) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (r : ℝ) * α) := by
  intro r hr
  -- `q n ≥ 1`, hence `(q n)² > 0`
  have hq1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqposn
  have hqpos : (0 : ℝ) < (q n : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hq2pos : (0 : ℝ) < (q n : ℝ) ^ 2 := pow_pos hqpos 2
  -- (A) `4/(q n)² ≤ csm`, from `csm * (q n)² ≥ 10^6`
  have h4csm : 4 / (q n : ℝ) ^ 2 ≤ csm := by
    rw [div_le_iff₀ hq2pos]
    nlinarith [hbig]
  -- cast of `natAbs`
  have hcast : ∀ x : ℤ, (((x.natAbs : ℕ) : ℝ)) = |(x : ℝ)| := by
    intro x; rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  by_cases hcase : |r| < K₀
  · -- small residue: `csm ≤ fracDist ≤ ...` and `4/q² ≤ csm`
    exact le_trans h4csm (h1 r hcase)
  · push Not at hcase
    -- large residue: `K₀ ≤ |r|`
    have h2r := h2 r hcase
    rw [hcast r] at h2r
    have hrK : (K₀ : ℝ) ≤ |(r : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hcase
    have hr1 : (1 : ℝ) ≤ |(r : ℝ)| := le_trans (by exact_mod_cast hK₀1) hrK
    have hrpos : (0 : ℝ) < |(r : ℝ)| := lt_of_lt_of_le zero_lt_one hr1
    have hrab : |(r : ℝ)| ≤ (q n : ℝ) / 2 := by
      rw [← Int.cast_abs]; exact_mod_cast hr
    -- `|r|² ≤ (q/2)²`, hence `4/q² ≤ 1/|r|² = (|r|⁻¹)²`
    have hsq : |(r : ℝ)| ^ 2 ≤ ((q n : ℝ) / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hrab 2
    have hgoal : 4 / (q n : ℝ) ^ 2 ≤ ((|(r : ℝ)|)⁻¹) ^ 2 := by
      rw [inv_pow]
      rw [show 4 / (q n : ℝ) ^ 2 = ((q n : ℝ) ^ 2 / 4)⁻¹ by rw [inv_div]]
      rw [inv_le_inv₀ (by positivity) (pow_pos hrpos 2)]
      nlinarith [hsq]
    exact le_trans hgoal h2r

end Work.TMC16Core.Main
