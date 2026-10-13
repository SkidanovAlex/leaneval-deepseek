import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LGammaT_abs_le_on_compact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsWp

/-- `|a / b| ≤ |a|` as soon as `1 ≤ b`. -/
private lemma abs_div_le_abs_of_one_le {a b : ℝ} (hb : 1 ≤ b) : |a / b| ≤ |a| := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  rw [abs_div, abs_of_nonneg hb0.le, div_le_iff₀ hb0]
  exact le_mul_of_one_le_right (abs_nonneg a) hb

/-- `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

/-- **`𝓛_Γ^T` is bounded pointwise in terms of the data bound `B`.**  Unfolding
`𝓛_Γ^T = 𝓛 - (2zΓ/(c(1+z)²))L₁₂ - 𝕡(3D_θ/(1+z))` leaves five terms, each bounded by `B`
(the two `1/(1+z)` factors by `B` and `1 + z ≥ 1` on `z ≥ 0`, the two `L₁₂`-coefficients by
`hcoef`/`hcoef2` against `hL12f`/`hL12T`).  This is the pointwise form of
`Work.FTS.StrongEps.LGammaT_abs_le_on_compact`. -/
theorem LGammaT_abs_le_explicit {α B : ℝ} (hB : 0 ≤ B)
    {f : Work.FTS.Galerkin.Fn} {z θ : ℝ} (hz : 0 ≤ z)
    (hbnd : |f z θ| + |Work.Spaces.Dz f z θ| + |Work.Spaces.Dth f z θ| ≤ B)
    (hcoef : |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ B)
    (hcoef2 : |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ B)
    (hL12f : |Work.Coercivity.L12f f z| ≤ B)
    (hL12T : |Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B) :
    |Work.Coercivity.LGammaT α f z θ| ≤ 7 * B + 2 * (B * B) := by
  have hz1 : (1 : ℝ) ≤ 1 + z := by linarith
  have hfB : |f z θ| ≤ B := by
    nlinarith [abs_nonneg (Work.Spaces.Dz f z θ), abs_nonneg (Work.Spaces.Dth f z θ)]
  have hDzB : |Work.Spaces.Dz f z θ| ≤ B := by
    nlinarith [abs_nonneg (f z θ), abs_nonneg (Work.Spaces.Dth f z θ)]
  have hDthB : |Work.Spaces.Dth f z θ| ≤ B := by
    nlinarith [abs_nonneg (f z θ), abs_nonneg (Work.Spaces.Dz f z θ)]
  -- unfold `𝓛_Γ^T` once and for all into its five summands
  have hsplit : Work.Coercivity.LGammaT α f z θ
      = (Work.Coercivity.L f z θ
          - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
            * Work.Coercivity.L12f f z)
        - (Work.Coercivity.Transport f z θ
          - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := rfl
  rw [hsplit]
  -- `𝓛 f = f + D_z f - 2f/(1+z)`, bounded by `2B + 2B`
  have hA : |Work.Coercivity.L f z θ| ≤ 4 * B := by
    have hLf : Work.Coercivity.L f z θ
        = f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z) := rfl
    rw [hLf]
    have h1 : |f z θ + Work.Spaces.Dz f z θ - 2 * f z θ / (1 + z)| ≤
        |f z θ + Work.Spaces.Dz f z θ| + |2 * f z θ / (1 + z)| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (f z θ + Work.Spaces.Dz f z θ) (-(2 * f z θ / (1 + z)))
    have h2 : |f z θ + Work.Spaces.Dz f z θ| ≤ |f z θ| + |Work.Spaces.Dz f z θ| :=
      abs_add_le _ _
    have h3 : |2 * f z θ / (1 + z)| ≤ 2 * B := by
      have h4 : |2 * f z θ| ≤ 2 * B := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      exact le_trans (abs_div_le_abs_of_one_le (a := 2 * f z θ) hz1) h4
    linarith
  have hCL : |(2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
      * Work.Coercivity.L12f f z| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hcoef hL12f (abs_nonneg _) hB
  -- `Transport f = 3 D_θ f/(1+z)`, bounded by `3B`
  have hB2 : |Work.Coercivity.Transport f z θ| ≤ 3 * B := by
    have hTe : Work.Coercivity.Transport f z θ
        = 3 * Work.Spaces.Dth f z θ / (1 + z) := rfl
    rw [hTe]
    have h5 : |3 * Work.Spaces.Dth f z θ| ≤ 3 * B := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    exact le_trans (abs_div_le_abs_of_one_le (a := 3 * Work.Spaces.Dth f z θ) hz1) h5
  have hCT : |(Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
      * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hcoef2 hL12T (abs_nonneg _) hB
  -- assemble: `|X₁| ≤ 4B + B²`, `|X₂| ≤ 3B + B²`, `|X₁ - X₂| ≤ |X₁| + |X₂|`
  have hX1 : |Work.Coercivity.L f z θ
      - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z| ≤ 4 * B + B * B := by
    have h := abs_sub_le_abs_add_abs (Work.Coercivity.L f z θ)
      ((2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z)
    linarith [h, hA, hCL]
  have hX2 : |Work.Coercivity.Transport f z θ
      - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0| ≤ 3 * B + B * B := by
    have h := abs_sub_le_abs_add_abs (Work.Coercivity.Transport f z θ)
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
    linarith [h, hB2, hCT]
  have hfin := abs_sub_le_abs_add_abs
    (Work.Coercivity.L f z θ
      - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z)
    (Work.Coercivity.Transport f z θ
      - (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
  linarith [hfin, hX1, hX2]

end Work.FTS.StrongEps.EpsWp
