import Mathlib

namespace Work.LinnikAreas

/-
# `turanPerTerm`

Let `c_j = 1 - j/(J+1)`.  Assuming the Fejér-kernel lower bound
`-‖w‖/(1+‖w‖) ≤ Σ_{j=1}^J c_j (w^j).re` holds for every `‖w‖ ≤ 1`, we prove the
"per term" consequence

`-2‖u‖/(1+‖u‖) ≤ Σ_{j=1}^J c_j (u^j).re (1 + (v^j).re)`

for all `‖u‖, ‖v‖ ≤ 1`.

The mechanism is the elementary identity (`two_re_mul_re`)

`2 Re(u^j) Re(v^j) = Re((uv)^j) + Re((u conj v)^j)`,

which turns the cross term `Σ_j c_j Re(u^j) Re(v^j)` into the average of two Fejér sums,
one at `w = uv` and one at `w = u conj v`; both have modulus `≤ ‖u‖`, and
`t ↦ t/(1+t)` is increasing, so each of them is `≥ -‖u‖/(1+‖u‖)`.  Adding the bound
`Σ_j c_j Re(u^j) ≥ -‖u‖/(1+‖u‖)` (the hypothesis at `w = u`) gives the claim.

No positivity of `c_j` is needed.
-/

/-- Elementary real-part identity behind the "per term" estimate:
`2 Re(u^j) Re(v^j) = Re((uv)^j) + Re((u * conj v)^j)`. -/
lemma two_re_mul_re (u v : ℂ) (j : ℕ) :
    2 * ((u ^ j).re * (v ^ j).re) = ((u * v) ^ j).re + ((u * star v) ^ j).re := by
  have h1 : ((u * v) ^ j).re = (u ^ j * v ^ j).re := by rw [mul_pow]
  have h2 : ((u * star v) ^ j).re = (u ^ j * star (v ^ j)).re := by rw [mul_pow, star_pow]
  rw [h1, h2, Complex.mul_re, Complex.mul_re]
  have hr : (star (v ^ j) : ℂ).re = (v ^ j).re := Complex.conj_re (v ^ j)
  have hi : (star (v ^ j) : ℂ).im = -(v ^ j).im := Complex.conj_im (v ^ j)
  rw [hr, hi]
  ring

/-- Monotonicity of `t ↦ t/(1+t)` on `[0,∞)`. -/
lemma div_one_add_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (1 + a) ≤ b / (1 + b) := by
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 1 + a) (by linarith : (0:ℝ) < 1 + b)]
  nlinarith

theorem turanPerTerm (J : ℕ) (hJ : 1 ≤ J)
    (hfejer : ∀ w : ℂ, ‖w‖ ≤ 1 →
      -‖w‖ / (1 + ‖w‖) ≤
        ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re)
    (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    -2 * (‖u‖ / (1 + ‖u‖)) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((u ^ j).re * (1 + (v ^ j).re)) := by
  have hterm := fun j : ℕ => two_re_mul_re u v j
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a / (1 + a) ≤ b / (1 + b) :=
    fun a b => div_one_add_mono
  have hnorm_uv : ‖u * v‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖u‖ * ‖v‖ ≤ 1 * 1 := mul_le_mul hu hv (norm_nonneg v) zero_le_one
      _ = 1 := by ring
  have hnorm_usv : ‖u * star v‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    calc ‖u‖ * ‖v‖ ≤ 1 * 1 := mul_le_mul hu hv (norm_nonneg v) zero_le_one
      _ = 1 := by ring
  have h1 := hfejer u hu
  have h3 := hfejer (u * v) hnorm_uv
  have h2 := hfejer (u * star v) hnorm_usv
  rw [neg_div] at h1 h3 h2
  have hle_uv : ‖u * v‖ ≤ ‖u‖ := by
    rw [norm_mul]
    calc ‖u‖ * ‖v‖ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg u)
      _ = ‖u‖ := by ring
  have hle_usv : ‖u * star v‖ ≤ ‖u‖ := by
    rw [norm_mul, norm_star]
    calc ‖u‖ * ‖v‖ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg u)
      _ = ‖u‖ := by ring
  have hS1 : -(‖u‖ / (1 + ‖u‖)) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u * v) ^ j).re := by
    have hm := hmono ‖u * v‖ ‖u‖ (norm_nonneg _) hle_uv
    linarith
  have hS2 : -(‖u‖ / (1 + ‖u‖)) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u * star v) ^ j).re := by
    have hm := hmono ‖u * star v‖ ‖u‖ (norm_nonneg _) hle_usv
    linarith
  have hsplit : (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u^j).re * (1 + (v^j).re)))
      = (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * (u^j).re)
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u^j).re * (v^j).re)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _; ring
  have hdouble : 2 * (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u^j).re * (v^j).re))
      = (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u*v)^j).re)
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u*star v)^j).re) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h := hterm j
    calc 2 * ((1 - (j:ℝ)/(J+1)) * ((u^j).re * (v^j).re))
        = (1 - (j:ℝ)/(J+1)) * (2 * ((u^j).re * (v^j).re)) := by ring
      _ = (1 - (j:ℝ)/(J+1)) * (((u*v)^j).re + ((u*star v)^j).re) := by rw [h]
      _ = (1 - (j:ℝ)/(J+1)) * ((u*v)^j).re
            + (1 - (j:ℝ)/(J+1)) * ((u*star v)^j).re := by ring
  have hT2 : -(‖u‖ / (1 + ‖u‖)) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j:ℝ)/(J+1)) * ((u^j).re * (v^j).re) := by
    linarith [hdouble, hS1, hS2]
  rw [hsplit]
  linarith

end Work.LinnikAreas
