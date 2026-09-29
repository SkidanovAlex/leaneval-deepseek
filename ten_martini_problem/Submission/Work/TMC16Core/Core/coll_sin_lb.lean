import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

/-- For `x ∈ [-π, π]` we have `|sin x| = sin |x|`. -/
lemma abs_sin_eq_sin_abs {x : ℝ} (h1 : -Real.pi ≤ x) (h2 : x ≤ Real.pi) :
    |Real.sin x| = Real.sin |x| := by
  rcases lt_or_ge 0 x with h | h
  · rw [abs_of_nonneg (le_of_lt h),
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt h) h2)]
  · have hsx : Real.sin x ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le h h1
    rw [abs_of_nonpos hsx, abs_of_nonpos h, Real.sin_neg]

/-- **Lower bound for one collision term.**  If `fracDist (qₙ α) > 1/(q_{n+1} + qₙ)`,
`fracDist (qₙ α) ≤ 1/q_{n+1}` and `q_{n+1} ≤ e^{β qₙ}`, and if `m ≠ 0`, `|m| ≤ ℓ`,
`10 ℓ qₙ ≤ q_{n+1}`, then `|sin (π · m · qₙ · α)| ≥ e^{-β qₙ}`.
(Here `fracDist x = |x - round x|`.)

Sketch: writing `qₙ α = p + δ` with `p = round (qₙ α) ∈ ℤ` and `|δ| = fracDist (qₙ α)`,
periodicity (`Real.sin_add_int_mul_pi`) gives `|sin (π m qₙ α)| = |sin (π m δ)|`; also
`|m δ| ≤ ℓ · (1/q_{n+1}) ≤ 1/(10 qₙ) ≤ 1/10`, so
`|sin (π m δ)| ≥ (2/π)(π |m| |δ|) ≥ 2 |δ| > 2/(q_{n+1} + qₙ) ≥ 1/q_{n+1} ≥ e^{-β qₙ}`
(`Real.mul_le_sin` for the sine bound; `q_{n+1} ≥ 10 qₙ ≥ qₙ` and `e^{-β qₙ} ≤ 1/q_{n+1}`
from `hβ`). -/
theorem coll_sin_lb {α β : ℝ} {qn qn1 : ℕ} {ℓ : ℕ} {m : ℤ}
    (hℓ : 1 ≤ ℓ) (hq : 1 ≤ qn)
    (hℓb : 10 * (ℓ : ℤ) * (qn : ℤ) ≤ (qn1 : ℤ))
    (hΔlo : 1 / ((qn1 : ℝ) + (qn : ℝ)) < Work.TMC16Core.fracDist ((qn : ℝ) * α))
    (hΔup : Work.TMC16Core.fracDist ((qn : ℝ) * α) ≤ 1 / (qn1 : ℝ))
    (hβ : (qn1 : ℝ) ≤ Real.exp (β * (qn : ℝ)))
    (hm : m ≠ 0) (hmℓ : |m| ≤ (ℓ : ℤ)) :
    Real.exp (-β * (qn : ℝ)) ≤ |Real.sin (Real.pi * ((m : ℝ) * (qn : ℝ) * α))| := by
  -- ### Integrality / positivity bookkeeping
  have hℓ1 : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  have hq1 : (1 : ℤ) ≤ (qn : ℤ) := by exact_mod_cast hq
  have h10qn : 10 * (qn : ℤ) ≤ (qn1 : ℤ) := by nlinarith [hℓb, hℓ1, hq1]
  have hqn_le : (qn : ℤ) ≤ (qn1 : ℤ) := by nlinarith [h10qn]
  have h10ℓ : (10 : ℤ) * (ℓ : ℤ) ≤ (qn1 : ℤ) := by nlinarith [hℓb, hq1]
  have h10_le : (10 : ℤ) ≤ (qn1 : ℤ) := by nlinarith [h10qn, hq1]
  have hqn1_nat : 1 ≤ qn1 := by omega
  have hqn1_pos : (0 : ℝ) < (qn1 : ℝ) := by exact_mod_cast hqn1_nat
  have hqn_leR : (qn : ℝ) ≤ (qn1 : ℝ) := by exact_mod_cast hqn_le
  have h10ℓR : (10 : ℝ) * (ℓ : ℝ) ≤ (qn1 : ℝ) := by exact_mod_cast h10ℓ
  -- ### Write `qn α = p + δ`
  set p : ℤ := round ((qn : ℝ) * α) with hp
  set δ : ℝ := (qn : ℝ) * α - (p : ℝ) with hδdef
  have hδ : Work.TMC16Core.fracDist ((qn : ℝ) * α) = |δ| := by
    rw [Work.TMC16Core.fracDist, hδdef, hp]
  have hδlo : 1 / ((qn1 : ℝ) + (qn : ℝ)) < |δ| := by rw [← hδ]; exact hΔlo
  have hδup : |δ| ≤ 1 / (qn1 : ℝ) := by rw [← hδ]; exact hΔup
  -- ### Periodicity: `|sin (π m qn α)| = |sin (π m δ)|`
  have hper : |Real.sin (Real.pi * ((m : ℝ) * (qn : ℝ) * α))|
      = |Real.sin (Real.pi * ((m : ℝ) * δ))| := by
    have harg : Real.pi * ((m : ℝ) * (qn : ℝ) * α)
        = Real.pi * ((m : ℝ) * δ) + ((m * p : ℤ) : ℝ) * Real.pi := by
      rw [hδdef, hp]
      push_cast
      ring
    rw [harg, Real.sin_add_int_mul_pi, abs_mul, abs_zpow]
    simp
  -- ### Size bounds on `m` and `m δ`
  have hmR : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have hmRle : |(m : ℝ)| ≤ (ℓ : ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast hmℓ
  have hmδ_ge : |δ| ≤ |(m : ℝ) * δ| := by
    rw [abs_mul]
    calc |δ| = 1 * |δ| := (one_mul _).symm
      _ ≤ |(m : ℝ)| * |δ| := mul_le_mul_of_nonneg_right hmR (abs_nonneg δ)
  have hmδ_le : |(m : ℝ) * δ| ≤ 1 / 10 := by
    rw [abs_mul]
    have h1 : |(m : ℝ)| * |δ| ≤ (ℓ : ℝ) * (1 / (qn1 : ℝ)) :=
      mul_le_mul hmRle hδup (abs_nonneg δ) (by positivity)
    have h2 : (ℓ : ℝ) * (1 / (qn1 : ℝ)) ≤ 1 / 10 := by
      rw [mul_one_div, div_le_iff₀ hqn1_pos]
      linarith [h10ℓR]
    linarith [h1, h2]
  -- ### Sine lower bound via `Real.mul_le_sin`
  set u : ℝ := Real.pi * ((m : ℝ) * δ) with hu
  have hu_abs : |u| = Real.pi * |(m : ℝ) * δ| := by
    rw [hu, abs_mul, abs_of_pos Real.pi_pos]
  have hu_le : |u| ≤ Real.pi / 2 := by
    rw [hu_abs]; nlinarith [Real.pi_pos, hmδ_le]
  have hsin_abs : |Real.sin u| = Real.sin |u| := by
    apply abs_sin_eq_sin_abs
    · have := (abs_le.mp hu_le).1; linarith [Real.pi_pos]
    · have := (abs_le.mp hu_le).2; linarith [Real.pi_pos]
  have hsin_ge : 2 * |δ| ≤ |Real.sin u| := by
    rw [hsin_abs]
    have hml : (2 / Real.pi) * |u| ≤ Real.sin |u| := Real.mul_le_sin (abs_nonneg u) hu_le
    have h2 : 2 * |δ| ≤ (2 / Real.pi) * |u| := by
      rw [hu_abs]
      have heq : (2 / Real.pi) * (Real.pi * |(m : ℝ) * δ|) = 2 * |(m : ℝ) * δ| := by
        field_simp
      rw [heq]
      linarith [hmδ_ge]
    linarith [h2, hml]
  -- ### Assemble: `exp (-β qn) ≤ 1/qn1 ≤ 2|δ| ≤ |sin (π m qn α)|`
  have hexp : Real.exp (-β * (qn : ℝ)) ≤ 1 / (qn1 : ℝ) := by
    rw [show -β * (qn : ℝ) = -(β * (qn : ℝ)) by ring, Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le hqn1_pos hβ
  have hchain : 1 / (qn1 : ℝ) ≤ 2 * |δ| := by
    have hpos : (0 : ℝ) < (qn1 : ℝ) + (qn : ℝ) := by positivity
    have h1 : 1 / (qn1 : ℝ) ≤ 2 / ((qn1 : ℝ) + (qn : ℝ)) := by
      rw [div_le_div_iff₀ hqn1_pos hpos]
      linarith [hqn_leR]
    have h2 : 2 / ((qn1 : ℝ) + (qn : ℝ)) < 2 * |δ| := by
      have he : 2 / ((qn1 : ℝ) + (qn : ℝ)) = 2 * (1 / ((qn1 : ℝ) + (qn : ℝ))) :=
        (mul_one_div 2 _).symm
      rw [he]; linarith [hδlo]
    linarith [h1, h2]
  rw [hper]
  exact le_trans (le_trans hexp hchain) hsin_ge

end Work.TMC16Core.Core
