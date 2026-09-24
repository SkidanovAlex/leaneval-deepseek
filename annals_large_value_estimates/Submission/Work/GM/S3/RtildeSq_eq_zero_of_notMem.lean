import Mathlib
import Submission.Work.GM.S3.Defs

namespace Work.GM.S3

open Submission.GM

/-- **Support of the smoothing `R̃²`.** If `ψ₁` vanishes off `|x| ≤ c` and `ψ₂` vanishes off
`[a,b]`, then `RtildeSq W N B ψ₁ ψ₂ u = ∫ u', (N B) ψ₁ ((N B)(u-u')) ψ₂ u' ‖Rfun W u'‖²` vanishes
for `u` outside `[a - c/(N B), b + c/(N B)]`: the integrand is nonzero only when `ψ₂ u' ≠ 0` (so
`u' ∈ [a,b]`) and `ψ₁ ((N B)(u-u')) ≠ 0` (so `|u - u'| ≤ c/(N B)`). -/
theorem RtildeSq_eq_zero_of_notMem {ψ₁ ψ₂ : ℝ → ℝ} {c a b : ℝ} (hc : 0 ≤ c)
    (h₁ : ∀ x, ψ₁ x ≠ 0 → |x| ≤ c) (h₂ : ∀ x, ψ₂ x ≠ 0 → x ∈ Set.Icc a b)
    {W : Finset ℝ} {N : ℕ} {B : ℝ} (hB : 0 < (N : ℝ) * B) {u : ℝ}
    (hu : u ∉ Set.Icc (a - c / ((N : ℝ) * B)) (b + c / ((N : ℝ) * B))) :
    RtildeSq W N B ψ₁ ψ₂ u = 0 := by
  -- The integrand vanishes pointwise: a nonzero value would force `u' ∈ [a,b]` and
  -- `|u - u'| ≤ c/(N B)`, i.e. `u ∈ [a - c/(N B), b + c/(N B)]`.
  have key : ∀ u' : ℝ,
      (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2 = 0 := by
    intro u'
    have hcontra : ¬ (ψ₁ ((N : ℝ) * B * (u - u')) ≠ 0 ∧ ψ₂ u' ≠ 0) := by
      rintro ⟨h1ne, h2ne⟩
      have habs : |(N : ℝ) * B * (u - u')| = ((N : ℝ) * B) * |u - u'| := by
        rw [abs_mul, abs_of_pos hB]
      have hle : |u - u'| ≤ c / ((N : ℝ) * B) := by
        rw [le_div_iff₀ hB, mul_comm]
        rw [← habs]
        exact h₁ _ h1ne
      have hu' : u' ∈ Set.Icc a b := h₂ u' h2ne
      have hb' : (u - u') ≤ c / ((N : ℝ) * B) := (abs_le.mp hle).2
      have ha' : -(c / ((N : ℝ) * B)) ≤ (u - u') := (abs_le.mp hle).1
      exact hu ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    by_cases hp : ψ₁ ((N : ℝ) * B * (u - u')) = 0
    · rw [hp]; ring
    · by_cases hq : ψ₂ u' = 0
      · rw [hq]; ring
      · exact absurd ⟨hp, hq⟩ hcontra
  rw [RtildeSq]
  rw [show (fun u' : ℝ =>
        (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2)
      = fun _ => (0 : ℝ) from funext key]
  simp

end Work.GM.S3
