import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

set_option linter.unusedVariables false in
/-- When `h t` and `h (λ t)` are both real (`h t = β`, `h (λ t) = γ`), the definition of
`germPt` reduces to an explicit real formula. -/
lemma germPt_of_real {a β γ : ℝ} {h : ℂ → ℂ} {t : ℝ}
    (ht : h (t : ℂ) = (β : ℂ)) (htl : h ((eqLam a : ℂ) * t) = (γ : ℂ))
    (hden : γ - β ≠ 0) :
    germPt a h t =
      (((a * γ / (γ - β) - a / 2 : ℝ)) : ℂ) +
        (((a * β * γ / (γ - β) : ℝ)) : ℂ) * Complex.I := by
  unfold germPt
  rw [ht, htl]
  have e1 : ((a : ℂ) * (γ : ℂ) / ((γ : ℂ) - (β : ℂ))).re = a * γ / (γ - β) := by
    have h : ((a : ℂ) * (γ : ℂ) / ((γ : ℂ) - (β : ℂ))) = ((a * γ / (γ - β) : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [h, Complex.ofReal_re]
  have e2 : ((a : ℂ) * (β : ℂ) * (γ : ℂ) / ((γ : ℂ) - (β : ℂ))).re = a * β * γ / (γ - β) := by
    have h : ((a : ℂ) * (β : ℂ) * (γ : ℂ) / ((γ : ℂ) - (β : ℂ))) =
        ((a * β * γ / (γ - β) : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [h, Complex.ofReal_re]
  rw [e1, e2]

end Work.EQ
