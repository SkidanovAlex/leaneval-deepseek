import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

open Complex

/-- `germPt a h` is continuous on any interval `(0, ε)` on which `h` is continuous at `t`
and at `λ t`, and where the denominator `h (λ t) - h t` does not vanish. -/
lemma continuousOn_germPt {a : ℝ} {h : ℂ → ℂ} {ε : ℝ}
    (hcont : ∀ t ∈ Set.Ioo 0 ε, ContinuousAt h (t : ℂ) ∧ ContinuousAt h ((eqLam a : ℂ) * t))
    (hne : ∀ t ∈ Set.Ioo 0 ε, h ((eqLam a : ℂ) * t) ≠ h t) :
    ContinuousOn (germPt a h) (Set.Ioo 0 ε) := by
  intro t ht
  -- continuity of the two ingredients `t ↦ h t` and `t ↦ h (λ t)` at `t`
  have hMt : ContinuousAt (fun s : ℝ => h (s : ℂ)) t :=
    (hcont t ht).1.comp (continuous_ofReal.continuousAt)
  have hNt : ContinuousAt (fun s : ℝ => h ((eqLam a : ℂ) * (s : ℂ))) t :=
    (hcont t ht).2.comp (x := t) ((continuous_const.mul continuous_ofReal).continuousAt)
  have hden : h ((eqLam a : ℂ) * (t : ℂ)) - h (t : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (hne t ht)
  -- the two quotients appearing in `germPt`
  have hF : ContinuousAt
      (fun s : ℝ => (a : ℂ) * h ((eqLam a : ℂ) * (s : ℂ)) /
        (h ((eqLam a : ℂ) * (s : ℂ)) - h (s : ℂ))) t :=
    (continuousAt_const.mul hNt).div (hNt.sub hMt) hden
  have hG : ContinuousAt
      (fun s : ℝ => (a : ℂ) * h (s : ℂ) * h ((eqLam a : ℂ) * (s : ℂ)) /
        (h ((eqLam a : ℂ) * (s : ℂ)) - h (s : ℂ))) t :=
    ((continuousAt_const.mul hMt).mul hNt).div (hNt.sub hMt) hden
  -- take real parts, coerce to `ℂ`, subtract `a/2`, multiply by `I`, add
  have hreF : ContinuousAt
      (fun s : ℝ => ((a : ℂ) * h ((eqLam a : ℂ) * (s : ℂ)) /
        (h ((eqLam a : ℂ) * (s : ℂ)) - h (s : ℂ))).re) t :=
    Complex.continuous_re.continuousAt.comp hF
  have hreG : ContinuousAt
      (fun s : ℝ => ((a : ℂ) * h (s : ℂ) * h ((eqLam a : ℂ) * (s : ℂ)) /
        (h ((eqLam a : ℂ) * (s : ℂ)) - h (s : ℂ))).re) t :=
    Complex.continuous_re.continuousAt.comp hG
  exact ((continuous_ofReal.continuousAt.comp (hreF.sub continuousAt_const)).add
      ((continuous_ofReal.continuousAt.comp hreG).mul continuousAt_const)).continuousWithinAt

end Work.EQ
