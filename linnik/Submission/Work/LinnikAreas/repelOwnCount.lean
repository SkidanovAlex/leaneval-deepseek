import Mathlib

/-!
# The two-exponential matching at the Deuring--Heilbronn threshold

**Restoration note.**  This module was accidentally lost in the in-flight rename of the shared
zero-density chapter (its consumers `Submission.Work.ZeroDensity.Deuring.deuringHeilbronnLogFree`,
`Submission.Work.LinnikAreas.repelOwnZeroCount_le_zeroCountIn` and
`Submission.Work.LinnikAreas.DHHeightNearMax` still import it), which broke the whole
`Work.ZeroDensity` chapter and with it `Submission.Work.LinnikAreas.area6`.  The single lemma below
is restored verbatim: its statement was recovered from the surviving
`.lake/build/lib/lean/Submission/Work/LinnikAreas/repelOwnCount.olean`, and the proof here is
rewritten from scratch.  If the owner of the rename restores their own version, this file can be
dropped.

The content is the elementary matching that turns a *threshold* (nothing below
`c_r·log(1/λ₁)`) plus a *log-free growth* bound (`N t ≤ D·e^{c₃t}`) into a `λ₁`-proportional bound:
on the threshold range one has `t ≥ c_r·log(1/λ₁)`, hence `e^{-t/c_r} ≤ λ₁`, so the growth factor
`e^{c₃t}` can be split as `e^{(c₃+1/c_r)t}·e^{-t/c_r} ≤ e^{(c₃+1/c_r)t}·λ₁`.
-/

namespace Work.LinnikAreas

/-- **The two-exponential matching.**  If `N` vanishes below the threshold `c_r·log(1/λ₁)` and
grows at most as `D·e^{c₃t}`, then `N t ≤ D·λ₁·e^{(c₃+1/c_r)t}` for every `t ≥ 0`. -/
theorem ownCount_le_of_threshold_and_logfree {N : ℝ → ℝ} {lam₁ D c₃ c_r : ℝ}
    (hD : 0 < D) (hlam : 0 < lam₁) (hcr : 0 < c_r)
    (hthr : ∀ t, t < c_r * Real.log (1 / lam₁) → N t = 0)
    (hlog : ∀ t, 0 ≤ t → N t ≤ D * Real.exp (c₃ * t)) :
    ∀ t, 0 ≤ t → N t ≤ D * lam₁ * Real.exp ((c₃ + 1 / c_r) * t) := by
  intro t ht
  by_cases hcase : t < c_r * Real.log (1 / lam₁)
  · rw [hthr t hcase]
    exact mul_nonneg (mul_nonneg hD.le hlam.le) (Real.exp_nonneg _)
  · push_neg at hcase
    have hrpos : 0 < 1 / c_r := by positivity
    have hlog1 : Real.log (1 / lam₁) ≤ (1 / c_r) * t := by
      have h := mul_le_mul_of_nonneg_left hcase hrpos.le
      have h' : (1 / c_r) * (c_r * Real.log (1 / lam₁)) = Real.log (1 / lam₁) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hcr.ne', one_mul]
      rw [h'] at h
      exact h
    have hexp : Real.exp (-(1 / c_r) * t) ≤ lam₁ := by
      have h2 : Real.exp (-(1 / c_r) * t) ≤ Real.exp (-(Real.log (1 / lam₁))) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp (-(Real.log (1 / lam₁))) = lam₁ := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / lam₁), one_div,
          inv_inv]
      rwa [h3] at h2
    calc N t ≤ D * Real.exp (c₃ * t) := hlog t ht
      _ = D * Real.exp ((c₃ + 1 / c_r) * t) * Real.exp (-(1 / c_r) * t) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
      _ ≤ D * Real.exp ((c₃ + 1 / c_r) * t) * lam₁ :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hD.le (Real.exp_nonneg _))
      _ = D * lam₁ * Real.exp ((c₃ + 1 / c_r) * t) := by ring

end Work.LinnikAreas
