import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.ZeroFreeTables.P9.NearSummandLemmas
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.lam0w

open scoped Classical BigOperators

/-- **Every summand of `nearP3sum` is non-negative (wide vertical range).**

Same argument as `Work.ZeroFreeTables.P9.nearP3summand_nonneg`, but the a-priori bound on
`s.im` is `|s.im| ≤ 4` rather than `≤ 3`.  That hypothesis is used only to place a zero in the
window inside the range `|u.im| ≤ 10` to which `hmin` applies: from the window membership
`‖1 + i·Im s - u‖ ≤ δ` we get `|u.im| ≤ |s.im| + δ ≤ 4 + δ < 5 ≤ 10`. -/
theorem nearP3summand_nonneg_wide {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ1 : δ < 1)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 4)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (u : ℂ) : 0 ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u := by
  rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3]
  by_cases hz : Work.LinnikContract.zeroMult χ u = 0
  · simp [hz]
  by_cases hn : Work.ZeroFreeTables.P9.nearInd s δ u = 0
  · simp [hn]
  have hw : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra hc
    exact hn (by rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hc])
  have him : |u.im| ≤ 10 := by
    have h2 : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
    have h1 : |s.im - u.im| ≤ δ := by
      have h1' := Complex.abs_im_le_norm ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)
      rw [h2] at h1'
      exact h1'.trans hw
    have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
      calc |u.im| = |s.im - (s.im - u.im)| := by
            congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
    linarith
  have hlam : lam₁ ≤ (1 - u.re) * L := hmin u hz him
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Work.ZeroFreeTables.P9.nearInd_nonneg s δ u))
    (Work.ZeroFreeTables.P9.P3term_nonneg_of_min hL ha hlam₁ hsre hlam)

end Work.ZeroFreeTables.lam0w
