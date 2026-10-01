/-
# ZeroFreeTables/P9/NearSummandLemmas — pointwise facts about the `nearP3sum` summand

The summand of `nearP3sum` (`P9/NearSummandDefs.lean`) is non-negative, and so is the bare
`P₃`-term at a zero satisfying the minimality condition `λ₁ ≤ (1-u.re)L`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.P9

/-- **The `P₃`-term at a zero satisfying the minimality condition is non-negative.**
If `λ(u) = (1 - u.re)L ≥ λ₁`, then `Re P₃((a+λ₁)/((s-u)L)) ≥ 0` (`P3Bounds.1`), because
`Re((s-u)L) = a + (1-u.re)L ≥ a + λ₁ = α`. -/
lemma P3term_nonneg_of_min {a lam₁ L : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    {s u : ℂ} (hsre : s.re = 1 + a / L) (hmin : lam₁ ≤ (1 - u.re) * L) :
    0 ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re := by
  have hα : 0 < a + lam₁ := by linarith
  have hle : a + lam₁ ≤ ((s - u) * (L : ℂ)).re := by
    have hre : ((s - u) * (L : ℂ)).re = a + L * (1 - u.re) := by
      rw [Complex.mul_re, Complex.sub_re, hsre]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      field_simp
      ring
    rw [hre]; nlinarith
  have harg : (s - u) * (L : ℂ) = ((((s - u) * (L : ℂ)).re : ℂ)
      + (((s - u) * (L : ℂ)).im : ℂ) * Complex.I) := (Complex.re_add_im _).symm
  rw [harg]
  have h := Work.ZeroFreeTables.P3.P3Bounds.1 (a + lam₁) ((s - u) * (L : ℂ)).re
    ((s - u) * (L : ℂ)).im hα hle
  simpa only [Complex.ofReal_add] using h

/-- **Every summand of `nearP3sum` is non-negative.**  If `zeroMult χ u = 0` the multiplicity
factor kills it, if the `δ`-window indicator vanishes it is `0`, and otherwise `u` lies in the
window, whence `|u.im| ≤ |s.im| + δ ≤ 3 + δ < 10` and `hmin` applies. -/
lemma nearP3summand_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ1 : δ < 1)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ 3)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lam₁ ≤ (1 - u.re) * L)
    (u : ℂ) : 0 ≤ nearP3summand N L χ s a lam₁ δ u := by
  rw [nearP3summand_eq_P3]
  by_cases hz : Work.LinnikContract.zeroMult χ u = 0
  · simp [hz]
  by_cases hn : nearInd s δ u = 0
  · simp [hn]
  have hw : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
    by_contra hc
    exact hn (by rw [nearInd_eq_ite, if_neg hc])
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
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (nearInd_nonneg s δ u))
    (P3term_nonneg_of_min hL ha hlam₁ hsre hlam)

end Work.ZeroFreeTables.P9
