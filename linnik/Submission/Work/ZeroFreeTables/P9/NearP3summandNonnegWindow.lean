import Mathlib
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.P3Bounds

namespace Work.ZeroFreeTables.P9

/-- Inside the `δ`-window (and at a genuine zero) the side condition `α ≤ β` of the
pointwise bound `Re P₃(α/(β+it)) ≥ 0` is exactly the hypothesis `λ₁ ≤ (1-Re u)L`,
with `β = Re((s-u)L) = a + (1-Re u)L`. -/
theorem NearP3summandNonnegWindow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {L a lam₁ δ : ℝ} (hL : 0 < L) (hα : 0 < a + lam₁) {s : ℂ}
    (hs : s.re = 1 + a / L)
    (hwin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → lam₁ ≤ (1 - u.re) * L)
    (u : ℂ) : 0 ≤ Work.ZeroFreeTables.P9.nearP3summand N L χ s a lam₁ δ u := by
  rw [nearP3summand_eq_P3]
  by_cases hzm : Work.LinnikContract.zeroMult χ u = 0
  · simp [hzm]
  · have hzm' : Work.LinnikContract.zeroMult χ u ≠ 0 := hzm
    by_cases hni : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · have hwin' : lam₁ ≤ (1 - u.re) * L := hwin u hzm' hni
      have hy : a + lam₁ ≤ ((s - u) * (L:ℂ)).re := by
        rw [show ((s - u) * (L:ℂ)).re = (s.re - u.re)*L by
          simp [Complex.mul_re, Complex.sub_re]]
        rw [hs]
        have hLne : L ≠ 0 := ne_of_gt hL
        have hh : (1 + a/L - u.re)*L = a + (1-u.re)*L := by field_simp; ring
        rw [hh]; linarith
      have hP3 : 0 ≤ (Work.ZeroFreeTables.P3 ((↑a + ↑lam₁) / ((s - u) * (↑L)))).re := by
        have h := PhiG_nonneg (x := a + lam₁)
          (y := ((s - u) * (L:ℂ)).re) (t := ((s - u) * (L:ℂ)).im) hα hy
        have heq : PhiG (a + lam₁)
              ((s - u) * (L:ℂ)).re ((s - u) * (L:ℂ)).im
            = (Work.ZeroFreeTables.P3 ((↑a + ↑lam₁) / ((s - u) * (↑L)))).re := by
          unfold PhiG
          rw [Complex.re_add_im]
          norm_num
        rwa [heq] at h
      have hind : 0 ≤ nearInd s δ u := nearInd_nonneg s δ u
      have hm : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by positivity
      exact mul_nonneg (mul_nonneg hm hind) hP3
    · simp [nearInd, hni]

end Work.ZeroFreeTables.P9
