/-
# OffAxis/Rect10_3EndgameClean

The §10 numerical endgame for Heath-Brown's test function `tf72f (6/7)`, in a form whose import
closure avoids the `Work.ZeroFreeTables.G72` name clash (the module `tf72G` defines `G72 : ℝ → ℝ`,
the module `OffAxis/G72Defs` defines `G72 : ℂ → ℂ`, so the two can never be imported together).

`Rect10_3RealF2Complex` needs the (10.8)/(10.9) numerics of the complex `G72`, hence the
`G72Defs` side; it therefore cannot import `Rect10_3H_F2`/`Rect10_3H_F1` (which pull `tf72G`).
The two lemmas below are copies of `Work.OffAxis.tf72f_refute_quant_real` and
`Work.OffAxis.rect10_3_endgame_real` of `Rect10_3RealF1`, with the same proofs; their only
imports are the real-analytic inputs of the endgame, which are on the `tf72G`-free side.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds

namespace Work.OffAxis

open scoped Interval

/-- HB §10 endgame, refutation step: (10.7) fails for `λ₁ ≤ 792/1000` by an explicit margin. -/
theorem tf72f_refute_quant_clean (T : Work.ZeroFreeTables.TestFn) (hT : T.x₀ = 7/3)
    (hf : T.f = Work.ZeroFreeTables.tf72f (6/7)) (hF0 : T.F 0 = 8/9)
    (hF6 : T.F (-(6/7)) = 8/5) :
    ∀ l₁ : ℝ, 0 ≤ l₁ → l₁ ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l₁) ≥ 2 * (T.F 0 - T.F (6/7 - l₁)) + 83/9000 := by
  intro l₁ h0 h1
  obtain ⟨hb1, hb2⟩ := Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
  have hb1' : (∫ t in (0:ℝ)..(7/3),
      Real.exp ((792/1000:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t) ≤ 761/500 := by
    have h := hb1; rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have hb2' : (1709/2000 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3),
      Real.exp (-(57/875:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    have h := hb2; rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have eB : T.F (-l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (l₁ * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT hf]
    simp only [neg_mul, neg_neg]
  have eC : T.F (6/7 - l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (-((6/7 - l₁) * t)) * Work.ZeroFreeTables.tf72f (6/7) t :=
    Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (6/7 - l₁)
  have hgap := Work.ZeroFreeTables.tf72f_gap_mono l₁ h0 h1
  have hker : T.F (-l₁) - 2 * T.F (6/7 - l₁) ≤ (761/500 : ℝ) - 2 * (1709/2000 : ℝ) := by
    rw [eB, eC]
    linarith
  have hsub : (761/500 : ℝ) - 2 * (1709/2000 : ℝ) = -(187/1000) := by norm_num
  rw [hsub] at hker
  rw [hF6, hF0]
  linarith

/-- HB §10 endgame: from (10.6) and the moment step, `λ₃ ≥ 6/7 - ε`. -/
theorem rect10_3_endgame_clean (T : Work.ZeroFreeTables.TestFn) (ε' ε s l₁ l₂ l₃ : ℝ)
    (hε : 0 < ε) (hT : T.x₀ = 7/3) (hf : T.f = Work.ZeroFreeTables.tf72f (6/7))
    (hF0 : T.F 0 = 8/9) (hF6 : T.F (-(6/7)) = 8/5)
    (hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)))
    (hs0 : 0 ≤ s) (hse : s ≤ ε/10000) (hs8 : 8 * ε' * T.f 0 ≤ s) (hs83 : s < 83/9000)
    (hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l)
    (href : ∀ l : ℝ, 0 ≤ l → l ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l) ≥ 2 * (T.F 0 - T.F (6/7 - l)) + 83/9000)
    (h106 : T.F (-l₁) - T.F 0 - T.F (l₂ - l₁) - T.F (l₃ - l₁) + T.f 0 * (7/6 + 8 * ε') ≥ 0)
    (h01 : 0 ≤ l₁) (h13 : l₁ ≤ l₃) (h23 : l₂ ≤ l₃) (h36 : l₃ ≤ 6/7) :
    6/7 - ε ≤ l₃ := by
  by_contra hcon
  rw [not_le] at hcon
  have hanti := Work.ZeroFreeTables.TestFn_F_antitone T
  have h2 : T.F (6/7 - l₁) ≤ T.F (l₂ - l₁) := hanti (by linarith [h23])
  have h3 : T.F (6/7 - l₁) ≤ T.F (l₃ - l₁) := hanti (by linarith)
  have h107 : T.F (-(6/7)) - T.F (-l₁) ≤ 2 * (T.F 0 - T.F (6/7 - l₁)) + s := by
    have hk : T.f 0 * (7/6 + 8 * ε') = (3 * T.F 0 - T.F (-(6/7))) + 8 * ε' * T.f 0 := by
      rw [← hL75]; ring
    rw [hk] at h106
    linarith [h2, h3, h106, hs8]
  by_cases hcase : l₁ < 6/7
  · rcases hmom l₁ h01 hcase h107 with hle | hbig
    · have hh := href l₁ h01 hle
      linarith [hh, h107, hs83]
    · linarith
  · push Not at hcase
    linarith

end Work.OffAxis
