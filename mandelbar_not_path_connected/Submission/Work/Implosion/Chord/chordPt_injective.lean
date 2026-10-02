import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Chord
import Submission.Work.Implosion.Chord.chordPt_re_im

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

open Complex

/-- In the ideal case `a = iλ` with `h` real-valued and non-vanishing on the cut `ℓ`,
the chord parametrisation `(t,s) ↦ chordPt (iλ) h t s` is injective on
`(-1,1) × [0,1]`: the imaginary part recovers `t` (it equals `t·λ`), and then the
real part recovers `s` up to the non-zero factor `λ²(1−t²)·Re h(t·a)`. -/
theorem chordPt_injective (lam : ℝ) (h : ℂ → ℂ) (hlam : 0 < lam)
    (hreal : ∀ t : ℝ, (h (cutPt ((lam : ℂ) * I) t)).im = 0)
    (hne : ∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 → h (cutPt ((lam : ℂ) * I) t) ≠ 0)
    {t t' s s' : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (ht' : t' ∈ Set.Ioo (-1 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs' : s' ∈ Set.Icc (0 : ℝ) 1)
    (heq : chordPt ((lam : ℂ) * I) h t s = chordPt ((lam : ℂ) * I) h t' s') :
    t = t' ∧ s = s' := by
  -- The imaginary part of a chord point is `t·λ`, so it detects `t`.
  have him : ∀ (u v : ℝ), (chordPt ((lam : ℂ) * I) h u v).im = u * lam :=
    fun u v => (chordPt_re_im lam h u v (hreal u)).2
  have him_eq : t * lam = t' * lam := by
    have h := congrArg Complex.im heq
    rwa [him t s, him t' s'] at h
  have htt : t = t' := mul_right_cancel₀ (ne_of_gt hlam) him_eq
  -- The real part of a chord point is `s·λ²(1−t²)·Re h(t·a)`, so it detects `s`.
  have hre : ∀ (u v : ℝ), (chordPt ((lam : ℂ) * I) h u v).re
      = v * lam ^ 2 * (1 - u ^ 2) * (h (cutPt ((lam : ℂ) * I) u)).re :=
    fun u v => (chordPt_re_im lam h u v (hreal u)).1
  have hre_eq : s * lam ^ 2 * (1 - t ^ 2) * (h (cutPt ((lam : ℂ) * I) t)).re
      = s' * lam ^ 2 * (1 - t' ^ 2) * (h (cutPt ((lam : ℂ) * I) t')).re := by
    have h := congrArg Complex.re heq
    rwa [hre t s, hre t' s'] at h
  rw [htt.symm] at hre_eq
  have h1mt2 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hrh : (h (cutPt ((lam : ℂ) * I) t)).re ≠ 0 := by
    intro h0
    exact hne t ht (Complex.ext (by simpa using h0) (by simpa using hreal t))
  have hstep1 : s * lam ^ 2 * (1 - t ^ 2) = s' * lam ^ 2 * (1 - t ^ 2) :=
    mul_right_cancel₀ hrh hre_eq
  have hstep2 : s * lam ^ 2 = s' * lam ^ 2 :=
    mul_right_cancel₀ (ne_of_gt h1mt2) hstep1
  exact ⟨htt, mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt hlam)) hstep2⟩

end Work.Implosion.Chord
