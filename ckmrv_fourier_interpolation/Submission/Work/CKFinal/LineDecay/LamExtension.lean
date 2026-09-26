import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.lam_specialise
import Submission.Work.CKFinal.LineDecay.eqOn_halfplane_of_eqOn_Ioi

/-!
# Extending the CKMRV identity from `λ > 2π` to all `λ` (route 1)

The contour-shift identity `F = P₁+P₂+P₃` on the two lines `Re τ = ±1/2` is derived under the
assumption `λ = π r² > 2π`, which is what makes the tails of the shifted contours vanish.  To reach
the remaining range we extend analytically in the complex variable `z = λ`: both sides are
holomorphic on `{z : ℂ | -π < z.re}` (all the parametric integrals converge there), and they agree on
the real interval `(2π, ∞)`.  The identity principle for analytic functions then gives the identity
on the whole half-plane, in particular at `z = π r²` for every real `r`.

This file formalises the reduction: it takes as hypotheses the two holomorphy statements and the
two `λ > 2π` identities (proved elsewhere), and produces the two all-`r` identities that the bound
arguments need.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Work.CKFinal

open UpperHalfPlane

/-- **Route-1 extension of the shift identity.**  Given the holomorphy in `λ` of both sides and the
identity for `λ = π r² > 2π`, the identity holds for every real `r`.

The identity principle used is `Work.CKFinal.LineDecay.eqOn_halfplane_of_eqOn_Ioi`. -/
theorem shift_identity_all_of_large (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (hy : 12 ≤ τ.im)
    (hL : AnalyticOnNhd ℂ
      (LHSz (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ)
      {z : ℂ | -(Real.pi) < z.re})
    (hR : AnalyticOnNhd ℂ (RHSz (Work.Kernels.Kfun ℓ d) τ) {z : ℂ | -(Real.pi) < z.re})
    (hLt : AnalyticOnNhd ℂ (LHSzHat (Work.Kernels.Khat ℓ d) (Ghat ℓ d) τ)
      {z : ℂ | -(Real.pi) < z.re})
    (hRt : AnalyticOnNhd ℂ (RHSz (Work.Kernels.Khat ℓ d) τ) {z : ℂ | -(Real.pi) < z.re})
    (hbig : ∀ r : ℝ, 2 < r ^ 2 → Work.Kernels.gaussTerm τ r
      + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = P1 (Work.Kernels.Kfun ℓ d) r τ + P2 (Work.Kernels.Kfun ℓ d) r τ
        + P3 (Work.Kernels.Kfun ℓ d) r τ)
    (hbigt : ∀ r : ℝ, 2 < r ^ 2 →
      paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
      = P1 (Work.Kernels.Khat ℓ d) r τ + P2 (Work.Kernels.Khat ℓ d) r τ
        + P3 (Work.Kernels.Khat ℓ d) r τ) :
    ((∀ r : ℝ, Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
        = P1 (Work.Kernels.Kfun ℓ d) r τ + P2 (Work.Kernels.Kfun ℓ d) r τ
          + P3 (Work.Kernels.Kfun ℓ d) r τ)
      ∧ (∀ r : ℝ, paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
        = P1 (Work.Kernels.Khat ℓ d) r τ + P2 (Work.Kernels.Khat ℓ d) r τ
          + P3 (Work.Kernels.Khat ℓ d) r τ)) := by
  obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ := Work.CKFinal.LineDecay.lam_specialise ℓ d τ
  have hr_of : ∀ s : ℝ, 2 * Real.pi < s → ∃ r : ℝ, Real.pi * r ^ 2 = s ∧ 2 < r ^ 2 := by
    intro s hs
    have hspos : (0 : ℝ) < s / Real.pi :=
      div_pos (by linarith [Real.pi_pos]) Real.pi_pos
    refine ⟨Real.sqrt (s / Real.pi), ?_, ?_⟩
    · rw [Real.sq_sqrt hspos.le]
      field_simp
    · rw [Real.sq_sqrt hspos.le, lt_div_iff₀ Real.pi_pos]
      linarith
  have hray : ∀ s : ℝ, 2 * Real.pi < s →
      LHSz (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ (s : ℂ)
        = RHSz (Work.Kernels.Kfun ℓ d) τ (s : ℂ) := by
    intro s hs
    obtain ⟨r, hr1, hr2⟩ := hr_of s hs
    rw [← hr1, hsp1 r, hbig r hr2, ← hsp3 r]
  have hrayt : ∀ s : ℝ, 2 * Real.pi < s →
      LHSzHat (Work.Kernels.Khat ℓ d) (Ghat ℓ d) τ (s : ℂ)
        = RHSz (Work.Kernels.Khat ℓ d) τ (s : ℂ) := by
    intro s hs
    obtain ⟨r, hr1, hr2⟩ := hr_of s hs
    rw [← hr1, hsp2 r, hbigt r hr2, ← hsp4 r]
  have hmem : ∀ r : ℝ, -(Real.pi) < ((Real.pi * r ^ 2 : ℝ) : ℂ).re := by
    intro r
    rw [Complex.ofReal_re]
    have : (0 : ℝ) ≤ Real.pi * r ^ 2 := by positivity
    linarith [Real.pi_pos]
  constructor
  · intro r
    have heq := Work.CKFinal.LineDecay.eqOn_halfplane_of_eqOn_Ioi
      (LHSz (Work.Kernels.Kfun ℓ d) (Work.Asymptotics.Gcusp ℓ d) τ)
      (RHSz (Work.Kernels.Kfun ℓ d) τ) hL hR hray ((Real.pi * r ^ 2 : ℝ) : ℂ) (hmem r)
    rw [hsp1 r, hsp3 r] at heq
    exact heq
  · intro r
    have heq := Work.CKFinal.LineDecay.eqOn_halfplane_of_eqOn_Ioi
      (LHSzHat (Work.Kernels.Khat ℓ d) (Ghat ℓ d) τ)
      (RHSz (Work.Kernels.Khat ℓ d) τ) hLt hRt hrayt ((Real.pi * r ^ 2 : ℝ) : ℂ) (hmem r)
    rw [hsp2 r, hsp4 r] at heq
    exact heq

end Work.CKFinal
