import Mathlib
import Submission.Work.CKFinal.LineDecay.LamExtension
import Submission.Work.CKFinal.LineDecay.lam_analytic_kfun
import Submission.Work.CKFinal.LineDecay.lam_analytic_khat
import Submission.Work.CKFinal.LineDecay.shift_identity_kfun
import Submission.Work.CKFinal.LineDecay.shift_identity_khat

/-!
# The all-`r` shift identity on the two lines, via analytic continuation (route 1)

`shift_identity_kfun` and `shift_identity_khat` give the identity `F = P₁+P₂+P₃` on
`Re τ = ±1/2` for `λ = π r² > 2π`.  `lam_analytic_kfun`/`lam_analytic_khat` show that both sides
are holomorphic in `λ` on `{z : ℂ | -π < z.re}`, and `eqOn_halfplane_of_eqOn_Ioi` (via
`shift_identity_all_of_large`) upgrades the identity to all real `r`.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Work.CKFinal.LineDecay

/-- `z ↦ e^{cz}` is entire. -/
lemma analyticOnNhd_exp_mul (c : ℂ) : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (c * z)) Set.univ := by
  apply DifferentiableOn.analyticOnNhd
  · intro z _
    fun_prop
  · exact isOpen_univ

/-- **The all-`r` shift identity, un-hatted and hatted, for one dimension.** -/
theorem all_identities_route1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (hy : 12 ≤ τ.im) :
    ((∀ r : ℝ, Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
        = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
          + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
          + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ d) r τ)
      ∧ (∀ r : ℝ, Work.CKFinal.paperLayerK (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) r τ
        = Work.CKFinal.P1 (Work.Kernels.Khat ℓ d) r τ
          + Work.CKFinal.P2 (Work.Kernels.Khat ℓ d) r τ
          + Work.CKFinal.P3 (Work.Kernels.Khat ℓ d) r τ)) := by
  obtain ⟨hAk, hRk⟩ := lam_analytic_kfun ℓ d hd τ hτ hy
  obtain ⟨hAt, hRt⟩ := lam_analytic_khat ℓ d hd τ hτ hy
  have hAt' : AnalyticOnNhd ℂ
      (Work.CKFinal.LHSzHat (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ)
      {z : ℂ | -(Real.pi) < z.re} := by
    have hfun : Work.CKFinal.LHSzHat (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ
        = fun z : ℂ => Work.CKFinal.LHSz (Work.Kernels.Khat ℓ d) (Work.CKFinal.Ghat ℓ d) τ z
            - Complex.exp (Complex.I * (τ : ℂ) * z) := by
      funext z
      simp only [Work.CKFinal.LHSz, Work.CKFinal.LHSzHat]
      ring
    rw [hfun]
    exact hAt.sub ((analyticOnNhd_exp_mul (Complex.I * (τ : ℂ))).mono (Set.subset_univ _))
  exact Work.CKFinal.shift_identity_all_of_large ℓ d hd τ hτ hy
    hAk hRk hAt' hRt
    (fun r hr => shift_identity_kfun ℓ d hd τ hr hτ hy)
    (fun r hr => shift_identity_khat ℓ d hd τ hr hτ hy)

end Work.CKFinal.LineDecay
