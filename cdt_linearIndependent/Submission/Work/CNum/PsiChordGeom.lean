import Mathlib
import Submission.Work.CNum.C2_clockwise

namespace Work.CNum

/-!
# `Work.CNum.PsiChordGeom`

The chord of two points of the `ψ_C`-image of the "large" arc `C₂` of the unit circle.

On the arc `θ ∈ (α, 2π - α)` the normalised `C₂`-parametrisation `Vof` is
`Vof θ = -exp (I · Ψ(θ/2))`, `Ψ = C2Psi`.  Since `ψ_C = (3/4) W` and `Vof` is `(3/4) W(e^{iθ})`
rescaled so that `C₂` becomes the unit circle of centre `cenC2` and radius `√rho2sq`,

`ψ_C(e^{iθ}) = √rho2sq · Vof θ + cenC2`,

so the chord between two such points is `√rho2sq` times a unit-circle chord:

`‖ψ_C(e^{iθ₂}) - ψ_C(e^{iθ₁})‖ = √rho2sq · 2 |sin ((Ψ(θ₁/2) - Ψ(θ₂/2))/2)|`.

The exact value `√rho2sq = 115/143` (`sqrt_rho2sq`) turns `2√rho2sq` into `230/143`.
-/

/-- `ψ_C = (3/4) · W` (the definitional identity `√ = (·)^{1/2}`; local copy of
`Work.CNum.psiC_eq_smul_Wfun`). -/
private lemma psiC_eq_smul_Wfun (z : ℂ) :
    Submission.CDTPlan.psiC z = (3 / 4 : ℂ) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- Chord length of two points of the unit circle: `‖e^{ia} - e^{ib}‖ = 2 |sin ((a-b)/2)|`. -/
private lemma chord_norm (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have hfac : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hfac, Complex.norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem PsiChordGeom {θ₁ θ₂ : ℝ}
    (hVof : ∀ θ : ℝ, Work.CNum.alpR ≤ θ → θ ≤ 2 * Real.pi - Work.CNum.alpR →
      Work.CNum.Vof θ = -Complex.exp (Complex.I * (Work.CNum.C2Psi (θ / 2) : ℂ)))
    (h1 : Work.CNum.alpR ≤ θ₁) (h2 : θ₂ ≤ 2 * Real.pi - Work.CNum.alpR) (h12 : θ₁ ≤ θ₂) :
    ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) -
        Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ =
      (230 / 143) *
        |Real.sin ((Work.CNum.C2Psi (θ₁ / 2) - Work.CNum.C2Psi (θ₂ / 2)) / 2)| := by
  have hρ : ((Real.sqrt rho2sq : ℝ) : ℂ) ≠ 0 := by
    rw [sqrt_rho2sq]; norm_num
  have hnorm : ‖((Real.sqrt rho2sq : ℝ) : ℂ)‖ = Real.sqrt rho2sq := by
    rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  -- `ψ_C(e^{iθ}) = √rho2sq · Vof θ + cenC2`, which is just the definition of `Vof`.
  have hpsi : ∀ θ : ℝ, Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) =
      ((Real.sqrt rho2sq : ℝ) : ℂ) * Vof θ + (cenC2 : ℂ) := by
    intro θ
    rw [psiC_eq_smul_Wfun, Vof]
    field_simp
    ring
  have hV₂ : Vof θ₂ = -Complex.exp (Complex.I * (C2Psi (θ₂ / 2) : ℂ)) :=
    hVof θ₂ (le_trans h1 h12) h2
  have hV₁ : Vof θ₁ = -Complex.exp (Complex.I * (C2Psi (θ₁ / 2) : ℂ)) :=
    hVof θ₁ h1 (le_trans h12 h2)
  have hmain : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) -
      Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ))) =
      ((Real.sqrt rho2sq : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (C2Psi (θ₁ / 2) : ℂ)) -
         Complex.exp (Complex.I * (C2Psi (θ₂ / 2) : ℂ))) := by
    rw [hpsi θ₂, hpsi θ₁, hV₂, hV₁]
    ring
  rw [hmain, Complex.norm_mul, hnorm, chord_norm, sqrt_rho2sq]
  ring

end Work.CNum
