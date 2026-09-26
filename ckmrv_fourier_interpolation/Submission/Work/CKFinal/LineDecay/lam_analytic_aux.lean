import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.Asymptotics.Kaxis_local_flat
import Submission.Work.Asymptotics.Kaxis_local_tail
import Submission.Work.Asymptotics.measurable_Kfun_snd_all
import Submission.Work.Asymptotics.DomainD

/-!
# Auxiliary lemmas for `Work.CKFinal.LineDecay.lam_analytic_kfun`

Boundedness of the CKMRV kernel `K^{(d)}` on the contour pieces occurring in the complex-`λ`
form of the identity, and measurability of the corresponding integrands.  The main theorem
`Work.CKFinal.LineDecay.lam_analytic_kfun` (in the file `lam_analytic_kfun.lean`) is proved from
these together with the two general Laplace-transform analyticity lemmas
(`laplace_analytic_compact`, `laplace_analytic_Ici`) and the pointwise bound for the second
difference `Φ` (`Phi_axis_pointwise_bound`).
-/

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane

noncomputable section

/-! ## Elementary facts about the two lines

`τ` on one of the lines `Re τ = ±1/2` with `Im τ ≥ 1` lies in the CKMRV domain `𝒟`. -/

lemma mem_DomainD_of_re_half {τ : UpperHalfPlane}
    (hτ : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : (1 : ℝ) ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD := by
  have him : 0 < τ.im := τ.im_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hτ with h | h <;> rw [h] <;> norm_num
  · rcases hτ with h | h <;> rw [h] <;> norm_num
  · have h := Complex.abs_im_le_norm ((τ : ℂ) - 1 / 2)
    have h2 : ((τ : ℂ) - 1 / 2).im = τ.im := by simp
    rw [h2, abs_of_pos him] at h
    linarith
  · have h := Complex.abs_im_le_norm ((τ : ℂ) + 1 / 2)
    have h2 : ((τ : ℂ) + 1 / 2).im = τ.im := by simp
    rw [h2, abs_of_pos him] at h
    linarith


/-! ## Boundedness and measurability of the kernel on the relevant contour pieces -/

/-- **Flatness at the cusp `z = 0`**: the kernel is bounded on the initial segment `(0,1]` of the
imaginary axis, uniformly in `t` (`Work.Asymptotics.Kaxis_local_flat` for the one-point compact
set `{τ}`). -/
lemma kax_flat_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} (hτD : τ ∈ Work.Asymptotics.DomainD) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Kax (Work.Kernels.Kfun ℓ d) τ 0 t‖ ≤ c := by
  obtain ⟨c, hc, hb⟩ := Work.Asymptotics.Kaxis_local_flat ℓ d hd
    (K := {τ}) isCompact_singleton (by simpa using hτD) 0 le_rfl
  refine ⟨c, hc, fun t ht ht1 => ?_⟩
  rw [Kax_eq_Kaxis]
  simpa using hb τ t (by simp) ht ht1

/-- **The cusp-`i∞` expansion at a fixed `τ`**: `K^{(d)}(τ,it) - Aexp(τ,t)` is
`O((1+t)^M e^{-π(t-T₀)})` for `t ≥ 1` (`Work.Asymptotics.cusp_expansion_of_kernel` for the
one-point compact set `{τ}`). -/
lemma kax_tail_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} (hτD : τ ∈ Work.Asymptotics.DomainD) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Kax (Work.Kernels.Kfun ℓ d) τ 0 t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨C, M, T₀, hC, hM, hT₀, hb⟩ := Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd
    (K := {τ}) isCompact_singleton (by simpa using hτD)
  refine ⟨C, M, T₀, hC, hM, hT₀, fun t ht => ?_⟩
  rw [Kax_eq_Kaxis]
  exact hb τ t (by simp) ht

/-- **Measurability of `t ↦ K^{(d)}(τ, x+it)`** for a fixed real `x`: it is the composition of the
measurable `w ↦ K^{(d)}(τ,w)` with the translation `w ↦ x +ᵥ w`, written as
`Kaxis (fun _ w => K^{(d)}(τ, x +ᵥ w))`. -/
lemma measurable_kax_snd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (x : ℝ) :
    Measurable (fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ x t) := by
  have hK : Measurable (fun w : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ (x +ᵥ w)) :=
    (Work.Asymptotics.measurable_Kfun_snd_all ℓ d hd τ).comp
      (UpperHalfPlane.isometry_real_vadd x).continuous.measurable
  have hEq : (fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ x t)
      = fun t : ℝ => Work.Kernels.Kaxis
          (fun _ w => Work.Kernels.Kfun ℓ d τ (x +ᵥ w)) τ t := by
    funext t
    unfold Kax Work.Kernels.Kaxis
    by_cases h : 0 < t <;> simp [h]
  rw [hEq]
  exact Work.Asymptotics.measurable_Kaxis_of_measurable _ τ hK

/-- **Measurability of the second difference `t ↦ Φ(τ,t)`** on the imaginary axis. -/
lemma measurable_Phi_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Measurable (fun t : ℝ => Phi (Work.Kernels.Kfun ℓ d) τ t) := by
  have h1 := measurable_kax_snd ℓ d hd τ 0
  have h2 := measurable_kax_snd ℓ d hd τ (-1)
  have h3 := measurable_kax_snd ℓ d hd τ 1
  change Measurable ((fun t : ℝ => 2 * Kax (Work.Kernels.Kfun ℓ d) τ 0 t)
    - (fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ (-1) t)
    - (fun t : ℝ => Kax (Work.Kernels.Kfun ℓ d) τ 1 t))
  exact ((h1.const_mul 2).sub h2).sub h3


end

end Work.CKFinal.LineDecay
