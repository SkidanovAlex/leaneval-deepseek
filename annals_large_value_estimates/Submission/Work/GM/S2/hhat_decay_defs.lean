import Mathlib
import Submission.Work.GM.S2.Defs

/-!
# Vocabulary for GM Lemma 4.3(2) and the tail sum (the `S₂` area)

`hhat t ξ = 𝓕 (h_t) ξ` where `h_t(u) = w(u)² u^{it}` (GM (4.4)).  Writing the Fourier
kernel out, the integrand is the product of the *amplitude*

`hhatAmp ξ u = w(u)² e^{-2πiξu}`   (`hhatKernel` below is the kernel `e^{-2πiξu}`)

and the *phase* `hhatPhase t u = u^{it} = exp (i t log u)`.  So, on the support `[1,2]`,

`hhat t ξ = ∫ u, hhatAmp ξ u * hhatPhase t u`  (`hhat_eq_integral_amp` in `hhat_decay.lean`).

On `[1,2]` the phase is `C^∞` with all derivatives of modulus `1`, and `j` integrations by
parts against the phase multiply the integral by `∏_{k=1}^{j} (k + i t)⁻¹` and replace
`hhatAmp ξ` by its `j`-th derivative, which costs `(1+|ξ|)^j`.  This is GM Lemma 4.3(2).
-/

namespace Work.GM.S2

open Complex

/-- The Fourier kernel `u ↦ e^{-2πiξu}`, the character appearing in
`Real.fourier_real_eq_integral_exp_smul`. -/
noncomputable def hhatKernel (ξ u : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * u * ξ) * Complex.I)

/-- The phase `u ↦ u^{it} = exp (i t log u)`. -/
noncomputable def hhatPhase (t u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ))

/-- The amplitude `g_ξ(u) = w(u)² e^{-2πiξu}` of GM Lemma 4.3(2). -/
noncomputable def hhatAmp (ξ u : ℝ) : ℂ :=
  ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ) * hhatKernel ξ u

end Work.GM.S2
