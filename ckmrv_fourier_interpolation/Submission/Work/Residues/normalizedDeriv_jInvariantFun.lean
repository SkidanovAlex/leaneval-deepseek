/-
# The normalized derivative of the `j`-invariant

We prove Ramanujan's identity
  `D j = -(E₄² E₆)/Δ`,  where `j = E₄³/Δ` and `D = (2πi)⁻¹ d/dτ`

is the normalized derivative `Derivative.normalizedDerivOfComplex`.

The proof is the classical one:

* `Δ = (E₄³ - E₆²)/1728` (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`), so `D Δ = E₂ Δ`
  follows by combining Ramanujan's identities `D E₄ = (E₂E₄ - E₆)/3` and
  `D E₆ = (E₂E₆ - E₄²)/2` (`Work.Modular.ramanujan_E4`, `Work.Modular.ramanujan_E6`);
* the quotient rule for `D` applied to `j = E₄³/Δ` then gives
  `D j = (D(E₄³)Δ - E₄³ DΔ)/Δ² = ((E₂E₄³ - E₄²E₆)Δ - E₄³E₂Δ)/Δ² = -E₄²E₆/Δ`.

The helper lemmas (`normalizedDerivOfComplex_div`, the quotient rule for `D`, and
`normalizedDerivOfComplex_DeltaFun`, the identity `D Δ = E₂ Δ`) are kept `private` to this
file so that they cannot collide with the parallel developments of the same facts elsewhere
in the workspace.

## Main result

* `Work.Residues.normalizedDeriv_jInvariantFun` : `D j = -(E₄²E₆)/Δ`.
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Modular.ramanujan_E4
import Submission.Work.Modular.ramanujan_E6

noncomputable section

open UpperHalfPlane ModularForm
open scoped Manifold

namespace Work.Residues

/-- `E₄` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_E4Fun : MDiff Work.Kernels.E4Fun :=
  ModularFormClass.holo ModularForm.E₄

/-- `E₆` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_E6Fun : MDiff Work.Kernels.E6Fun :=
  ModularFormClass.holo ModularForm.E₆

/-- `Δ` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_DeltaFun : MDiff Work.Kernels.DeltaFun :=
  CuspFormClass.holo CuspForm.discriminant

/-- `Δ` does not vanish on `ℍ`. -/
private lemma DeltaFun_ne_zero (z : ℍ) : Work.Kernels.DeltaFun z ≠ 0 := by
  simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero z

/-- **Quotient rule for the normalized derivative** `D = (2πi)⁻¹ d/dτ`:
for holomorphic `F`, `G` with `G` nowhere zero,
`D (F/G) = (D F · G - F · D G)/G²`. -/
private lemma normalizedDerivOfComplex_div {F G : ℍ → ℂ} (hF : MDiff F) (hG : MDiff G)
    (hz : ∀ z, G z ≠ 0) :
    Derivative.normalizedDerivOfComplex (F / G)
      = fun z => (Derivative.normalizedDerivOfComplex F z * G z
          - F z * Derivative.normalizedDerivOfComplex G z) / (G z) ^ 2 := by
  funext z
  have hFz : DifferentiableAt ℂ (F ∘ ↑ofComplex) (z : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz : DifferentiableAt ℂ (G ∘ ↑ofComplex) (z : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  have hzne : (G ∘ ↑ofComplex) (z : ℂ) ≠ 0 := by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz z
  simp only [Derivative.normalizedDerivOfComplex]
  rw [show ((F / G) ∘ ↑ofComplex) = (F ∘ ↑ofComplex) / (G ∘ ↑ofComplex) from rfl,
    deriv_div hFz hGz hzne,
    Function.comp_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  ring

/-- **Ramanujan's identity for the discriminant:** `D Δ = E₂ Δ`. -/
private lemma normalizedDerivOfComplex_DeltaFun :
    Derivative.normalizedDerivOfComplex Work.Kernels.DeltaFun
      = fun z => Work.Kernels.E2Fun z * Work.Kernels.DeltaFun z := by
  have hE4 := mdifferentiable_E4Fun
  have hE6 := mdifferentiable_E6Fun
  -- `Δ = 1728⁻¹ • (E₄³ - E₆²)`.
  have hfun : Work.Kernels.DeltaFun
      = (1728 : ℂ)⁻¹ • (Work.Kernels.E4Fun ^ 3 - Work.Kernels.E6Fun ^ 2) := by
    funext z
    rw [show Work.Kernels.DeltaFun z
        = (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2) / 1728 from
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]
    simp [Pi.smul_apply, div_eq_inv_mul]
  rw [hfun, Derivative.normalizedDerivOfComplex_smul _ _
        ((hE4.pow 3).sub (hE6.pow 2)),
      Derivative.normalizedDerivOfComplex_sub _ _ (hE4.pow 3) (hE6.pow 2),
      Derivative.normalizedDerivOfComplex_pow _ 3 hE4,
      Derivative.normalizedDerivOfComplex_pow _ 2 hE6,
      Work.Modular.ramanujan_E4, Work.Modular.ramanujan_E6]
  funext z
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  field_simp
  ring

theorem normalizedDeriv_jInvariantFun :
    Derivative.normalizedDerivOfComplex Work.Kernels.jInvariantFun
      = fun z => -(Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z)
          / Work.Kernels.DeltaFun z := by
  have hE4 := mdifferentiable_E4Fun
  rw [show Work.Kernels.jInvariantFun
        = Work.Kernels.E4Fun ^ 3 / Work.Kernels.DeltaFun from rfl,
    normalizedDerivOfComplex_div (hE4.pow 3) mdifferentiable_DeltaFun DeltaFun_ne_zero,
    Derivative.normalizedDerivOfComplex_pow _ 3 hE4,
    Work.Modular.ramanujan_E4]
  funext z
  rw [show Derivative.normalizedDerivOfComplex Work.Kernels.DeltaFun z
      = Work.Kernels.E2Fun z * Work.Kernels.DeltaFun z from
    congr_fun normalizedDerivOfComplex_DeltaFun z]
  have hz0 : Work.Kernels.DeltaFun z ≠ 0 := DeltaFun_ne_zero z
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
  field_simp
  ring

end Work.Residues
