import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Decomposition of the real differential on `ℂ` into its `(1,0)` and `(0,1)` parts:
for `u` real-differentiable at `z` and `v : ℂ`,
`du_z(v) = ∂u(z)·v + ∂̄u(z)·\bar v`,
where `dzC u z = ∂u(z) = (1/2)(∂_x u - i∂_y u)` and
`dbarC u z = ∂̄u(z) = (1/2)(∂_x u + i∂_y u)` (see
`Submission/Work/CR/Flat/Cauchy.lean`).  This is the flat analogue of
`Submission.dbar_add_dpartial`. -/
theorem fderiv_eq_dzC_add_dbarC (u : ℂ → ℂ) (z v : ℂ) (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ u z v = dzC u z * v + dbarC u z * star v := by
  unfold Work.CR.Flat.dzC Work.CR.Flat.dbarC
  set D := fderiv ℝ u z with hD
  obtain ⟨a, b, hvab⟩ : ∃ a b : ℝ, v = (a:ℂ) + (b:ℂ) * Complex.I :=
    ⟨v.re, v.im, (Complex.re_add_im v).symm⟩
  subst hvab
  have hstar : star ((a:ℂ) + (b:ℂ) * Complex.I) = (a:ℂ) - (b:ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hDab : D ((a:ℂ) + (b:ℂ) * Complex.I) = D 1 * (a:ℂ) + D Complex.I * (b:ℂ) := by
    have hsplit : (a:ℂ) + (b:ℂ) * Complex.I = (a:ℝ) • (1:ℂ) + (b:ℝ) • (Complex.I) := by
      apply Complex.ext <;> simp
    rw [hsplit, map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
      Complex.real_smul, Complex.real_smul]
    ring
  have key : (1/2 : ℂ) * (D 1 - Complex.I * D Complex.I) * ((a:ℂ) + (b:ℂ) * Complex.I)
        + (1/2 : ℂ) * (D 1 + Complex.I * D Complex.I) * ((a:ℂ) - (b:ℂ) * Complex.I)
      = D 1 * (a:ℂ) + D Complex.I * (b:ℂ) := by
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hstar, hDab, key]

end Work.CR.Flat.Cauchy
