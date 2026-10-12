import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.fourier_convScale_scaling
import Submission.Work.OneBodyKin.kinFT_conv3_chi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.fourier_convScale`

The Fourier transform of the scaled bump autocorrelation `convScale ℓ = (χ⋆χ)(·/ℓ)` at the
momentum `q` is `ℓ³` times the square of the bump's Fourier profile at `ℓq`:

    `∫_z (χ⋆χ)(z/ℓ) · e^{−i⟪q,z⟫} dz = ℓ³ · profHat(ℓq)²`.

This is the `(χ⋆χ)`-Fourier input of the moving-box kinetic bridge.  The computation is split
into two independent pieces, both proved in their own modules:

* `fourier_convScale_scaling` — the scaling change of variables `z = ℓ • w` (Jacobian `ℓ³`),
  reducing the integral to `ℓ³ · kinFT (χ⋆χ) (ℓq)`;
* `kinFT_conv3_chi` — the convolution theorem for `kinFT`, `kinFT (χ⋆χ) p = (profHat p)²`.

No `(2π)`-normalisation appears: with the `p`-convention `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`
and the unnormalised convolution `conv3`, the convolution theorem is multiplicativity on the
nose (`Real.fourier_mul_convolution_eq`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

theorem fourier_convScale {ℓ : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.convScale ℓ z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = (ℓ : ℂ) ^ 3 * (((Work.OneBodyKin.profHat (ℓ • q) : ℝ)) : ℂ) ^ 2 := by
  rw [fourier_convScale_scaling hℓ q, kinFT_conv3_chi (ℓ • q)]

end Work.OneBodyKin
