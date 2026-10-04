import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.pd_fourierExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `integral_normSq_seriesFun`: the `L²` norm of a Fourier series from its coefficients

Layer A of the STE Fourier toolkit.  For a coefficient family
`d : (ι → ℤ) → ℂ` in `ℓ¹(ℤ^ι)`, the `L²` norm squared over the half open unit cube
`unitCube = (0,1]^ι` of the Fourier series `seriesFun d x = Σ_m d m · exp (2πi m·x)` is the
`ℓ²` norm squared of the coefficients:

  `∫_{unitCube} ‖seriesFun d ‖² = ∑'_m ‖d m‖²`.

This is the `L²`-isometry (one half of Parseval) for series-representable functions, deduced
from the character-orthogonality pairing `integral_seriesFun_mul_conj`

  `∫_{unitCube} seriesFun c x * star (seriesFun d x) dx = ∑'_m c m * star (d m)`

by choosing `c = d`: since `z * star z = ↑(‖z‖²)` (`RCLike.mul_conj`), the concrete pairing
`∑'_m d m * star (d m)` is the coercion of `∑'_m ‖d m‖²`.

No completeness of `L²` and no Parseval for arbitrary functions is used: the series is
absolutely convergent (`hd`, the `ℓ¹` hypothesis), so every step is elementary.  Note that the
`ℓ¹` hypothesis is essential on both sides: without summability the coefficients would not be
in `ℓ²` at all.  (`‖d m‖ ≤ Σ_l ‖d l‖` makes `Σ_m ‖d m‖²` summable, so `tsum` is not junk
here; indeed no separate summability of the squares is needed, `Complex.ofReal_tsum` is
unconditional.)
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

/-- The pointwise identity `‖z‖² = z * star z` at the level of the complex numbers, i.e.
the coercion `↑(‖z‖²)` is the product of `z` with its conjugate. -/
private lemma ofReal_normSq_eq_mul_star (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem integral_normSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : (ι → ℤ) → ℂ) (hd : Summable (fun m : ι → ℤ => ‖d m‖)) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.seriesFun d x‖ ^ 2
      = ∑' m : ι → ℤ, ‖d m‖ ^ 2 := by
  classical
  -- Both sides are real; it suffices to compare their coercions to `ℂ`.
  refine Complex.ofReal_injective ?_
  calc ((∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.seriesFun d x‖ ^ 2 : ℝ) : ℂ)
      -- push the coercion into the integrand
      = ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ((‖Work.Diff.STE.seriesFun d x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal.symm
    -- replace `↑‖seriesFun d x‖²` by the pairing with the conjugate
    _ = ∫ x in Work.Diff.STE.unitCube (ι := ι),
          (Work.Diff.STE.seriesFun d x * star (Work.Diff.STE.seriesFun d x)) := by
          apply integral_congr_ae
          filter_upwards with x
          exact ofReal_normSq_eq_mul_star _
    -- character orthogonality for the absolutely convergent series
    _ = ∑' m : ι → ℤ, d m * star (d m) :=
          Work.Diff.STE.integral_seriesFun_mul_conj d d hd hd
    -- `d m * star (d m)` is the coercion of `‖d m‖²`
    _ = ((∑' m : ι → ℤ, ‖d m‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_tsum]
          exact tsum_congr (fun m => (ofReal_normSq_eq_mul_star (d m)).symm)

end Work.Diff.STE
