import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- The autocorrelation (overlap) of the sliding cutoff `χ_{B(u)}` with its translate by `z`:

    `autocorr ℓ d u z = ∫_x χ_{B(u)}(x)·χ_{B(u)}(x − z)`.

Its value at `z = 0` is the sliding `χ_{B(u)}²`-mass `Work.SmallBoxSliding.chiMass`. -/
noncomputable def autocorr {M : ℕ} (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
    * Submission.BoseGases.chiSmallB M ℓ d u (x - z)

/-- The localised pair kernel with numerator `f`, written on the product space in the *lag*
variable `z = x − y`:

    `psiPairKernel M ℓ d u f (x,z) = χ_{B(u)}(x)·(f(z)/E(z))·χ_{B(u)}(x − z)`,

where `E(z) = (χ_M⋆χ_M)(z/(ℓd))·(χ⋆χ)(z/ℓ)` is the product of the two convolution scales.

This is the integrand whose `(x,y)`-form is `wSmallPair M ℓ d u f` (unfolded by
`Work.BoseFixB1.wSmallPair_eq_chi_mul`). -/
noncomputable def psiPairKernel (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Submission.BoseGases.chiSmallB M ℓ d u p.1
    * (f p.2 / (Submission.BoseGases.convScaleSmall M (ℓ * d) p.2
        * Submission.BoseGases.convScale ℓ p.2))
    * Submission.BoseGases.chiSmallB M ℓ d u (p.1 - p.2)

@[simp] lemma psiPairKernel_apply (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x z : EuclideanSpace ℝ (Fin 3)) :
    psiPairKernel M ℓ d u f (x, z)
      = Submission.BoseGases.chiSmallB M ℓ d u x
          * (f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
          * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := rfl

@[simp] lemma autocorr_apply {M : ℕ} (ℓ d : ℝ) (u z : EuclideanSpace ℝ (Fin 3)) :
    autocorr (M := M) ℓ d u z
      = ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
          * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := rfl

/-- **Unfolding of `wSmallPair`** (a local copy of `Work.BoseFixB1.wSmallPair_eq_chi_mul`, whose
module `Submission.Work.BoseFixB1.w2_sub_w1_pointwise` cannot be imported together with
`Submission.Work.BoseFixB1.perBoxF_flat` because of a pre-existing name collision in the corpus):
the localised kernel is the `χ_B`-sandwich of the numerator divided by the product of the two
convolution scales. -/
theorem wSmallPair_eq_kernel (M : ℕ) (ℓ d : ℝ) (u x y : EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Submission.BoseGases.wSmallPair M ℓ d u f x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
          * (f (x - y) / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              * Submission.BoseGases.convScale ℓ (x - y)))
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  rw [div_div]

/-- The nested-division form of `wSmallScaled M c f z / convScale ℓ z` is the single quotient by
the product of the two convolution scales. -/
lemma wSmallScaled_div_convScale_eq (M : ℕ) (ℓ d : ℝ)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wSmallScaled M (ℓ * d) f z / Submission.BoseGases.convScale ℓ z
      = f z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
          * Submission.BoseGases.convScale ℓ z) := by
  simp only [Submission.BoseGases.wSmallScaled]
  rw [div_div]

end Work.BoseFixB1
