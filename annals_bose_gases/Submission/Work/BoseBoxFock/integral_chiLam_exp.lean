import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integral_chiLam_exp`

The Fourier transform of the localisation window against the *conjugate* plane
wave: for every `ℓ > 0` and every momentum `k`,

    `∫ χ_Λ(z) e^{-i⟪k,z⟫} dz = ℓ³ χ̂(ℓk)`      (`integral_chiLam_exp`)

(`χ_Λ = BoxData.chiLam ℓ`).  This is FS's first box integral
`∫χ_Λ e^{ik·x} = ℓ³ χ̂(ℓk)` (`Work.BoseB4.BoxData.integral_chiLam_mul_cos`) with
the opposite sign of the plane wave; the extra imaginary part
`-∫ χ_Λ sin⟪k,·⟫` vanishes because `χ_Λ` is even and the sine is odd, so the two
statements are the same.  The proof expands
`e^{-iθ} = cos θ - sin θ · i`, splits the (Bochner) integral into its two real
pieces, kills the sine piece by oddness of the measure `volume` on `ℝ³` and
evaluates the cosine piece with `integral_chiLam_mul_cos`.

The helper lemmas below are stated for a general `BoxData` (or for an arbitrary
odd real function) so that they are reusable elsewhere.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- **Integral of an odd function on `ℝ³` vanishes.**  `volume` on `ℝ³` is
invariant under `z ↦ -z` (`Measure.measurePreserving_neg`), so substituting
`z ↦ -z` turns `∫ f` into `∫ -f = -∫ f`, whence `∫ f = 0`. -/
lemma integral_eq_zero_of_odd {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hodd : ∀ x, f (-x) = - f x) : ∫ x, f x = 0 := by
  have h1 : ∫ x, f (-x) = ∫ x, f x :=
    (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin 3)))).integral_comp
      measurableEmbedding_neg f
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) => f (-x)) = fun x => - f x from funext hodd,
    integral_neg] at h1
  linarith

/-- `e^{-i x} = cos x - i sin x` for a real angle `x`, in the form needed to
split `Complex.exp (-(I * θ))` into its real and imaginary parts. -/
lemma exp_neg_mul_I_ofReal (x : ℝ) :
    Complex.exp (-((x : ℂ) * Complex.I)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * Complex.I := by
  have h : -((x : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- `χ_Λ · sin⟪k,·⟫` is integrable (the sine companion of
`BoxData.integrable_chiLam_mul_cos`): `χ_Λ` is continuous with compact support,
the sine factor is continuous and bounded. -/
lemma integrable_chiLam_mul_sin (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    Integrable fun z => B.chiLam ℓ z * Real.sin (inner ℝ k z) :=
  ((Work.BoseB4.BoxData.chiLam_cont B ℓ).mul
      (Real.continuous_sin.comp (continuous_const.inner continuous_id))).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right
      ((Work.BoseB4.BoxData.boxL_compact B ℓ).of_isClosed_subset
        (isClosed_tsupport _)
        (Work.BoseB4.BoxData.tsupport_chiLam_subset B hℓ)))

/-- `χ_Λ · sin⟪k,·⟫` is odd (`χ_Λ` is even, the sine of an odd argument is odd),
so its integral vanishes. -/
lemma integral_chiLam_mul_sin (B : Work.BoseB4.BoxData) {ℓ : ℝ}
    (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ z, B.chiLam ℓ z * Real.sin (inner ℝ k z) = 0 := by
  refine integral_eq_zero_of_odd (f := fun z => B.chiLam ℓ z * Real.sin (inner ℝ k z)) ?_
  intro z
  rw [Work.BoseB4.BoxData.chiLam_even, inner_neg_right, Real.sin_neg, mul_neg]

/-- **The Fourier transform of the window at `ℓk`.**  The complex pairing of the
rescaled localization function `χ_Λ = chiLam ℓ` with the conjugate plane wave
`e^{-i⟨k,·⟩}` is the (real) box transform `ℓ³ χ̂(ℓk)`: the imaginary part
`∫ χ_Λ sin⟨k,·⟩` vanishes because `χ_Λ` is even and the sine is odd, and
`BoxData.integral_chiLam_mul_cos` (in `Submission.Work.BoseB4.BoxChiScaling`)
computes the real part. -/
lemma integral_chiLam_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) := by
  set B := Work.BoseK15.corpusBox
  have hcos := Work.BoseB4.BoxData.integral_chiLam_mul_cos B hℓ k
  have hsin : ∫ z, B.chiLam ℓ z * Real.sin (inner ℝ k z) = 0 :=
    integral_chiLam_mul_sin B k
  -- `e^{-iθ} = cos θ - i sin θ`
  have hpt : ∀ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)
      = ((B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ)
        - Complex.I * ((B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ) := by
    intro z
    have hI : Complex.exp (-(Complex.I * (inner ℝ k z : ℂ)))
        = (Real.cos (inner ℝ k z) : ℂ) - (Real.sin (inner ℝ k z) : ℂ) * Complex.I := by
      rw [mul_comm Complex.I (inner ℝ k z : ℂ)]
      exact exp_neg_mul_I_ofReal (inner ℝ k z)
    rw [hI]
    push_cast
    ring
  have h1 : Integrable fun z => ((B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ) :=
    (Work.BoseB4.BoxData.integrable_chiLam_mul_cos B hℓ k).ofReal
  have h2 : Integrable fun z => Complex.I * ((B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ) :=
    (integrable_chiLam_mul_sin B hℓ k).ofReal.const_mul Complex.I
  calc ∫ z, Complex.exp (-(Complex.I * (inner ℝ k z : ℂ))) * ((B.chiLam ℓ z : ℝ) : ℂ)
      = ∫ z, (((B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ)) : ℂ)
          - Complex.I * (((B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ)) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z, ((B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ))
          - ∫ z, Complex.I * ((B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ) :=
        integral_sub h1 h2
    _ = ((∫ z, B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ)
          - Complex.I * ((∫ z, B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ) := by
        rw [integral_const_mul,
          show (∫ z, ((B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ))
            = ((∫ z, B.chiLam ℓ z * Real.cos (inner ℝ k z) : ℝ) : ℂ) from integral_ofReal,
          show (∫ z, ((B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ))
            = ((∫ z, B.chiLam ℓ z * Real.sin (inner ℝ k z) : ℝ) : ℂ) from integral_ofReal]
    _ = ((ℓ ^ 3 * B.hatChi (ℓ • k) : ℝ) : ℂ) := by
        rw [hcos, hsin]
        simp

end Work.BoseBoxFock
