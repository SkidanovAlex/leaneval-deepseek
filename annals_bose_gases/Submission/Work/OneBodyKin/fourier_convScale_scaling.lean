import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.fourier_convScale_scaling`

The scaled convolution kernel `convScale ℓ z = (χ⋆χ)(z/ℓ)` has Fourier transform
`ℓ³ · 𝓕[(χ⋆χ)](ℓ q)` in the paper's `p`-convention `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`:

    `∫_z (χ⋆χ)(z/ℓ) · e^{−i⟪q,z⟫} dz = ℓ³ · kinFT (χ⋆χ) (ℓ q)`.

This is the pure *dilation* statement: the convolution `χ⋆χ` itself is not computed
(that is `kinFT_conv3_chi`/`fourier_convScale`); only the substitution `z = ℓ·w` with
its volume factor `ℓ³` is used, plus `⟪q, ℓ·w⟫ = ⟪ℓ·q, w⟫`.

The substitution is the complex-valued version of the dilation lemmas in
`Submission/KernelIds` (`integral_comp_smul_left`/`integral_comp_smul_right`, which are
stated for real-valued integrands); it is proved here for `ℂ`-valued integrands by the
same measure-theoretic route (`MeasurableEmbedding.integral_map` for the homeomorphism
`x ↦ ℓ • x` and `Measure.map_addHaar_smul` for the volume factor `ℓ⁻³`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## The complex-valued dilation substitution -/

/-- Substituting `s ↦ ℓ • s` in an integral of a `ℂ`-valued function over `ℝ³` brings a
factor `(ℓ³)⁻¹`.  Complex-valued analogue of `Submission.BoseGases.integral_comp_smul_left`. -/
lemma integral_comp_smul_left_complex (g : ℝ³ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ s : ℝ³, g (ℓ • s)) = ((ℓ ^ 3)⁻¹ : ℝ) • (∫ x : ℝ³, g x) := by
  let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.smulOfNeZero ℓ (ne_of_gt hℓ)
  have hfun : (fun x : ℝ³ => ℓ • x) = ⇑φ := by
    funext x
    simp [φ, Homeomorph.smulOfNeZero]
  have hemb : MeasurableEmbedding (fun x : ℝ³ => ℓ • x) := by
    have hemb0 : MeasurableEmbedding ⇑φ := (Homeomorph.measurableEmbedding φ)
    simpa [← hfun] using hemb0
  have hint := hemb.integral_map (μ := (volume : Measure ℝ³)) (g := g)
  calc
    (∫ s : ℝ³, g (ℓ • s)) = ∫ y : ℝ³, g y ∂(Measure.map (fun x : ℝ³ => ℓ • x) volume) :=
      hint.symm
    _ = ∫ y : ℝ³, g y ∂(ENNReal.ofReal ((ℓ ^ 3)⁻¹) • (volume : Measure ℝ³)) := by
        rw [Submission.BoseGases.map_smul_volume3 ℓ hℓ]
    _ = (ENNReal.ofReal ((ℓ ^ 3)⁻¹)).toReal • (∫ x : ℝ³, g x) := by
        rw [integral_smul_measure]
    _ = ((ℓ ^ 3)⁻¹ : ℝ) • (∫ x : ℝ³, g x) := by
        have hnn : 0 ≤ (ℓ ^ 3)⁻¹ := le_of_lt (inv_pos.mpr (pow_pos hℓ 3))
        simp [ENNReal.toReal_ofReal hnn]

/-- Substituting `x = ℓ • s` in an integral of a `ℂ`-valued function over `ℝ³` brings a
factor `ℓ³`.  Complex-valued analogue of `Submission.BoseGases.integral_comp_smul_right`. -/
lemma integral_eq_smul_integral_comp_smul (g : ℝ³ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, g x) = (ℓ ^ 3 : ℝ) • (∫ s : ℝ³, g (ℓ • s)) := by
  have h := integral_comp_smul_left_complex (g := g) hℓ
  rw [h, smul_smul]
  have hne : ℓ ^ 3 ≠ 0 := ne_of_gt (pow_pos hℓ 3)
  rw [mul_inv_cancel₀ hne, one_smul]

/-! ## The scaling identity -/

/-- **The Fourier transform of the scaled convolution.**  With
`convScale ℓ z = (χ⋆χ)(z/ℓ)` and the `p`-convention Fourier transform `kinFT`, the
substitution `z = ℓ•w` gives

    `∫_z (χ⋆χ)(z/ℓ)·e^{−i⟪q,z⟫} dz = ℓ³ · kinFT (χ⋆χ) (ℓ q)`. -/
theorem fourier_convScale_scaling {ℓ : ℝ} (hℓ : 0 < ℓ)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.convScale ℓ z : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))))
      = (ℓ : ℂ) ^ 3 *
          Submission.BoseGases.kinFT
            (fun w : EuclideanSpace ℝ (Fin 3) =>
              ((Submission.BoseGases.conv3 Submission.BoseGases.chi
                Submission.BoseGases.chi w : ℝ) : ℂ)) (ℓ • q) := by
  -- pointwise form of the substitution `z = ℓ•w`
  have hpt : ∀ w : ℝ³,
      (Submission.BoseGases.convScale ℓ (ℓ • w) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q (ℓ • w) : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ (ℓ • q) w : ℂ))) *
        ((Submission.BoseGases.conv3 Submission.BoseGases.chi
          Submission.BoseGases.chi w : ℝ) : ℂ) := by
    intro w
    have hcs : Submission.BoseGases.convScale ℓ (ℓ • w) =
        Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi w := by
      rw [Submission.BoseGases.convScale, smul_smul, inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
    have hinner : inner ℝ q (ℓ • w) = inner ℝ (ℓ • q) w := by
      rw [inner_smul_right, inner_smul_left]
      simp
    rw [hcs, hinner, mul_comm]
  rw [integral_eq_smul_integral_comp_smul
    (g := fun z : ℝ³ => (Submission.BoseGases.convScale ℓ z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) hℓ]
  rw [show (∫ s : ℝ³, (fun z : ℝ³ => (Submission.BoseGases.convScale ℓ z : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))) (ℓ • s))
      = ∫ w : ℝ³, Complex.exp (-(Complex.I * (inner ℝ (ℓ • q) w : ℂ))) *
        ((Submission.BoseGases.conv3 Submission.BoseGases.chi
          Submission.BoseGases.chi w : ℝ) : ℂ) from by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpt]
  rw [Submission.BoseGases.kinFT, Complex.real_smul, Complex.ofReal_pow]

end Work.OneBodyKin
