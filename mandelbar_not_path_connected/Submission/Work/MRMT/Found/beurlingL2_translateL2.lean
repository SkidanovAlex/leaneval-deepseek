/-
Work.MRMT.Found — the Beurling transform commutes with translations.

`beurlingL2` is the `L²` Fourier multiplier with symbol `beurlingSymbol ξ = ξ̄/ξ`, and it is
defined by choice from `Beurling.beurling_l2_isometry`, so the only available information about
it is the isometry property and the Fourier-side identity `fourier_beurlingL2`.  We prove that
it commutes with translations of `L²(ℂ)` by first computing the Fourier transform of a
translation: on the Fourier side, translation by `t` becomes multiplication by the unimodular
function `transChar t ξ = 𝐞 ⟪-t, ξ⟫`.  Since multiplication operators commute, the two
multipliers commute and the result follows from injectivity of the Fourier transform.

The proof follows the same density pattern as `Work.MRMT.Beurling.Hilbert.fourier_star`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal FourierTransform SchwartzMap

namespace Work.MRMT.Found

/-! ## The Fourier multiplier of a translation -/

/-- The unimodular function `ξ ↦ 𝐞 ⟪-t, ξ⟫`, which is the Fourier multiplier implementing
translation by `t`. -/
noncomputable def transChar (t : ℂ) : ℂ → ℂ := fun ξ => (Real.fourierChar (inner ℝ (-t) ξ) : ℂ)

theorem continuous_transChar (t : ℂ) : Continuous (transChar t) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

theorem aestronglyMeasurable_transChar (t : ℂ) :
    AEStronglyMeasurable (transChar t) (volume : Measure ℂ) :=
  (continuous_transChar t).aestronglyMeasurable

theorem norm_transChar_le_one (t : ℂ) :
    ∀ᵐ ξ ∂(volume : Measure ℂ), ‖transChar t ξ‖ ≤ 1 := by
  filter_upwards with ξ
  simp only [transChar]
  exact le_of_eq (Circle.norm_coe _)

/-! ## Translation of a Schwartz function -/

/-- Precomposition with the translation `w ↦ w - t` on the Schwartz space of `ℂ`. -/
noncomputable def schwartzTranslate (t : ℂ) : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz (K := 1) ℝ (g := fun w : ℂ => w - t) (by fun_prop)
    (by intro x y; simp)

theorem schwartzTranslate_apply (t : ℂ) (g : 𝓢(ℂ, ℂ)) :
    ⇑(schwartzTranslate t g) = ⇑g ∘ (fun w : ℂ => w - t) := rfl

/-- The Fourier transform turns translation of a Schwartz function into multiplication by
`transChar t`. -/
theorem fourier_schwartzTranslate (t : ℂ) (g : 𝓢(ℂ, ℂ)) (ξ : ℂ) :
    (𝓕 (schwartzTranslate t g)) ξ = transChar t ξ * (𝓕 g) ξ := by
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℂ) (⇑(schwartzTranslate t g)) ξ
    = transChar t ξ * VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℂ) (⇑g) ξ
  rw [show (⇑(schwartzTranslate t g)) = ⇑g ∘ (fun v : ℂ => v + (-t)) from rfl]
  have h := VectorFourier.fourierIntegral_comp_add_right (e := 𝐞) (μ := volume) (L := innerₗ ℂ)
    (f := ⇑g) (v₀ := -t)
  rw [h]
  simp only [transChar, Circle.smul_def, smul_eq_mul]
  rfl

/-- On the Schwartz space, the `L²` translation agrees with `schwartzTranslate`. -/
theorem translateL2_schwartz (t : ℂ) (g : 𝓢(ℂ, ℂ)) :
    translateL2 t (g.toLp 2 (volume : Measure ℂ))
      = (schwartzTranslate t g).toLp 2 (volume : Measure ℂ) := by
  rw [show g.toLp 2 (volume : Measure ℂ)
      = MemLp.toLp ⇑g (g.memLp 2 (volume : Measure ℂ)) from rfl]
  rw [show translateL2 t (MemLp.toLp ⇑g (g.memLp 2 (volume : Measure ℂ)))
      = Lp.compMeasurePreserving (fun w : ℂ => w - t) (measurePreserving_sub_right volume t)
          (MemLp.toLp ⇑g (g.memLp 2 (volume : Measure ℂ))) from rfl]
  rw [Lp.toLp_compMeasurePreserving]
  rw [show (schwartzTranslate t g).toLp 2 (volume : Measure ℂ)
      = MemLp.toLp (⇑g ∘ fun w : ℂ => w - t)
          ((schwartzTranslate t g).memLp 2 (volume : Measure ℂ)) from rfl]

/-- `SchwartzMap.toLp_fourier_eq` stated for the explicit `L²` Fourier transform
`Lp.fourierTransformₗᵢ`. -/
theorem fourier_toLp (f : 𝓢(ℂ, ℂ)) :
    (Lp.fourierTransformₗᵢ ℂ ℂ) (f.toLp 2 (volume : Measure ℂ))
      = (𝓕 f).toLp 2 (volume : Measure ℂ) :=
  SchwartzMap.toLp_fourier_eq f

/-- The Fourier-side identity of the previous lemmas, as an equality in `L²(ℂ)`. -/
theorem fourier_translateL2_schwartz (t : ℂ) (g : 𝓢(ℂ, ℂ)) :
    (Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t (g.toLp 2 (volume : Measure ℂ)))
      = mulL2 (transChar t) (aestronglyMeasurable_transChar t) (norm_transChar_le_one t)
          ((Lp.fourierTransformₗᵢ ℂ ℂ) (g.toLp 2 (volume : Measure ℂ))) := by
  rw [translateL2_schwartz, fourier_toLp (schwartzTranslate t g), fourier_toLp g]
  apply Lp.ext
  filter_upwards [mulL2_apply_ae (transChar t) (aestronglyMeasurable_transChar t)
      (norm_transChar_le_one t) ((𝓕 g).toLp 2 (volume : Measure ℂ)),
    SchwartzMap.coeFn_toLp (𝓕 (schwartzTranslate t g)) 2 (volume : Measure ℂ),
    SchwartzMap.coeFn_toLp (𝓕 g) 2 (volume : Measure ℂ)] with ξ h1 h2 h3
  rw [h1, h2, h3]
  exact fourier_schwartzTranslate t g ξ

/-! ## The Fourier transform of a translation on `L²(ℂ)` -/

theorem fourier_translateL2 (t : ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    (((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume]
      fun ξ => transChar t ξ *
        (((Lp.fourierTransformₗᵢ ℂ ℂ) f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) ξ := by
  have hdense : DenseRange (fun g : 𝓢(ℂ, ℂ) => g.toLp 2 (volume : Measure ℂ)) :=
    SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := ℂ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℂ))
      (by norm_num)
  have hmain : ((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t f) : Lp ℂ 2 (volume : Measure ℂ))
      = mulL2 (transChar t) (aestronglyMeasurable_transChar t) (norm_transChar_le_one t)
          ((Lp.fourierTransformₗᵢ ℂ ℂ) f) := by
    refine DenseRange.induction_on (p := fun u =>
        ((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t u) : Lp ℂ 2 (volume : Measure ℂ))
          = mulL2 (transChar t) (aestronglyMeasurable_transChar t) (norm_transChar_le_one t)
              ((Lp.fourierTransformₗᵢ ℂ ℂ) u)) hdense f ?_ ?_
    · exact isClosed_eq
        ((Lp.fourierTransformₗᵢ ℂ ℂ).continuous.comp (translateL2 t).continuous)
        (((mulL2 (transChar t) (aestronglyMeasurable_transChar t)
            (norm_transChar_le_one t)).continuous).comp (Lp.fourierTransformₗᵢ ℂ ℂ).continuous)
    · intro g
      exact fourier_translateL2_schwartz t g
  rw [hmain]
  exact mulL2_apply_ae (transChar t) (aestronglyMeasurable_transChar t)
    (norm_transChar_le_one t) ((Lp.fourierTransformₗᵢ ℂ ℂ) f)

/-! ## The commutation with the Beurling transform -/

theorem beurlingL2_translateL2 (t : ℂ)
    (f : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    beurlingL2 (translateL2 t f) = translateL2 t (beurlingL2 f) := by
  apply (Lp.fourierTransformₗᵢ ℂ ℂ).injective
  apply Lp.ext
  have hA : ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (beurlingL2 (translateL2 t f))) =ᵐ[volume]
      fun ξ => beurlingSymbol ξ * (transChar t ξ * ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) f) ξ) := by
    filter_upwards [fourier_beurlingL2 (translateL2 t f), fourier_translateL2 t f] with ξ h1 h2
    rw [h1, h2]
  have hB : ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) (translateL2 t (beurlingL2 f))) =ᵐ[volume]
      fun ξ => transChar t ξ * (beurlingSymbol ξ * ⇑((Lp.fourierTransformₗᵢ ℂ ℂ) f) ξ) := by
    filter_upwards [fourier_translateL2 t (beurlingL2 f), fourier_beurlingL2 f] with ξ h1 h2
    rw [h1, h2]
  filter_upwards [hA, hB] with ξ ha hb
  rw [ha, hb]
  ring

end Work.MRMT.Found
