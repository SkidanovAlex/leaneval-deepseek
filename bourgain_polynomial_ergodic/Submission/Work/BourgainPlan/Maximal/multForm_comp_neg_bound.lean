import Mathlib
import Submission.Work.BourgainPlan.Maximal.iwMult_mul

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- **Reflection invariance of a Lebesgue integral along `x ↦ -x`.**

For every (not necessarily measurable) `F : ℝ → ENNReal` the Lebesgue integral of `F ∘ (-·)`
agrees with that of `F`, because `x ↦ -x` is a measure-preserving measurable embedding of
`(ℝ, volume)`. -/
lemma lintegral_comp_neg_enorm (F : ℝ → ENNReal) :
    ∫⁻ x : ℝ, F (-x) = ∫⁻ x : ℝ, F x := by
  have hmap := MeasurableEmbedding.lintegral_map (μ := (volume : Measure ℝ))
    (g := Neg.neg) measurableEmbedding_neg F
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at hmap
  exact hmap.symm

/-- **Reflection of the multiplier symbol.**  Negating the symbol amounts to reflecting the input:
`multForm (fun ξ => m (-ξ)) g x = multForm m (fun y => g (-y)) (-x)`.

Equivalently, if `ρ` denotes the reflection `x ↦ -x`, then
`multForm (m ∘ ρ) g = ρ (multForm m (g ∘ ρ))`. -/
lemma multForm_comp_neg_eq (m g : ℝ → ℂ) :
    multForm (fun ξ => m (-ξ)) g
      = fun x => multForm m (fun y => g (-y)) (-x) := by
  have hfourier : ∀ ξ : ℝ, 𝓕 (fun y => g (-y)) ξ = 𝓕 g (-ξ) := by
    intro ξ
    rw [show (fun y : ℝ => g (-y)) = g ∘ ⇑(LinearIsometryEquiv.neg ℝ) from rfl,
        Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) g ξ]
    simp
  -- the symbol of the reflected multiplier, `φ ξ = m ξ * 𝓕 g (-ξ)`
  have hL : multForm (fun ξ => m (-ξ)) g = 𝓕 (fun ξ => m ξ * 𝓕 g (-ξ)) := by
    rw [multForm_def, Real.fourierInv_eq_fourier_comp_neg]
    congr 1
    funext ξ
    simp
  have hR : (fun x => multForm m (fun y => g (-y)) (-x)) = 𝓕 (fun ξ => m ξ * 𝓕 g (-ξ)) := by
    rw [multForm_def]
    funext x
    rw [Real.fourierInv_eq_fourier_neg]
    simp only [neg_neg]
    rw [show (fun ξ : ℝ => m ξ * 𝓕 (fun y => g (-y)) ξ) = (fun ξ => m ξ * 𝓕 g (-ξ)) from by
      funext ξ; rw [hfourier ξ]]
  rw [hL, hR]

/-- **The `L^q` maximal bound is invariant under negating the multiplier symbol.** -/
theorem multForm_comp_neg_bound {q : ℝ} {m : ℝ → ℂ} {A : ℝ}
    (H : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      ∫⁻ x : ℝ, ‖Work.BourgainPlan.Maximal.multForm m g x‖ₑ ^ q
        ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q) :
    ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      ∫⁻ x : ℝ, ‖Work.BourgainPlan.Maximal.multForm (fun ξ : ℝ => m (-ξ)) g x‖ₑ ^ q
        ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
  intro g hg
  have hg' : MeasureTheory.Integrable (fun y : ℝ => g (-y)) := hg.comp_neg
  have h := H (fun y : ℝ => g (-y)) hg'
  calc ∫⁻ x : ℝ, ‖multForm (fun ξ : ℝ => m (-ξ)) g x‖ₑ ^ q
      = ∫⁻ x : ℝ, ‖multForm m (fun y : ℝ => g (-y)) (-x)‖ₑ ^ q := by
          rw [multForm_comp_neg_eq]
    _ = ∫⁻ x : ℝ, ‖multForm m (fun y : ℝ => g (-y)) x‖ₑ ^ q :=
          lintegral_comp_neg_enorm (fun x : ℝ => ‖multForm m (fun y : ℝ => g (-y)) x‖ₑ ^ q)
    _ ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g (-x)‖ₑ ^ q := h
    _ = ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
          rw [lintegral_comp_neg_enorm (fun x : ℝ => ‖g x‖ₑ ^ q)]

end

end Work.BourgainPlan.Maximal
