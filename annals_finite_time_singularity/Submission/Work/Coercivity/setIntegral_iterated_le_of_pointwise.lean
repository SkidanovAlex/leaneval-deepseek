import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.Coercivity

set_option autoImplicit false

/-- Pointwise coercivity of the iterated set integral: if `0 ≤ a` and `a ≤ C * g` on `s × t`,
`C ≥ 0`, and the `θ`-slice of `g` is integrable on `t` for every `z ∈ s` while `z ↦ ∫ θ in t, g z θ`
is integrable on `s`, then `∫ z in s, ∫ θ in t, a z θ ≤ C * ∫ z in s, ∫ θ in t, g z θ`.

The subtlety is that nothing is assumed about `a` beyond the pointwise bounds (no measurability,
no integrability); we use `MeasureTheory.integral_mono_of_nonneg`, which does not require the
smaller function to be integrable, together with the `integral_undef` convention
(`∫ f = 0` for non-integrable `f`) inside the inner integral. -/
theorem setIntegral_iterated_le_of_pointwise {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (a g : ℝ → ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hintg : (∀ z ∈ s, MeasureTheory.IntegrableOn (fun θ => g z θ) t) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in t, g z θ) s)
    (ha : ∀ z ∈ s, ∀ θ ∈ t, 0 ≤ a z θ)
    (hpt : ∀ z ∈ s, ∀ θ ∈ t, a z θ ≤ C * g z θ) :
    ∫ z in s, ∫ θ in t, a z θ ≤ C * ∫ z in s, ∫ θ in t, g z θ := by
  have hψint : Integrable (fun z => ∫ θ in t, g z θ) (volume.restrict s) := hintg.2
  -- The pointwise bound on the inner integrals.
  have hinner : ∀ z ∈ s, (∫ θ in t, a z θ) ≤ C * (∫ θ in t, g z θ) := by
    intro z hz
    by_cases hint : IntegrableOn (fun θ => a z θ) t
    · -- honest case: monotonicity of the integral on the `θ`-slice
      have hCg : IntegrableOn (fun θ => C * g z θ) t := (hintg.1 z hz).const_mul C
      have hae : ∀ᵐ θ ∂(volume.restrict t), a z θ ≤ C * g z θ := by
        filter_upwards [ae_restrict_mem ht] with θ hθ
        exact hpt z hz θ hθ
      calc ∫ θ in t, a z θ ≤ ∫ θ in t, C * g z θ := integral_mono_ae hint hCg hae
        _ = C * ∫ θ in t, g z θ := by rw [integral_const_mul]
    · -- non-integrable slice: the inner integral is `0` by convention
      rw [integral_undef hint]
      rcases eq_or_lt_of_le hC with hC0 | hCpos
      · rw [← hC0]; simp
      · have hψnn : 0 ≤ ∫ θ in t, g z θ := by
          apply setIntegral_nonneg ht
          intro θ hθ
          have h1 : 0 ≤ C * g z θ := le_trans (ha z hz θ hθ) (hpt z hz θ hθ)
          exact (mul_nonneg_iff_of_pos_left hCpos).mp h1
        exact mul_nonneg hC hψnn
  -- The same bound, but only a.e. and together with nonnegativity, for the outer integral.
  have hphi_nonneg : ∀ z ∈ s, 0 ≤ ∫ θ in t, a z θ := by
    intro z hz
    by_cases hint : IntegrableOn (fun θ => a z θ) t
    · exact setIntegral_nonneg ht (fun θ hθ => ha z hz θ hθ)
    · rw [integral_undef hint]
  have hCs : Integrable (fun z => C * ∫ θ in t, g z θ) (volume.restrict s) := hψint.const_mul C
  have hle_ae : (fun z => ∫ θ in t, a z θ) ≤ᵐ[volume.restrict s]
      (fun z => C * ∫ θ in t, g z θ) := by
    filter_upwards [ae_restrict_mem hs] with z hz
    exact hinner z hz
  have hnneg : 0 ≤ᵐ[volume.restrict s] (fun z => ∫ θ in t, a z θ) := by
    filter_upwards [ae_restrict_mem hs] with z hz
    exact hphi_nonneg z hz
  calc ∫ z in s, ∫ θ in t, a z θ
      = ∫ z, (∫ θ in t, a z θ) ∂(volume.restrict s) := rfl
    _ ≤ ∫ z, C * (∫ θ in t, g z θ) ∂(volume.restrict s) :=
        integral_mono_of_nonneg hnneg hCs hle_ae
    _ = C * ∫ z in s, ∫ θ in t, g z θ := by rw [integral_const_mul]

end Work.Coercivity
