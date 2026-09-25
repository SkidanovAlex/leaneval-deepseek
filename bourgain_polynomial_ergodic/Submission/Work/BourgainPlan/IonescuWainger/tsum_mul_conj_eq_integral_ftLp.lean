import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

/-!
# Parseval/Plancherel identity for the `ℓ²(ℤ) ≅ L²(𝕋)` Fourier dictionary

The bilinear pairing `⟨h, k⟩ = Σ_n h n · conj (k n)` on `ℓ²(ℤ)` corresponds, under the unitary
identification `ftLp : ℓ²(ℤ) ≅ L²(𝕋)` (Mathlib's `fourierBasis.repr`), to the `L²` inner product
`∫_𝕋 F · conj G`.  Equivalently, the map `h ↦ ftLp h` is an isometry of inner-product spaces.

This is the standard Parseval identity, transported along `HilbertBasis.repr`; it is the bridge
that lets an `ℓ²`-computation on coefficient sequences be evaluated as a circle integral, and
vice versa.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

theorem tsum_mul_conj_eq_integral_ftLp {h k : ℤ → ℂ} (hh : Memℓp h 2) (hk : Memℓp k 2) :
    ∑' n : ℤ, h n * star (k n)
      = ∫ ξ : Circle, (ftLp h hh : Circle → ℂ) ξ * star ((ftLp k hk : Circle → ℂ) ξ)
          ∂AddCircle.haarAddCircle := by
  -- Step 1: the circle integral is the `L²` inner product `⟪ftLp k, ftLp h⟫`.
  have h1 : (∫ ξ : Circle, (ftLp h hh : Circle → ℂ) ξ * star ((ftLp k hk : Circle → ℂ) ξ)
        ∂AddCircle.haarAddCircle) = inner ℂ (ftLp k hk) (ftLp h hh) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [h1]
  -- Step 2: `ftLp` is `fourierBasis.repr.symm`, an isometry of inner-product spaces.
  change ∑' n : ℤ, h n * star (k n)
      = inner ℂ ((fourierBasis (T := 1)).repr.symm ⟨k, hk⟩)
          ((fourierBasis (T := 1)).repr.symm ⟨h, hh⟩)
  rw [LinearIsometryEquiv.inner_map_map]
  -- Step 3: the `ℓ²` inner product is computed coefficientwise.
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [RCLike.inner_apply, starRingEnd_apply]

end Work.BourgainPlan.IonescuWainger
