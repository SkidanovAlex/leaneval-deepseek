import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.kernel_arcSymbol_torsion

/-!
# The frequency support of the torsion-kernel sequence

Tao's `ortho-apply`(ii) computes the Fourier coefficients of the modulated torsion-arc symbol
`Σ_{β ∈ Σ_{⊆ A}} φ(· - (β + α))`: they are supported on the multiples of `Q_A`, where they equal
`star (fourier m α) · Q_A · K m`, with `K m` the coefficients of `φ` (`kernel_arcSymbol_torsion`).
Since `φ` is supported in the ball of radius `ε`, the symbol is supported in the union of the
translated balls `β + α + B(0, ε)`, `β ∈ Σ_{⊆ A}`.

This file draws the band-limited (`ℓ²`) conclusion: the sequence
`n ↦ star (fourier n α) · Q_A · [Q_A ∣ n] · K n` is band-limited with frequency support in that
union.  The bridge is
`hasFreqSupport_of_coeff`: if the sequence `h` occurs as the sequence of circle Fourier coefficients
of an `L²` function `g` which vanishes off `E`, then `h` has frequency support in `E`.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The `L²` inner product against a Fourier basis element as a circle integral.**  For an `L²`
function `g`, pairing its `L²`-class with the `m`-th character `e^{2πi m ·}` gives the integral of
`g · conj (e^{2πi m ·})`. -/
theorem inner_fourierBasis_toLp {g : Circle → ℂ}
    (hg : MemLp g 2 (AddCircle.haarAddCircle (T := 1))) (m : ℤ) :
    inner ℂ (fourierBasis (T := 1) m) (MemLp.toLp g hg)
      = ∫ θ : Circle, g θ * star (fourier m θ) ∂(AddCircle.haarAddCircle (T := 1)) := by
  rw [MeasureTheory.L2.inner_def]
  have hcoe : (fun θ : Circle =>
        (fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) θ)
      =ᵐ[AddCircle.haarAddCircle] ⇑(fourier m) := by
    simpa using (coeFn_fourierLp (T := 1) 2 (n := m))
  have hsplit : (fun θ : Circle => inner ℂ
        ((fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) θ)
        ((MemLp.toLp g hg : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) θ))
      =ᵐ[AddCircle.haarAddCircle] fun θ : Circle => g θ * star (fourier m θ) := by
    filter_upwards [hcoe, MemLp.coeFn_toLp hg] with θ h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply]
  rw [integral_congr_ae hsplit]

/-- **A sequence realising the Fourier coefficients of a band-limited `L²` function is
band-limited there.**  If `g ∈ L²(𝕋)` vanishes off `E` and `h m = ∫ g · conj (e^{2πi m ·})` for all
`m`, then `h` has frequency support in `E`.

Indeed `ftLp h hh` and the `L²`-class of `g` have the same coefficients along the Hilbert basis
`fourierBasis`, so they coincide, and `g` vanishes off `E`. -/
theorem hasFreqSupport_of_coeff {h : ℤ → ℂ} (hh : Memℓp h 2) {g : Circle → ℂ}
    (hg : MemLp g 2 (AddCircle.haarAddCircle (T := 1)))
    (hcoeff : ∀ m : ℤ,
      ∫ ξ, g ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = h m)
    {E : Set Circle} (hsupp : ∀ ξ, ξ ∉ E → g ξ = 0) :
    HasFreqSupport h hh E := by
  have hinner : ∀ m : ℤ, fourierBasis.repr (MemLp.toLp g hg) m = h m := by
    intro m
    rw [HilbertBasis.repr_apply_apply, inner_fourierBasis_toLp hg m, hcoeff m]
  have hLp : MemLp.toLp g hg = ftLp h hh := by
    refine fourierBasis.repr.injective ?_
    ext m
    rw [hinner m, HilbertBasis.repr_apply_apply, ftLp_coeff]
  have hae : (ftLp h hh : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] g := by
    rw [← hLp]
    exact MemLp.coeFn_toLp hg
  simp only [HasFreqSupport]
  filter_upwards [hae] with θ hθ hmem
  rw [hθ]
  exact hsupp θ hmem

theorem hasFreqSupport_torsionKernel {A : Finset ℕ} (α : Circle) (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    {ε : ℝ} (hφsupp : ∀ ξ : Circle, ε < ‖ξ‖ → φ ξ = 0)
    {hT : Memℓp (fun n : ℤ => star (fourier n α)
        * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n) 2} :
    HasFreqSupport (fun n : ℤ => star (fourier n α)
        * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n) hT
      {ξ : Circle | ∃ β ∈ sigmaSubAFinset A, ξ - (β + α) ∈ Metric.closedBall (0 : Circle) ε} := by
  refine hasFreqSupport_of_coeff hT
    ((memLp_arcSymbol hφ (arcShift (sigmaSubAFinset A) α)).mono_exponent le_top)
    (fun m => kernel_arcSymbol_torsion α φ hφ hK m) ?_
  intro ξ hξ
  rw [arcSymbol_arcShift]
  refine Finset.sum_eq_zero (fun β hβ => ?_)
  have hnb : ξ - (β + α) ∉ Metric.closedBall (0 : Circle) ε := fun h => hξ ⟨β, hβ, h⟩
  have hnorm : ε < ‖ξ - (β + α)‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hnb
    exact not_le.mp hnb
  exact hφsupp _ hnorm

end

end Work.BourgainPlan.IonescuWainger
