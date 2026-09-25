import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_discFourier_l1

/-!
# The bridge between `ftLp` and `discFourier` for absolutely summable sequences

For `ρ ∈ ℓ¹(ℤ)` the discrete Fourier transform `discFourier ρ ξ = Σ'_n ρ n · e^{2πi n ξ}` is an
absolutely (indeed uniformly) convergent series, hence a bounded measurable function on `𝕋`, hence
an element of `L²(𝕋)`; and it is the `L²`-function whose `n`-th Fourier coefficient is `ρ n`.  Since
`ftLp ρ hρ2` is by construction the (unique) `L²`-function with those coefficients, the two agree
almost everywhere: `ftLp ρ hρ2 =ᵐ discFourier ρ`.

The coefficient of `discFourier ρ` is computed by the `ℓ¹` Parseval identity
`tsum_mul_conj_eq_integral_discFourier_l1` applied to `ρ` and the Kronecker delta at `n` (whose
`discFourier` is the character `fourier n`, `discFourier_single`).
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- `discFourier ρ` is measurable: it is a pointwise sum of measurable functions. -/
theorem measurable_discFourier (ρ : ℤ → ℂ) : Measurable (discFourier ρ) := by
  unfold discFourier
  exact Measurable.tsum fun n => measurable_const.mul (map_continuous (fourier n)).measurable

/-- **`discFourier ρ ∈ L²(𝕋)` for `ρ ∈ ℓ¹(ℤ)`.**  The series converges uniformly, so
`‖discFourier ρ‖_∞ ≤ Σ_n ‖ρ n‖` and the circle carries a probability measure. -/
theorem memLp_discFourier {ρ : ℤ → ℂ} (hρ : Summable fun m => ‖ρ m‖) :
    MemLp (discFourier ρ) 2 (AddCircle.haarAddCircle (T := 1)) := by
  refine MemLp.of_bound (measurable_discFourier ρ).aestronglyMeasurable (∑' n : ℤ, ‖ρ n‖) ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  have hs : Summable fun n : ℤ => ρ n * fourier n θ :=
    Summable.of_norm_bounded hρ fun n => by rw [norm_mul, norm_fourier_apply', mul_one]
  calc ‖discFourier ρ θ‖ = ‖∑' n : ℤ, ρ n * fourier n θ‖ := rfl
    _ ≤ ∑' n : ℤ, ‖ρ n * fourier n θ‖ := norm_tsum_le_tsum_norm hs.norm
    _ = ∑' n : ℤ, ‖ρ n‖ := tsum_congr fun n => by rw [norm_mul, norm_fourier_apply', mul_one]

/-- **The `m`-th Fourier coefficient of `discFourier ρ` for `ρ ∈ ℓ¹(ℤ)`:**
`∫_𝕋 𝓕ρ(θ) · conj (e^{2πi m θ}) dθ = ρ m`.  This is the `ℓ¹` Parseval identity
`tsum_mul_conj_eq_integral_discFourier_l1` applied to `ρ` and the Kronecker delta at `m`, whose
discrete Fourier transform is the character `fourier m`. -/
theorem integral_discFourier_mul_star_fourier {ρ : ℤ → ℂ} (hρ : Summable fun m => ‖ρ m‖)
    (m : ℤ) :
    ∫ θ : Circle, discFourier ρ θ * star (fourier m θ) ∂AddCircle.haarAddCircle = ρ m := by
  have hδ : Summable fun n : ℤ => ‖(if n = m then (1 : ℂ) else 0)‖ := by
    refine summable_of_ne_finset_zero (s := {m}) ?_
    intro n hn
    have hnm : n ≠ m := by simpa using hn
    simp [hnm]
  have h := tsum_mul_conj_eq_integral_discFourier_l1 (h := ρ)
    (k := fun n : ℤ => if n = m then (1 : ℂ) else 0) hρ hδ
  have hlhs : (∑' n : ℤ, ρ n * star (if n = m then (1 : ℂ) else 0)) = ρ m := by
    rw [tsum_eq_single m (fun n hn => by rw [if_neg hn, star_zero, mul_zero])]
    simp
  rw [hlhs] at h
  have hrhs : (∫ ξ : Circle, discFourier ρ ξ *
        star (discFourier (fun n : ℤ => if n = m then (1 : ℂ) else 0) ξ)
        ∂AddCircle.haarAddCircle)
      = ∫ ξ : Circle, discFourier ρ ξ * star (fourier m ξ) ∂AddCircle.haarAddCircle := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show discFourier ρ ξ * star (discFourier (fun n : ℤ => if n = m then (1 : ℂ) else 0) ξ)
      = discFourier ρ ξ * star (fourier m ξ)
    rw [discFourier_single]
  rw [hrhs] at h
  exact h.symm

/-- **The bridge between the two Fourier formulations for absolutely summable sequences.**  For
`ρ ∈ ℓ¹(ℤ)` (hence `ρ ∈ ℓ²(ℤ)`), the `L²(𝕋)` Fourier transform `ftLp ρ hρ2` is a.e. equal to the
absolutely convergent series `discFourier ρ = ∑'_n ρ n · e^{2πi n ·}` of `FreqArc.lean`; so a
support condition stated for `discFourier` (as in `BandLimited.lean`) implies `HasFreqSupport` (as
used by the band-limited `ℓ²` results).

Proof route: both are `L²` functions whose `n`-th Fourier coefficient is `ρ n`: the coefficient of
`ftLp ρ hρ2` is `ρ n` (`ftLp_coeff`), and that of `discFourier ρ` is
`∫ θ, discFourier ρ θ · conj (e_n θ) dθ = ρ n` (term-by-term integration of the absolutely
convergent series, `MeasureTheory.integral_tsum` and the orthonormality of the characters). -/
theorem ftLp_eq_discFourier {ρ : ℤ → ℂ} (hρ : Summable fun m => ‖ρ m‖) (hρ2 : Memℓp ρ 2) :
    (ftLp ρ hρ2 : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle] discFourier ρ := by
  have hmem := memLp_discFourier hρ
  -- `discFourier ρ` and `ftLp ρ hρ2` have the same Fourier coefficients
  have hcoeff : ∀ m : ℤ,
      inner ℂ (fourierBasis (T := 1) m) (MemLp.toLp (discFourier ρ) hmem) = ρ m := by
    intro m
    have hcoe : (fun θ : Circle =>
          (fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) θ)
        =ᵐ[AddCircle.haarAddCircle] ⇑(fourier m) := by
      simpa using (coeFn_fourierLp (T := 1) 2 (n := m))
    rw [MeasureTheory.L2.inner_def]
    have hsplit : (fun θ : Circle =>
          inner ℂ (((fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) θ)
            ((MemLp.toLp (discFourier ρ) hmem : Circle → ℂ) θ))
        =ᵐ[AddCircle.haarAddCircle] fun θ : Circle => discFourier ρ θ * star (fourier m θ) := by
      filter_upwards [hcoe, MemLp.coeFn_toLp hmem] with θ h1 h2
      rw [h1, h2]
      simp [RCLike.inner_apply]
    rw [integral_congr_ae hsplit]
    exact integral_discFourier_mul_star_fourier hρ m
  -- hence the two `L²` classes coincide, since `fourierBasis` is a Hilbert basis
  have hLp : MemLp.toLp (discFourier ρ) hmem = ftLp ρ hρ2 := by
    have hx : (⟨ρ, hρ2⟩ : ℓ²(ℤ, ℂ)) =
        (fourierBasis (T := 1)).repr (MemLp.toLp (discFourier ρ) hmem) := by
      refine Subtype.ext ?_
      funext m
      rw [HilbertBasis.repr_apply_apply]
      exact (hcoeff m).symm
    rw [ftLp]
    exact (((fourierBasis (T := 1)).repr.symm_apply_eq).mpr hx).symm
  rw [← hLp]
  exact MemLp.coeFn_toLp hmem

end Work.BourgainPlan.IonescuWainger
