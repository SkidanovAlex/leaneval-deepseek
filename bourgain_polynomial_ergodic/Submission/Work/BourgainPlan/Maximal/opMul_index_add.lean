import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **Shifting the index of a multiplier shifts (modulates) its symbol.**  Evaluating the multiplier with symbol `Φ` at the index `x+u` is the same as applying the multiplier whose symbol is the `L^∞`-class of `ξ ↦ star (fourier u ξ) · Φ ξ` at the index `x`.  This is the "translation of the sequence ↔ modulation of the symbol" half of the modulation symmetries of `opMul` (the other half is `opMul_modSeq`).  (`star` rather than `fourier` is what makes the shift come out as `x+u`.)
Route (either is fine): (a) `opMul_eq_tsum_kernel` (`Work.BourgainPlan.IonescuWainger.opMul_eq_tsum_kernel`, from `norm_opMul_le_of_kernel`): write both sides as `Σ_k f k K(…)` where `K m = ∫ ξ, Φ ξ * star (fourier m ξ)`; the kernel of `mstSymStarLp u Φ` is `m ↦ ∫ ξ, (star (fourier u ξ) * Φ ξ) * star (fourier m ξ) = ∫ ξ, Φ ξ * star (fourier (m+u) ξ)` (character identity `fourier (m+u) = fourier m * fourier u` and `mstSymStarLp_coeFn`), i.e. `K (m+u)`, and then `K (x - k + u) = K (x + u - k)`; or (b) `ftLp_injective`: the Fourier transform of `x ↦ opMul Φ f hf (x+u)` is `ξ ↦ star (fourier u ξ) · 𝓕(Op_Φ f)(ξ)` — prove the "Fourier transform of a shifted index" identity `ftLp (fun x => h (x+u)) = (class of star (fourier u ·)) • ftLp h` from the basis coefficients (`ftLp_coeff`, `HilbertBasis.repr_apply_apply`, orthonormality of `fourierBasis`, `fourier_add`) — and then use `ftLp_opMul` on both sides. -/
theorem opMul_index_add (Φ : MeasureTheory.Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar) (f : ℤ → ℂ)
    (hf : Memℓp f 2) (u x : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul Φ f hf (x + u)
      = Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.mstSymStarLp u Φ) f hf x := by
  -- the coefficient kernel of `Φ`:  `K m = ∫ ξ, Φ ξ · star (fourier m ξ)`
  let K : ℤ → ℂ := fun m => ∫ ξ : mstCirc, (Φ : mstCirc → ℂ) ξ * star (fourier m ξ) ∂mstHaar
  have hker1 : ∀ m : ℤ,
      ∫ ξ : mstCirc, (Φ : mstCirc → ℂ) ξ * star (fourier m ξ) ∂mstHaar = K m :=
    fun m => rfl
  -- the coefficient kernel of `mstSymStarLp u Φ` is `m ↦ K (m + u)`
  have hker2 : ∀ m : ℤ,
      ∫ ξ : mstCirc, ((mstSymStarLp u Φ : MeasureTheory.Lp ℂ ⊤ mstHaar) : mstCirc → ℂ) ξ
        * star (fourier m ξ) ∂mstHaar = K (m + u) := by
    intro m
    have hcoe := mstSymStarLp_coeFn u Φ
    have h1 : ∫ ξ : mstCirc, ((mstSymStarLp u Φ : MeasureTheory.Lp ℂ ⊤ mstHaar) : mstCirc → ℂ) ξ
          * star (fourier m ξ) ∂mstHaar
        = ∫ ξ : mstCirc, (star (fourier u ξ) * (Φ : mstCirc → ℂ) ξ) * star (fourier m ξ)
          ∂mstHaar := by
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with ξ hξ
      rw [hξ]
    rw [h1]
    have h2 : ∫ ξ : mstCirc, (star (fourier u ξ) * (Φ : mstCirc → ℂ) ξ) * star (fourier m ξ)
          ∂mstHaar
        = ∫ ξ : mstCirc, (Φ : mstCirc → ℂ) ξ * star (fourier (m + u) ξ) ∂mstHaar := by
      refine integral_congr_ae ?_
      filter_upwards with ξ
      have hstar : star (fourier (m + u) ξ) = star (fourier u ξ) * star (fourier m ξ) := by
        rw [fourier_add, star_mul]
      rw [hstar]
      ring
    rw [h2]
  rw [opMul_eq_tsum_kernel Φ f hf (K := K) hker1 (x + u),
    opMul_eq_tsum_kernel (mstSymStarLp u Φ) f hf (K := fun m => K (m + u)) hker2 x]
  refine tsum_congr fun k => ?_
  exact congrArg (fun t : ℤ => f k * K t) (by ring)

end

end Work.BourgainPlan.Maximal
