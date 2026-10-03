import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_ftLp

/-!
# Orthogonality of band-limited `ℓ²(ℤ)`-functions with disjoint frequency supports

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(ii)); see `ARC_ARITH_STATUS.md`, addendum of session 6.

The two-factor case of Tao's denominator orthogonality, in the `ℓ²` setting of genuine
band-limited functions: if the Fourier transforms of `h, k ∈ ℓ²(ℤ)` (the `L²(𝕋)` functions
`ftLp h hh`, `ftLp k hk`) are supported in disjoint sets, then the pairing `Σ_n h n · conj (k n)`
vanishes.  The proof is Parseval (`tsum_mul_conj_eq_integral_ftLp`) followed by the observation that
the integrand vanishes almost everywhere.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Two-factor orthogonality of band-limited `ℓ²`-functions.**  If the Fourier transforms of
`h` and `k` are (a.e.) supported in disjoint sets `E` and `D`, then `Σ_n h n · conj (k n) = 0`. -/
theorem tsum_mul_conj_eq_zero_of_disjoint_freqSupport {h k : ℤ → ℂ} (hh : Memℓp h 2)
    (hk : Memℓp k 2) {E D : Set Circle} (hE : HasFreqSupport h hh E)
    (hD : HasFreqSupport k hk D) (hdisj : Disjoint E D) :
    ∑' n : ℤ, h n * star (k n) = 0 := by
  rw [tsum_mul_conj_eq_integral_ftLp hh hk]
  have hzero : (fun θ : Circle => (ftLp h hh : Circle → ℂ) θ
        * star ((ftLp k hk : Circle → ℂ) θ)) =ᵐ[AddCircle.haarAddCircle] 0 := by
    filter_upwards [hE, hD] with θ hθE hθD
    by_cases hmem : θ ∈ E
    · rw [hθD (fun h => Set.disjoint_left.mp hdisj hmem h), star_zero, mul_zero]
      rfl
    · rw [hθE hmem, zero_mul]
      rfl
  rw [integral_congr_ae hzero]
  simp

end Work.BourgainPlan.IonescuWainger
