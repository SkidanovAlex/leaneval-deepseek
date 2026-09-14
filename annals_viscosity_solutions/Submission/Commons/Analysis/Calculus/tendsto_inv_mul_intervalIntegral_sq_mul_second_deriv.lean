import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.Analysis.Calculus.tendsto_inv_mul_intervalIntegral_of_tendsto_zero

namespace Commons.Analysis.Calculus

open Filter MeasureTheory Set
open scoped Topology

theorem tendsto_inv_mul_intervalIntegral_sq_mul_second_deriv {s : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hs2 : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt (deriv s) (deriv (deriv s) t) t) (hint : ∀ t ∈ Set.Ioo (0:ℝ) ε, IntervalIntegrable (fun τ : ℝ => τ ^ 2 * deriv (deriv s) τ) MeasureTheory.volume 0 t) (hint1 : ∀ t ∈ Set.Ioo (0:ℝ) ε, IntervalIntegrable (fun τ : ℝ => 2 * τ * deriv s τ) MeasureTheory.volume 0 t) (hlim : Filter.Tendsto (fun t : ℝ => t * deriv s t) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0)) : Filter.Tendsto (fun t : ℝ => t⁻¹ * ∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- `τ ↦ τ^2 * deriv s τ` tends to 0 at 0⁺ (needed for the FTC at the left endpoint).
  have ha : Tendsto (fun τ : ℝ => τ ^ 2 * deriv s τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun τ : ℝ => τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (0:ℝ)) :=
      (continuousAt_id (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul hlim
    simpa [pow_two, mul_assoc] using h2
  -- The key identity on `(0, ε)` coming from the FTC applied to `τ ↦ τ^2 * deriv s τ`.
  have hident : ∀ t ∈ Set.Ioo (0:ℝ) ε,
      t⁻¹ * ∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ
        = t * deriv s t - t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have htε : t < ε := ht.2
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) t,
        HasDerivAt (fun τ : ℝ => τ ^ 2 * deriv s τ)
          (2 * x * deriv s x + x ^ 2 * deriv (deriv s) x) x := by
      intro x hx
      have hu : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hv : HasDerivAt (deriv s) (deriv (deriv s) x) x :=
        hs2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact hu.mul hv
    have hintf' : IntervalIntegrable
        (fun τ : ℝ => 2 * τ * deriv s τ + τ ^ 2 * deriv (deriv s) τ) MeasureTheory.volume 0 t :=
      (hint1 t ht).add (hint t ht)
    have hb : Tendsto (fun τ : ℝ => τ ^ 2 * deriv s τ) (nhdsWithin t (Set.Iio t))
        (nhds (t ^ 2 * deriv s t)) :=
      (((continuousAt_id (x := t)).pow 2).mul (hs2 t ht).continuousAt).continuousWithinAt
    have hftc : ∫ τ in (0:ℝ)..t, (2 * τ * deriv s τ + τ ^ 2 * deriv (deriv s) τ)
        = t ^ 2 * deriv s t := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht0 hderiv hintf' ha hb
      simpa using this
    have hsplit : ∫ τ in (0:ℝ)..t, (2 * τ * deriv s τ + τ ^ 2 * deriv (deriv s) τ)
        = (∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ)
          + (∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ) :=
      intervalIntegral.integral_add (hint1 t ht) (hint t ht)
    have hI2 : ∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ
        = t ^ 2 * deriv s t - ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ := by
      linarith [hftc, hsplit]
    have haux : t⁻¹ * (t ^ 2 * deriv s t) = t * deriv s t := by
      rw [pow_two, mul_assoc, inv_mul_cancel_left₀ (ne_of_gt ht0)]
    calc t⁻¹ * ∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ
        = t⁻¹ * (t ^ 2 * deriv s t - ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ) := by rw [hI2]
      _ = t⁻¹ * (t ^ 2 * deriv s t) - t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ := by
            rw [mul_sub]
      _ = t * deriv s t - t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ := by rw [haux]
  -- `2 τ deriv s τ → 0` at `0⁺`.
  have hg : Tendsto (fun τ : ℝ => 2 * τ * deriv s τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have := hlim.const_mul 2
    simpa [mul_assoc] using this
  have hB : Tendsto (fun t : ℝ => t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_inv_mul_intervalIntegral_of_tendsto_zero hε hg hint1
  have hAB : Tendsto (fun t : ℝ => t * deriv s t - t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    have := hlim.sub hB
    simpa using this
  have hev : (fun t : ℝ => t * deriv s t - t⁻¹ * ∫ τ in (0:ℝ)..t, 2 * τ * deriv s τ)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
        (fun t : ℝ => t⁻¹ * ∫ τ in (0:ℝ)..t, τ ^ 2 * deriv (deriv s) τ) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    exact (hident t ht).symm
  exact Tendsto.congr' hev hAB

end Commons.Analysis.Calculus