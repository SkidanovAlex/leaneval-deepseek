import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixB3.Conv.ChiFourier
import Submission.Work.BoseFixB3.Eps.tail_zpow_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/Tail/kinFT_phiC_tail_le`

The high-frequency tail of the profile `φ = χ²` in the corpus's `p`-convention
(`Submission.BoseGases.kinFT`): there is a constant `C ≥ 0` with

`∫_{‖q‖ ≥ r} ‖φ̂(q)‖ dq ≤ C r^{-40}` for every `r > 0`.

The proof is the standard Fourier-side argument behind `Conv/chi_highpass_decay.lean`:

* `φ` is a *Schwartz* function (`phiSch`), so `φ̂ = 𝓕 phiSch` is rapidly decaying.  Taking
  the `k = 43` seminorm of `SchwartzMap.decay` gives the pure-power bound
  `‖φ̂(q)‖ ≤ K (‖q‖ ^ 43)⁻¹` for `q ≠ 0` (`kinFT_phiC_norm_inv_pow_le`);
* the radial tail integral `∫_{‖q‖ ≥ r} (‖q‖ ^ 43)⁻¹ dq ≤ (4π/40) r^{-40}` is
  `Work.BoseFixB3.Eps.tail_zpow_integral` at `N = 43`;
* the two are glued with `setIntegral_mono_on`, and the exponent `3 - 43 = -40` is
  converted from `zpow` to `rpow`.

The threshold `40` is precisely `43 - 3`: `N = 43` makes the radial integral converge in
`ℝ³` (dimension `3`) with exactly the decay `r^{3-N} = r^{-40}` requested.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology BigOperators FourierTransform SchwartzMap

namespace Work.BoseFixB3.Conv.Tail

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseFixB3.Scaling

/-! ### The pointwise Schwartz decay of `φ̂` in pure-power form -/

/-- `φ̂` is bounded by a pure power: `‖φ̂(q)‖ ≤ K (‖q‖ ^ 43)⁻¹` for `q ≠ 0`.

This is `SchwartzMap.decay (𝓕 phiSch) 43 0` transported along
`kinFT_phiC_fourier` (`ξ = (2π)⁻¹ q`). -/
lemma kinFT_phiC_norm_inv_pow_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : E3, q ≠ 0 →
      ‖Submission.BoseGases.kinFT phiC q‖ ≤ K * (‖q‖ ^ 43)⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := SchwartzMap.decay (𝓕 phiSch) 43 0
  set K : ℝ := (2 * π) ^ 43 * C with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨K, hKnn, ?_⟩
  intro q hq
  have hqn : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq
  set ξ : E3 := (2 * π)⁻¹ • q with hξdef
  have hξn : ‖ξ‖ = (2 * π)⁻¹ * ‖q‖ := by
    rw [hξdef, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)]
  have hdec : ‖ξ‖ ^ 43 * ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖ ≤ C := by
    have h1 := hC ξ
    rwa [norm_iteratedFDeriv_zero] at h1
  have hmul : ((2 * π)⁻¹) ^ 43 * (‖q‖ ^ 43 *
      ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖) ≤ C := by
    have h := hdec
    rw [hξn, mul_pow, mul_assoc] at h
    exact h
  have hKbound : ‖q‖ ^ 43 * ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖ ≤ K := by
    have h := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ (2 * π) ^ 43 by positivity)
    have he : (2 * π) ^ 43 * (((2 * π)⁻¹) ^ 43 * (‖q‖ ^ 43 *
        ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖))
        = ‖q‖ ^ 43 * ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖ := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0),
        one_pow, one_mul]
    rw [he] at h
    rwa [hKdef]
  have hfinal : ‖(FourierTransform.fourier phiSch : E3 → ℂ) ξ‖ ≤ K * (‖q‖ ^ 43)⁻¹ := by
    have hq43 : (0 : ℝ) < ‖q‖ ^ 43 := pow_pos hqn 43
    rw [le_mul_inv_iff₀ hq43, mul_comm]
    exact hKbound
  rw [kinFT_phiC_fourier, ← hξdef]
  exact hfinal

/-! ### The tail bound -/

theorem kinFT_phiC_tail_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      ∫ q in {q : EuclideanSpace ℝ (Fin 3) | r ≤ ‖q‖},
          ‖Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC q‖
        ≤ C * r ^ (-(40 : ℝ)) := by
  obtain ⟨K, hK, hdec⟩ := kinFT_phiC_norm_inv_pow_le
  obtain ⟨C₀, hC₀, htail⟩ := Work.BoseFixB3.Eps.tail_zpow_integral 43 (by norm_num)
  refine ⟨K * C₀, by positivity, ?_⟩
  intro r hr
  set s : Set E3 := {q : E3 | r ≤ ‖q‖} with hs
  have hs_meas : MeasurableSet s := measurableSet_le measurable_const measurable_norm
  obtain ⟨hInt, hLe⟩ := htail r hr
  have hkin : IntegrableOn (fun q : E3 => ‖Submission.BoseGases.kinFT phiC q‖) s :=
    kinFT_phiC_integrable.norm.integrableOn
  have hbdd : IntegrableOn (fun q : E3 => K * ((‖q‖ ^ 43)⁻¹)) s := hInt.const_mul K
  have hmono : ∫ q in s, ‖Submission.BoseGases.kinFT phiC q‖
      ≤ ∫ q in s, K * ((‖q‖ ^ 43)⁻¹) := by
    refine setIntegral_mono_on hkin hbdd hs_meas (fun q hq => ?_)
    have hqr : r ≤ ‖q‖ := by simpa [hs] using hq
    have hqn : (0 : ℝ) < ‖q‖ := lt_of_lt_of_le hr hqr
    have hqne : q ≠ 0 := fun h => by rw [h] at hqn; simp at hqn
    exact hdec q hqne
  have hrexp : r ^ (3 - ((43 : ℕ) : ℤ)) = r ^ (-(40 : ℝ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    norm_num
  calc ∫ q in s, ‖Submission.BoseGases.kinFT phiC q‖
      ≤ ∫ q in s, K * ((‖q‖ ^ 43)⁻¹) := hmono
    _ = K * ∫ q in s, (‖q‖ ^ 43)⁻¹ := by rw [MeasureTheory.integral_const_mul]
    _ ≤ K * (C₀ * r ^ (3 - ((43 : ℕ) : ℤ))) := mul_le_mul_of_nonneg_left hLe hK
    _ = K * C₀ * r ^ (-(40 : ℝ)) := by rw [hrexp]; ring

end Work.BoseFixB3.Conv.Tail
