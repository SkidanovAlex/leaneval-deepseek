/-
# The high-frequency piece of the off-diagonal decay of the Ionescu--Wainger projections

This is the `ℓ¹`-mass estimate `Work.KMTAreas.A4.offPieceHigh` (the analytic heart of the "far
window" case of `iw-prop`(i), see `Work.KMTAreas.A4.offDecayKMT`), assembled from the three
independent pieces

* `offSampleConvComp`: for Schwartz `h`, `v` with `∫ v = 1`, the sampled `ℓ¹` mass of
  `h - h ∗ v` is bounded by the first moment of `v` times `‖h'‖₁ + ‖h''‖₁`
  (the composition of `offSample` with two applications of `offConvMoment`);
* `offBDerivBound`, `offBIteratedDeriv2Bound`: with `B = λ_k - η_{≤jj} λ_k`
  (`η_{≤jj} = bmp jj` the rescaled cutoff, `λ_k = 𝓕⁻ η_{≤k}`), the `L¹` norms of `B'` and `B''`
  are dominated by `C · 2^k · (max (2^{k+jj-1}) 1)^{-N}` for `k ≤ 0 ≤ jj`, `0 ≤ k + jj`.

Taking `h = B`, `v = λ_{-jv}`, whose first moment is `≲ 2^{jv}` (`offLamMoment`), gives the claim.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offLamMoment
import Submission.Work.KMTAreas.A4.offSampleConvComp
import Submission.Work.KMTAreas.A4.offBIteratedDeriv2Bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.KMTAreas.A4

theorem offPieceHighClaim (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj jv : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∑' j : ℤ, ‖(Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k) - Work.KMTAreas.A4.cS (Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k)) (Work.KMTAreas.A4.lam (-jv))) (j : ℝ)‖ ≤ C * (2 : ℝ) ^ (k + jv) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
  obtain ⟨Cc, hCcpos, hComp⟩ := offSampleConvComp
  obtain ⟨Cm, hCmpos, hM⟩ := offLamMoment
  obtain ⟨C1, hC1pos, hD1⟩ := offBDerivBound N
  obtain ⟨C2, hC2pos, hD2⟩ := offBIteratedDeriv2Bound N
  refine ⟨Cc * Cm * (C1 + C2), by positivity, ?_⟩
  intro k jj jv hk hjj hkjj
  set B : SchwartzMap ℝ ℂ := lam k - mS (bmp jj) (lam k) with hB
  set v : SchwartzMap ℝ ℂ := lam (-jv) with hv
  set P : ℝ := (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) with hP
  have hvint : ∫ y : ℝ, v y = 1 := by rw [hv]; exact integral_lam (-jv)
  have hMv : (∫ y : ℝ, |y| * ‖(v : ℝ → ℂ) y‖) ≤ Cm * (2:ℝ)^jv := by
    have h := hM (-jv)
    have hv' : (v : ℝ → ℂ) = (Work.KMTAreas.A7.etaMult_K (-jv) : ℝ → ℂ) := by
      rw [hv, lam_eq_etaMult_K]
    rw [hv']
    simpa using h
  have hI1 : (∫ x : ℝ, ‖deriv (B : ℝ → ℂ) x‖) ≤ C1 * (2:ℝ)^k * P := by
    have h := hD1 k jj hk hjj hkjj
    rw [hB, hP]
    exact h
  have hI2 : (∫ x : ℝ, ‖deriv (deriv (B : ℝ → ℂ)) x‖) ≤ C2 * (2:ℝ)^k * P := by
    have h := hD2 k jj hk hjj hkjj
    rw [hB, hP]
    exact h
  have hsum := hComp B v hvint
  have h2 : (2:ℝ)^(k+jv) = (2:ℝ)^k * (2:ℝ)^jv := by rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have hmain : ∑' j : ℤ, ‖(B - cS B v) (j : ℝ)‖ ≤ Cc * Cm * (C1 + C2) * (2:ℝ)^(k+jv) * P := by
    calc ∑' j : ℤ, ‖(B - cS B v) (j : ℝ)‖
        ≤ Cc * (∫ y : ℝ, |y| * ‖(v : ℝ → ℂ) y‖) * ((∫ x : ℝ, ‖deriv (B : ℝ → ℂ) x‖) + ∫ x : ℝ, ‖deriv (deriv (B : ℝ → ℂ)) x‖) := hsum
      _ ≤ Cc * (Cm * (2:ℝ)^jv) * (C1 * (2:ℝ)^k * P + C2 * (2:ℝ)^k * P) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hMv hCcpos.le
          · exact add_le_add hI1 hI2
          · positivity
          · positivity
      _ = Cc * Cm * (C1 + C2) * (2:ℝ)^k * (2:ℝ)^jv * P := by ring
      _ = Cc * Cm * (C1 + C2) * (2:ℝ)^(k+jv) * P := by rw [h2]; ring
  exact hmain

end Work.KMTAreas.A4
