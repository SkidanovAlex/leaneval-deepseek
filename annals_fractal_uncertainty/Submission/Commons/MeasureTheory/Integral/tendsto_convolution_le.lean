import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter Topology
open scoped Topology

namespace Commons.MeasureTheory.Integral

theorem tendsto_convolution_le {d : ℕ}
    {K : ℕ → (Fin d → ℂ) → ℝ} {u : (Fin d → ℂ) → ℝ}
    (husc : UpperSemicontinuous u)
    (hloc : ∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M)
    (hKnn : ∀ (n : ℕ) (s : Fin d → ℂ), 0 ≤ K n s)
    (hKmass : ∀ n : ℕ, ∫ s : Fin d → ℂ, K n s = 1)
    (hKsupp : ∀ n : ℕ, Function.support (K n) ⊆ Metric.closedBall 0 (1 / (n + 1)))
    (z : Fin d → ℂ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      (∫ s : Fin d → ℂ, K n s * u (z - s)) ≤ u z + ε := by
  intro ε hε
  -- Upper semicontinuity at z gives a neighbourhood on which u < u z + ε.
  have h_ev : ∀ᶠ w in 𝓝 z, u w < u z + ε :=
    husc z (u z + ε) (lt_add_of_pos_right _ hε)
  rw [Metric.eventually_nhds_iff] at h_ev
  obtain ⟨δ, hδpos, hδ⟩ := h_ev
  -- The radii 1/(n+1) eventually fall below δ.
  have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [Tendsto.eventually_lt_const hδpos htend] with n hn
  have hn2 : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
    simpa [Nat.cast_add, Nat.cast_one] using hn
  have hle1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    calc 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (1 : ℝ) :=
            one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by norm_num
  have hKint : Integrable (K n) volume := integrable_of_integral_eq_one (hKmass n)
  obtain ⟨M, hM⟩ := hloc (‖z‖ + 1)
  have hCn : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  -- Pointwise domination of the integrand by `max M 0 * K n`.
  have hbound : ∀ s : Fin d → ℂ, ‖K n s * u (z - s)‖ ≤ ‖(max M 0) * K n s‖ := by
    intro s
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hKnn n s), abs_of_nonneg hCn]
    by_cases h : K n s = 0
    · rw [h, zero_mul, mul_zero]
    · have hs : s ∈ Function.support (K n) := h
      have hsnorm : ‖s‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        have h := Metric.mem_closedBall.1 (hKsupp n hs)
        rw [dist_eq_norm, sub_zero] at h
        simpa [Nat.cast_add, Nat.cast_one] using h
      have hzs : ‖z - s‖ ≤ ‖z‖ + 1 := by
        calc ‖z - s‖ ≤ ‖z‖ + ‖s‖ := norm_sub_le z s
          _ ≤ ‖z‖ + 1 / ((n + 1 : ℕ) : ℝ) := by gcongr
          _ ≤ ‖z‖ + 1 := by gcongr
      have huM : |u (z - s)| ≤ M := hM (z - s) hzs
      have huC : |u (z - s)| ≤ max M 0 := huM.trans (le_max_left M 0)
      calc K n s * |u (z - s)| ≤ K n s * max M 0 :=
            mul_le_mul_of_nonneg_left huC (hKnn n s)
        _ = max M 0 * K n s := by ring
  have hsub : Measurable (fun s : Fin d → ℂ => z - s) :=
    measurable_const.sub measurable_id
  have hfaesm : AEStronglyMeasurable (fun s : Fin d → ℂ => K n s * u (z - s)) volume :=
    hKint.aestronglyMeasurable.mul
      ((husc.measurable.comp hsub).aestronglyMeasurable)
  have hfint : Integrable (fun s : Fin d → ℂ => K n s * u (z - s)) volume :=
    Integrable.mono (hKint.const_mul (max M 0)) hfaesm (Eventually.of_forall hbound)
  have hgint : Integrable (fun s : Fin d → ℂ => K n s * (u z + ε)) volume :=
    hKint.mul_const (u z + ε)
  have hmono : (∫ s : Fin d → ℂ, K n s * u (z - s)) ≤
      ∫ s : Fin d → ℂ, K n s * (u z + ε) :=
    integral_mono hfint hgint (fun s => by
      by_cases h : K n s = 0
      · rw [h, zero_mul, zero_mul]
      · have hs : s ∈ Function.support (K n) := h
        have hsnorm : ‖s‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
          have h := Metric.mem_closedBall.1 (hKsupp n hs)
          rw [dist_eq_norm, sub_zero] at h
          simpa [Nat.cast_add, Nat.cast_one] using h
        have hlt : ‖s‖ < δ := lt_of_le_of_lt hsnorm hn2
        have hdist : dist (z - s) z < δ := by
          rw [dist_eq_norm]
          have h1 : (z - s) - z = -s := by abel
          rw [h1, norm_neg]
          exact hlt
        exact mul_le_mul_of_nonneg_left (le_of_lt (hδ hdist)) (hKnn n s))
  calc (∫ s : Fin d → ℂ, K n s * u (z - s))
      ≤ ∫ s : Fin d → ℂ, K n s * (u z + ε) := hmono
    _ = (∫ s : Fin d → ℂ, K n s) * (u z + ε) := integral_mul_const (u z + ε) (K n)
    _ = u z + ε := by rw [hKmass n, one_mul]

end Commons.MeasureTheory.Integral