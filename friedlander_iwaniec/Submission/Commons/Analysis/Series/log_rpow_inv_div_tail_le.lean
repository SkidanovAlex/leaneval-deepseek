import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Submission.Commons.Analysis.Series.summable_log_rpow_inv_div

namespace Commons.Analysis.Series

open MeasureTheory Filter intervalIntegral Set
open scoped Topology

/-- Derivative of `t ↦ (log t)^(1-p) / (1-p)` for `t > 1`, `p ≠ 1`. -/
lemma hasDerivAt_log_rpow_div (p x : ℝ) (hp : p ≠ 1) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - p) / (1 - p)) ((Real.log x) ^ (-p) / x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h1 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - p))
      (x⁻¹ * (1 - p) * (Real.log x) ^ (1 - p - 1)) x :=
    (Real.hasDerivAt_log hx0).rpow_const (Or.inl hlog)
  have h2 := h1.div_const (1 - p)
  have hne : (1 : ℝ) - p ≠ 0 := by intro h; exact hp (by linarith)
  have key : (x⁻¹ * (1 - p) * (Real.log x) ^ (1 - p - 1)) / (1 - p) = (Real.log x) ^ (-p) / x := by
    rw [show (1 - p - 1 : ℝ) = -p by ring, div_eq_iff hne, div_eq_mul_inv]
    ring
  rwa [key] at h2

/-- `x ↦ (log x)^(-p)/x` is antitone on `[2,∞)` for `p > 1`. -/
lemma antitoneOn_log_rpow_div (p : ℝ) (hp : 1 < p) :
    AntitoneOn (fun x : ℝ => (Real.log x) ^ (-p) / x) (Ici 2) := by
  intro a ha b hb hab
  have ha2 : (2 : ℝ) ≤ a := ha
  have hb2 : (2 : ℝ) ≤ b := hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hle : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have h1 : (Real.log b) ^ (-p) ≤ (Real.log a) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hla hle (by linarith)
  have h2 : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb0 ha0).mpr hab
  simp only [div_eq_mul_inv]
  exact mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg (le_of_lt hla) (-p))

/-- `t ↦ (log t)^(1-p)/(1-p)` tends to `0` at `+∞` for `p > 1`. -/
lemma tendsto_log_rpow_div (p : ℝ) (hp : 1 < p) :
    Tendsto (fun t : ℝ => (Real.log t) ^ (1 - p) / (1 - p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (Real.log t) ^ (-(p - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < p - 1 by linarith)).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun t : ℝ => (Real.log t) ^ (1 - p)) atTop (𝓝 0) := by
    simpa only [show (-(p - 1) : ℝ) = 1 - p by ring] using h1
  have h3 := h2.div_const (1 - p)
  simpa using h3

/-- `x ↦ (log x)^(-p)/x` is integrable on `(N,∞)` for `N ≥ 2`, `p > 1`. -/
lemma integrableOn_log_rpow_div (p : ℝ) (hp : 1 < p) {N : ℕ} (hN : 2 ≤ N) :
    IntegrableOn (fun x : ℝ => (Real.log x) ^ (-p) / x) (Ioi (N : ℝ)) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ x ∈ Ici (N : ℝ),
      HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - p) / (1 - p)) ((Real.log x) ^ (-p) / x) x := by
    intro x hx
    have hx1 : 1 < x := by have hx' : (N : ℝ) ≤ x := hx; linarith
    exact hasDerivAt_log_rpow_div p x hp.ne' hx1
  have hpos : ∀ x ∈ Ioi (N : ℝ), 0 ≤ (Real.log x) ^ (-p) / x := by
    intro x hx
    have hx1 : 1 < x := by have hx' : (N : ℝ) < x := hx; linarith
    have hx0 : 0 < x := by linarith
    exact div_nonneg (Real.rpow_nonneg (le_of_lt (Real.log_pos hx1)) (-p)) (le_of_lt hx0)
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos (tendsto_log_rpow_div p hp)

/-- Value of the tail integral of `x ↦ (log x)^(-p)/x`. -/
lemma integral_Ioi_log_rpow_div (p : ℝ) (hp : 1 < p) {N : ℕ} (hN : 2 ≤ N) :
    ∫ x in Ioi (N : ℝ), (Real.log x) ^ (-p) / x = (Real.log (N : ℝ)) ^ (1 - p) / (p - 1) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ x ∈ Ici (N : ℝ),
      HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - p) / (1 - p)) ((Real.log x) ^ (-p) / x) x := by
    intro x hx
    have hx1 : 1 < x := by have hx' : (N : ℝ) ≤ x := hx; linarith
    exact hasDerivAt_log_rpow_div p x hp.ne' hx1
  have hpos : ∀ x ∈ Ioi (N : ℝ), 0 ≤ (Real.log x) ^ (-p) / x := by
    intro x hx
    have hx1 : 1 < x := by have hx' : (N : ℝ) < x := hx; linarith
    have hx0 : 0 < x := by linarith
    exact div_nonneg (Real.rpow_nonneg (le_of_lt (Real.log_pos hx1)) (-p)) (le_of_lt hx0)
  have hlim := tendsto_log_rpow_div p hp
  have hint := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hval, zero_sub, ← div_neg, show -(1 - p : ℝ) = p - 1 by ring]

theorem log_rpow_inv_div_tail_le (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑' k : ℕ, (Real.log ((N + k : ℕ) : ℝ)) ^ (-p) / ((N + k : ℕ) : ℝ))
        ≤ C * (Real.log (N : ℝ)) ^ (1 - p) := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  refine ⟨1 + 1 / (p - 1), ?_, ?_⟩
  · have : (0 : ℝ) < 1 / (p - 1) := div_pos one_pos hp1
    linarith
  · intro N hN
    have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNgt1 : (1 : ℝ) < (N : ℝ) := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNgt1
    have hanti : AntitoneOn (fun x : ℝ => (Real.log x) ^ (-p) / x) (Ici (N : ℝ)) :=
      (antitoneOn_log_rpow_div p hp).mono (Ici_subset_Ici.mpr hN2R)
    have hnonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ (Real.log t) ^ (-p) / t := by
      intro t ht
      have ht1 : (1 : ℝ) < t := by have ht' : (N : ℝ) < t := ht; linarith
      have ht0 : 0 < t := by linarith
      exact div_nonneg (Real.rpow_nonneg (le_of_lt (Real.log_pos ht1)) (-p)) (le_of_lt ht0)
    have hint : IntegrableOn (fun x : ℝ => (Real.log x) ^ (-p) / x) (Ioi (N : ℝ)) :=
      integrableOn_log_rpow_div p hp hN
    have hval : ∫ x in Ioi (N : ℝ), (Real.log x) ^ (-p) / x
        = (Real.log (N : ℝ)) ^ (1 - p) / (p - 1) := integral_Ioi_log_rpow_div p hp hN
    have hcmp := AntitoneOn.tsum_comp_add_le_integral N hanti hint hnonneg
    rw [hval] at hcmp
    have hsumm : Summable (fun n : ℕ => (Real.log ((n : ℕ) : ℝ)) ^ (-p) / ((n : ℕ) : ℝ)) :=
      hanti.summable_of_integrableOn_Ioi hint hnonneg
    have hsummN : Summable (fun k : ℕ =>
        (Real.log (((N + k : ℕ)) : ℝ)) ^ (-p) / (((N + k : ℕ)) : ℝ)) := by
      have h := (summable_nat_add_iff N).mpr hsumm
      refine h.congr (fun k => ?_)
      show (Real.log (((k + N : ℕ)) : ℝ)) ^ (-p) / (((k + N : ℕ)) : ℝ)
        = (Real.log (((N + k : ℕ)) : ℝ)) ^ (-p) / (((N + k : ℕ)) : ℝ)
      rw [Nat.add_comm k N]
    have htsum := hsummN.tsum_eq_zero_add
    have hshift : (∑' k : ℕ,
          (Real.log (((N + (k + 1) : ℕ)) : ℝ)) ^ (-p) / (((N + (k + 1) : ℕ)) : ℝ))
        = ∑' k : ℕ, (Real.log (((k + N + 1 : ℕ)) : ℝ)) ^ (-p) / (((k + N + 1 : ℕ)) : ℝ) := by
      apply tsum_congr; intro k
      rw [show (N + (k + 1) : ℕ) = k + N + 1 by omega]
    have hfN : (Real.log (N : ℝ)) ^ (-p) / (N : ℝ) ≤ (Real.log (N : ℝ)) ^ (1 - p) := by
      have hkey : (Real.log (N : ℝ)) ^ (1 - p)
          = (Real.log (N : ℝ)) ^ (-p) * Real.log (N : ℝ) := by
        rw [show (1 : ℝ) - p = -p + 1 by ring, Real.rpow_add hlogN, Real.rpow_one]
      rw [hkey, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt hlogN) (-p))
      rw [inv_le_iff_one_le_mul₀ hNpos]
      have hl2 : (1 / 2 : ℝ) ≤ Real.log (N : ℝ) := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2R
        linarith [Real.log_two_gt_d9]
      nlinarith
    calc (∑' k : ℕ, (Real.log (((N + k : ℕ)) : ℝ)) ^ (-p) / (((N + k : ℕ)) : ℝ))
        = (Real.log (((N + 0 : ℕ)) : ℝ)) ^ (-p) / (((N + 0 : ℕ)) : ℝ)
            + ∑' k : ℕ,
                (Real.log (((N + (k + 1) : ℕ)) : ℝ)) ^ (-p) / (((N + (k + 1) : ℕ)) : ℝ) := htsum
      _ = (Real.log (N : ℝ)) ^ (-p) / (N : ℝ)
            + ∑' k : ℕ,
                (Real.log (((N + (k + 1) : ℕ)) : ℝ)) ^ (-p) / (((N + (k + 1) : ℕ)) : ℝ) := by
          rw [Nat.add_zero]
      _ = (Real.log (N : ℝ)) ^ (-p) / (N : ℝ)
            + ∑' k : ℕ,
                (Real.log (((k + N + 1 : ℕ)) : ℝ)) ^ (-p) / (((k + N + 1 : ℕ)) : ℝ) := by
          rw [hshift]
      _ ≤ (Real.log (N : ℝ)) ^ (-p) / (N : ℝ) + (Real.log (N : ℝ)) ^ (1 - p) / (p - 1) :=
          add_le_add le_rfl hcmp
      _ ≤ (Real.log (N : ℝ)) ^ (1 - p) + (Real.log (N : ℝ)) ^ (1 - p) / (p - 1) :=
          add_le_add hfN le_rfl
      _ = (1 + 1 / (p - 1)) * (Real.log (N : ℝ)) ^ (1 - p) := by ring

end Commons.Analysis.Series