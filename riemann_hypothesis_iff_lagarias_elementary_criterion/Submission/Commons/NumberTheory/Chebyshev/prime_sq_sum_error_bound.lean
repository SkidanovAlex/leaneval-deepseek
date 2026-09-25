import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

open MeasureTheory

namespace Commons.NumberTheory.Chebyshev

/-- `√t / t^3 = t^(-5/2)` for `t > 0`. -/
private lemma sqrt_div_cube (t : ℝ) (ht : 0 < t) : Real.sqrt t / t ^ 3 = t ^ (-(5/2:ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 3, ← Real.rpow_sub ht]
  norm_num

/-- `√x · L^10 / (x^2 · L) = L^9 / x^(3/2)` for `x > 0`, `L ≠ 0`. -/
private lemma sqrt_mul_pow_div_log_eq (x L : ℝ) (hx : 0 < x) (hL : L ≠ 0) :
    Real.sqrt x * L^10 / (x^2 * L) = L^9 / x^(3/2:ℝ) := by
  have hx3 : x^(3/2:ℝ) = Real.sqrt x * x := by
    rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1/2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
  rw [hx3]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring_nf
  rw [Real.sq_sqrt hx.le]
  ring

/-- `1/2 ≤ log t` for `t ≥ 2`. -/
private lemma log_two_ge_half {t : ℝ} (ht : 2 ≤ t) : (1/2:ℝ) ≤ Real.log t := by
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  exact le_trans h2 (Real.log_le_log (by norm_num) ht)

/-- Pointwise bound for the integrand. -/
private lemma integrand_bound_aux {C t m g : ℝ} (ht : 2 ≤ t) (htm : t ≤ m) (hC : 0 ≤ C)
    (hg : |g| ≤ C * Real.sqrt t * (Real.log t)^10) :
    ‖((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * g‖
      ≤ 4*C*(Real.log m)^9 * t^(-(5/2:ℝ)) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hℓ : 0 < Real.log t := Real.log_pos ht1
  have hℓm : Real.log t ≤ Real.log m := Real.log_le_log (by linarith) htm
  have hM : 0 < Real.log m := lt_of_lt_of_le hℓ hℓm
  have hfac : 0 ≤ (2*Real.log t + 1)/(t^3 * (Real.log t)^2) := by
    apply div_nonneg
    · nlinarith
    · positivity
  calc ‖((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * g‖
      = ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * |g| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hfac]
    _ ≤ ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (C * Real.sqrt t * (Real.log t)^10) :=
          mul_le_mul_of_nonneg_left hg hfac
    _ = C*(2*Real.log t+1)*(Real.log t)^8*(Real.sqrt t/t^3) := by
          field_simp
    _ = C*(2*Real.log t+1)*(Real.log t)^8*(t^(-(5/2:ℝ))) := by
          rw [sqrt_div_cube t ht0]
    _ ≤ C*(4*Real.log t)*(Real.log t)^8*(t^(-(5/2:ℝ))) := by
          gcongr
          linarith [log_two_ge_half ht]
    _ = 4*C*(Real.log t)^9*(t^(-(5/2:ℝ))) := by ring
    _ ≤ 4*C*(Real.log m)^9*(t^(-(5/2:ℝ))) := by
          gcongr

/-- `∫_n^m t^(-5/2) dt ≤ (2/3) n^(-3/2)` for `0 < n ≤ m`. -/
private lemma intervalIntegral_rpow_neg_five_halves_le {n m : ℝ} (hn : 0 < n) (hnm : n ≤ m) :
    ∫ t in n..m, t ^ (-(5/2):ℝ) ≤ (2/3) * n ^ (-(3/2):ℝ) := by
  have h0 : (0:ℝ) ∉ Set.uIcc n m := by
    rw [Set.uIcc_of_le hnm]
    exact fun hx => absurd hx.1 (not_le.mpr hn)
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  rw [show (-(5/2:ℝ)) + 1 = -(3/2:ℝ) by norm_num]
  have : (m ^ (-(3/2:ℝ)) - n ^ (-(3/2:ℝ))) / (-(3/2)) =
      (2/3) * (n ^ (-(3/2:ℝ)) - m ^ (-(3/2:ℝ))) := by
    field_simp
    ring
  rw [this]
  have hm3 : 0 ≤ m ^ (-(3/2:ℝ)) := Real.rpow_nonneg (le_trans hn.le hnm) _
  nlinarith [hm3]

/--

Error bound for the Abel-summation expression associated with `∑_{n < p ≤ m} p^{-2}`:
if `|θ t - t| ≤ C √t (log t)^10` on `[n,m]` (with `2 ≤ n ≤ m`, `C ≥ 0`), then the boundary terms
minus the integral are bounded by `5 C (log m)^9 / n^{3/2}`.

-/
theorem prime_sq_sum_error_bound {n m : ℝ} {C : ℝ} (hn : 2 ≤ n) (hnm : n ≤ m) (hC : 0 ≤ C)
    (hθ : ∀ t ∈ Set.Icc n m, |Chebyshev.theta t - t| ≤ C * Real.sqrt t * (Real.log t)^10) :
    |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)
      - (1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)
      + ∫ t in Set.Ioc n m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)|
      ≤ 5 * C * (Real.log m)^9 / n^(3/2 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hm1 : 1 < m := by linarith
  have hℓn : 0 < Real.log n := Real.log_pos hn1
  have hℓm : 0 < Real.log m := Real.log_pos hm1
  have hℓnm : Real.log n ≤ Real.log m := Real.log_le_log (by linarith) hnm
  rw [← intervalIntegral.integral_of_le hnm]
  have hA : |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
      ≤ C * (Real.log m)^9 / n^(3/2:ℝ) := by
    have hgm := hθ m ⟨hnm, le_refl m⟩
    have hden : 0 < m^2 * Real.log m := by positivity
    calc |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
        = |Chebyshev.theta m - m| / (m^2 * Real.log m) := by
            rw [abs_mul, abs_of_pos (one_div_pos.mpr hden)]; ring
      _ ≤ (C * Real.sqrt m * (Real.log m)^10) / (m^2 * Real.log m) :=
            div_le_div_of_nonneg_right hgm hden.le
      _ = C * (Real.log m)^9 / m^(3/2:ℝ) := by
            calc (C * Real.sqrt m * (Real.log m)^10) / (m^2 * Real.log m)
                = C * (Real.sqrt m * (Real.log m)^10 / (m^2 * Real.log m)) := by ring
              _ = C * ((Real.log m)^9 / m^(3/2:ℝ)) := by
                    rw [sqrt_mul_pow_div_log_eq m (Real.log m) hm0 hℓm.ne']
              _ = C * (Real.log m)^9 / m^(3/2:ℝ) := by ring
      _ ≤ C * (Real.log m)^9 / n^(3/2:ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hn0 _)
              (Real.rpow_le_rpow hn0.le hnm (by norm_num))
  have hB : |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)|
      ≤ C * (Real.log m)^9 / n^(3/2:ℝ) := by
    have hgn := hθ n ⟨le_refl n, hnm⟩
    have hden : 0 < n^2 * Real.log n := by positivity
    calc |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)|
        = |Chebyshev.theta n - n| / (n^2 * Real.log n) := by
            rw [abs_mul, abs_of_pos (one_div_pos.mpr hden)]; ring
      _ ≤ (C * Real.sqrt n * (Real.log n)^10) / (n^2 * Real.log n) :=
            div_le_div_of_nonneg_right hgn hden.le
      _ = C * (Real.log n)^9 / n^(3/2:ℝ) := by
            calc (C * Real.sqrt n * (Real.log n)^10) / (n^2 * Real.log n)
                = C * (Real.sqrt n * (Real.log n)^10 / (n^2 * Real.log n)) := by ring
              _ = C * ((Real.log n)^9 / n^(3/2:ℝ)) := by
                    rw [sqrt_mul_pow_div_log_eq n (Real.log n) hn0 hℓn.ne']
              _ = C * (Real.log n)^9 / n^(3/2:ℝ) := by ring
      _ ≤ C * (Real.log m)^9 / n^(3/2:ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓn.le hℓnm 9) hC) (by positivity)
  have hI : |∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)|
      ≤ (8/3) * C * (Real.log m)^9 / n^(3/2:ℝ) := by
    have huIcc : (0:ℝ) ∉ Set.uIcc n m := by
      rw [Set.uIcc_of_le hnm]
      exact fun hx => absurd hx.1 (not_le.mpr hn0)
    have hbound : IntervalIntegrable (fun t => 4*C*(Real.log m)^9 * t^(-(5/2:ℝ))) volume n m :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr huIcc)).const_mul _
    have hpoint : ∀ᵐ t ∂volume, t ∈ Set.Ioc n m →
        ‖((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)‖
          ≤ 4*C*(Real.log m)^9 * t^(-(5/2:ℝ)) := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      exact integrand_bound_aux (le_trans hn (le_of_lt ht.1)) ht.2 hC (hθ t ⟨le_of_lt ht.1, ht.2⟩)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hnm hpoint hbound
    rw [Real.norm_eq_abs] at h1
    have h2 : ∫ t in n..m, 4*C*(Real.log m)^9 * t^(-(5/2:ℝ))
        ≤ (8/3)*C*(Real.log m)^9 / n^(3/2:ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      calc 4*C*(Real.log m)^9 * (∫ t in n..m, t^(-(5/2:ℝ)))
          ≤ 4*C*(Real.log m)^9 * ((2/3) * n^(-(3/2:ℝ))) := by
            apply mul_le_mul_of_nonneg_left (intervalIntegral_rpow_neg_five_halves_le hn0 hnm)
            positivity
        _ = (8/3)*C*(Real.log m)^9 / n^(3/2:ℝ) := by
            rw [Real.rpow_neg hn0.le]
            ring
    exact le_trans h1 h2
  have htri : |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)
      - (1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)
      + ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)|
      ≤ |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
        + |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)|
        + |∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)| := by
    have h1 := abs_add_le ((1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)
        - (1/(n^2 * Real.log n)) * (Chebyshev.theta n - n))
        (∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t))
    have h2 : |((1/(m^2 * Real.log m)) * (Chebyshev.theta m - m))
        - ((1/(n^2 * Real.log n)) * (Chebyshev.theta n - n))|
        ≤ |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
          + |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)| := by
      rw [sub_eq_add_neg]
      calc |((1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)) + (-((1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)))|
            ≤ |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
              + |(-((1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)))| := abs_add_le _ _
        _ = |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
              + |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)| := by rw [abs_neg]
    linarith [h1, h2]
  have hK : 0 ≤ C * (Real.log m)^9 / n^(3/2:ℝ) := by positivity
  calc |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)
        - (1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)
        + ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)|
      ≤ |(1/(m^2 * Real.log m)) * (Chebyshev.theta m - m)|
        + |(1/(n^2 * Real.log n)) * (Chebyshev.theta n - n)|
        + |∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * (Chebyshev.theta t - t)| := htri
    _ ≤ C*(Real.log m)^9/n^(3/2:ℝ) + C*(Real.log m)^9/n^(3/2:ℝ)
        + (8/3)*C*(Real.log m)^9/n^(3/2:ℝ) := by
          exact add_le_add (add_le_add hA hB) hI
    _ ≤ 5 * C * (Real.log m)^9 / n^(3/2:ℝ) := by
          have h5 : (5:ℝ) * C * (Real.log m)^9 / n^(3/2:ℝ)
              = 5 * (C * (Real.log m)^9 / n^(3/2:ℝ)) := by ring
          rw [h5]
          have hsum : C*(Real.log m)^9/n^(3/2:ℝ) + C*(Real.log m)^9/n^(3/2:ℝ)
              + (8/3)*C*(Real.log m)^9/n^(3/2:ℝ)
              = (14/3)*(C*(Real.log m)^9/n^(3/2:ℝ)) := by ring
          rw [hsum]
          exact mul_le_mul_of_nonneg_right (by norm_num) hK

end Commons.NumberTheory.Chebyshev