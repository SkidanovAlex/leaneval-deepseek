import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.int_summable_rpow_inv_two
import Submission.Work.BourgainPlan.IonescuWainger.int_tsum_rpow_inv_two_mul_le

namespace Work.BourgainPlan.IonescuWainger

/-- For a real number `x`, the squared norm of `(x : ℂ)⁻¹` is `(x²)⁻¹`. -/
private lemma norm_inv_ofReal_sq (x : ℝ) : ‖(((x : ℝ) : ℂ))⁻¹‖ ^ 2 = (x ^ 2)⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← sq, ← inv_pow]

/-- Pointwise comparison: for `a ≥ 0` the polynomial weight `(1 + (a m)²)⁻²` is dominated by
twice the rational majorant `(1 + |a m|)⁻²`, because `(1 + |t|)² ≤ 2 (1 + t²)²`. -/
private lemma inv_sq_one_add_sq_le (s : ℝ) :
    ((1 + s ^ 2) ^ 2)⁻¹ ≤ 2 * (1 + |s|) ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |s|) 2, Real.rpow_two]
  have key : (1 + |s|) ^ 2 ≤ 2 * (1 + s ^ 2) ^ 2 := by
    nlinarith [sq_abs s, abs_nonneg s, sq_nonneg (|s| - 1 / 3)]
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 + |s|) ^ 2) key
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, one_mul, one_mul] at h
  linarith

/-- **The restricted `ℓ²`-norm of the inverse polynomial weight**: for `ε > 0`, `Q ≥ 1` and
`ε·Q ≤ 1`, one has `Σ_m ‖(1 + ε²(Qm)²)⁻¹‖² ≤ 8/(εQ)`.  This is the constant `C₁²` of the weighted
Cauchy–Schwarz step of the `p = ∞` endpoint of Tao's `ortho-apply`(ii), taken over the annihilator
`Qℤ` (Tao's observation that the integrand is supported on `(Q_Aℤ)^d`).  The hypothesis `ε·Q ≤ 1`
is necessary: the `m = 0` term already contributes `1`, so the bound `8/(εQ)` cannot hold for large
`εQ` (the unrestricted sum over `ℤ` would only give `O(1/ε)`, which is `√Q` times worse and not
enough for the intended `O(1)` constant). -/
theorem tsum_inv_polyWeight_sq_mul_le {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q)
    (hεQ : ε * (Q : ℝ) ≤ 1) :
    ∑' m : ℤ, ‖((1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2)⁻¹‖ ^ 2
      ≤ 8 / (ε * Q) := by
  set a : ℝ := ε * (Q : ℝ) with ha_def
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have ha : 0 < a := by rw [ha_def]; exact mul_pos hε hQpos
  have ha1 : a ≤ 1 := hεQ
  -- Step 1: reduce the complex summand to its real value and dominate `(1 + t²)⁻²` by the
  -- rational majorant `2 · (1 + |t|)⁻²`.
  have hpt : ∀ m : ℤ, ‖((1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2)⁻¹‖ ^ 2
      ≤ 2 * (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) := by
    intro m
    have hz : (1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2
        = (((1 + (a * (m : ℝ)) ^ 2 : ℝ)) : ℂ) := by
      rw [ha_def]; push_cast; ring
    rw [hz, norm_inv_ofReal_sq]
    exact inv_sq_one_add_sq_le _
  have hM : Summable (fun m : ℤ => (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ))) :=
    int_summable_rpow_inv_two a ha
  have hG : Summable (fun m : ℤ =>
      ‖((1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2)⁻¹‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun m => by positivity) (fun m => hpt m) (hM.mul_left 2)
  have hle := Summable.tsum_le_tsum hpt hG (hM.mul_left 2)
  rw [tsum_mul_left] at hle
  have hMbound : a * ∑' m : ℤ, (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) ≤ 3 :=
    int_tsum_rpow_inv_two_mul_le a ha ha1
  have hsumM : ∑' m : ℤ, (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) ≤ 3 / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hMbound
  calc ∑' m : ℤ, ‖((1 : ℂ) + (ε : ℂ) ^ 2 * ((Q : ℂ) * (m : ℂ)) ^ 2)⁻¹‖ ^ 2
      ≤ 2 * ∑' m : ℤ, (1 + |a * (m : ℝ)|) ^ (-(2 : ℝ)) := hle
    _ ≤ 2 * (3 / a) := mul_le_mul_of_nonneg_left hsumM (by norm_num)
    _ = 6 / a := by ring
    _ ≤ 8 / a := div_le_div_of_nonneg_right (by norm_num) (le_of_lt ha)

end Work.BourgainPlan.IonescuWainger
