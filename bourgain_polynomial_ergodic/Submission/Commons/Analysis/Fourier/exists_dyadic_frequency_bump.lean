import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Data.Int.Star

namespace Commons.Analysis.Fourier

/-- Telescoping sum over a `ℤ`-indexed half-open interval:
`∑_{i=m}^{m+k-1} (f i - f (i+1)) = f m - f (m+k)`. -/
lemma sum_Ico_sub_int {M : Type*} [AddCommGroup M] (f : ℤ → M) :
    ∀ (m : ℤ) (k : ℕ), ∑ i ∈ Finset.Ico m (m + k), (f i - f (i + 1)) = f m - f (m + k) := by
  intro m k
  induction k with
  | zero => simp
  | succ k ih =>
    have hins : Finset.Ico m (m + (k : ℤ) + 1) = insert (m + k) (Finset.Ico m (m + k)) := by
      rw [show m + (k : ℤ) + 1 = (m + k) + 1 by ring]
      exact (Finset.insert_Ico_right_eq_Ico_add_one (by omega : m ≤ m + (k : ℤ))).symm
    rw [show m + ((k + 1 : ℕ) : ℤ) = m + (k : ℤ) + 1 by push_cast; ring, hins,
      Finset.sum_insert (by simp [Finset.mem_Ico]), ih]
    abel

/-- Telescoping sum over a `ℤ`-indexed half-open interval. -/
lemma sum_Ico_sub_int' {M : Type*} [AddCommGroup M] (f : ℤ → M) {m n : ℤ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (f i - f (i + 1)) = f m - f n := by
  obtain ⟨k, hk⟩ := Int.le.dest hmn
  rw [← hk]
  exact sum_Ico_sub_int f m k

theorem exists_dyadic_frequency_bump :
    ∃ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      (∀ ξ : ℝ, |ξ| ≤ 1 → θ ξ = 1) ∧
      (∀ ξ : ℝ, 2 ≤ |ξ| → θ ξ = 0) ∧
      (∀ ξ : ℝ, ξ ≠ 0 → ∑' a : ℤ, (θ ((2:ℝ)^a * ξ) - θ ((2:ℝ)^(a+1) * ξ)) = 1) := by
  set θb : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩ with hθb
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (θb : ℝ → ℝ) := θb.contDiff
  have hsupp : HasCompactSupport (θb : ℝ → ℝ) := θb.hasCompactSupport
  have hone : ∀ ξ : ℝ, |ξ| ≤ 1 → θb ξ = 1 := by
    intro ξ hξ
    apply θb.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hξ
  have hzero : ∀ ξ : ℝ, 2 ≤ |ξ| → θb ξ = 0 := by
    intro ξ hξ
    apply θb.zero_of_le_dist
    rw [Real.dist_eq, sub_zero]
    exact hξ
  refine ⟨(θb : ℝ → ℝ), hcont, hsupp, hone, hzero, ?_⟩
  intro ξ hξ
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max |ξ| (2 / |ξ|)) (by norm_num : (1:ℝ) < 2)
  have hN1 : |ξ| < (2:ℝ)^N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 / |ξ| < (2:ℝ)^N := lt_of_le_of_lt (le_max_right _ _) hN
  have h2pos : (0:ℝ) < 2 := by norm_num
  have h2one : (1:ℝ) ≤ 2 := by norm_num
  -- scaling below the `1`-threshold
  have hsmall : ∀ a : ℤ, a ≤ -(N:ℤ) → |(2:ℝ)^a * ξ| ≤ 1 := by
    intro a ha
    rw [abs_mul, abs_of_pos (zpow_pos h2pos a)]
    have hle : (2:ℝ)^a ≤ (2:ℝ)^(-(N:ℤ)) := zpow_le_zpow_right₀ h2one ha
    have hb : (2:ℝ)^(-(N:ℤ)) * |ξ| < 1 := by
      have he : (2:ℝ)^(-(N:ℤ)) = ((2:ℝ)^N)⁻¹ := by rw [zpow_neg, zpow_natCast]
      rw [he, inv_mul_eq_div, div_lt_one (pow_pos h2pos N)]
      exact hN1
    exact le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (abs_nonneg ξ)) hb)
  -- scaling above the `2`-threshold
  have hbig : ∀ a : ℤ, (N:ℤ) ≤ a → 2 ≤ |(2:ℝ)^a * ξ| := by
    intro a ha
    rw [abs_mul, abs_of_pos (zpow_pos h2pos a)]
    have hle : (2:ℝ)^(N:ℤ) ≤ (2:ℝ)^a := zpow_le_zpow_right₀ h2one ha
    have hb : 2 < (2:ℝ)^(N:ℤ) * |ξ| := by
      have he : (2:ℝ)^(N:ℤ) = (2:ℝ)^N := zpow_natCast (2:ℝ) N
      rw [he]
      have h := mul_lt_mul_of_pos_right hN2 hξpos
      rwa [div_mul_cancel₀ 2 hξpos.ne'] at h
    exact le_of_lt (lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right hle (abs_nonneg ξ)))
  -- the summand vanishes off the finite window
  have hsuppG : ∀ a : ℤ, a ∉ Finset.Ico (-(N:ℤ)) (N:ℤ) →
      θb ((2:ℝ)^a * ξ) - θb ((2:ℝ)^(a+1) * ξ) = 0 := by
    intro a ha
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
    rcases ha with ha | ha
    · rw [hone _ (hsmall a (le_of_lt ha)), hone _ (hsmall (a + 1) (by omega))]
      ring
    · rw [hzero _ (hbig a ha), hzero _ (hbig (a + 1) (by omega))]
      ring
  rw [tsum_eq_sum hsuppG]
  have htel : ∑ b ∈ Finset.Ico (-(N:ℤ)) (N:ℤ),
        (θb ((2:ℝ)^b * ξ) - θb ((2:ℝ)^(b+1) * ξ))
      = (fun a : ℤ => θb ((2:ℝ)^a * ξ)) (-(N:ℤ))
        - (fun a : ℤ => θb ((2:ℝ)^a * ξ)) (N:ℤ) := by
    simpa using sum_Ico_sub_int' (fun a : ℤ => θb ((2:ℝ)^a * ξ)) (by omega : -(N:ℤ) ≤ (N:ℤ))
  rw [htel]
  change θb ((2:ℝ)^(-(N:ℤ)) * ξ) - θb ((2:ℝ)^((N:ℤ)) * ξ) = 1
  rw [hone _ (hsmall (-(N:ℤ)) le_rfl), hzero _ (hbig (N:ℤ) le_rfl)]
  ring

end Commons.Analysis.Fourier