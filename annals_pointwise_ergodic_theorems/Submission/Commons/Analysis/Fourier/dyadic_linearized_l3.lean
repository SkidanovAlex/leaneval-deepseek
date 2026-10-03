import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
import Submission.Commons.Analysis.Convolution.integral_inner_convolution_eq_adjoint_meas
import Submission.Commons.Analysis.CalderonZygmund.cz_weak_type_one_measurable_bounded
import Submission.Commons.Analysis.Fourier.block_maximal_of_separated
import Submission.Commons.Analysis.Fourier.bourgain_smooth_window_maximal_l2
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology FourierTransform

namespace Commons.Analysis.Fourier

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Part 1: elementary facts about `K` -/

/-- A Lipschitz function `ℝ → ℂ` is continuous. -/
lemma dl3_lipschitz_continuous (K : ℝ → ℂ)
    (hKlip : ∃ A : ℝ, 0 < A ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ A * |u - v|) :
    Continuous K := by
  obtain ⟨A, hA, hL⟩ := hKlip
  have hLip : LipschitzWith ⟨A, hA.le⟩ K := by
    refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
    rw [dist_eq_norm, Real.dist_eq]
    exact hL u v
  exact hLip.continuous

/-- The stronger elementary bound `(1+|z|)^{-2} ≤ (1+z^2)^{-1}`. -/
lemma dl3_one_add_abs_sq_inv_le (z : ℝ) :
    (1 + |z|) ^ (-2 : ℤ) ≤ (1 + z ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_abs z, abs_nonneg z, sq_nonneg z]

/-- **The decay hypothesis implies integrability.** -/
lemma dl3_integrable (K : ℝ → ℂ) (A : ℝ) (hA : 0 < A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|) :
    MeasureTheory.Integrable K (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hcont := dl3_lipschitz_continuous K hKlip
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul A) hcont.aestronglyMeasurable ?_
  filter_upwards with z
  calc ‖K z‖ ≤ A / (1 + |z|) ^ 2 := hKb z
    _ = A * (1 + |z|) ^ (-2 : ℤ) := by rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
    _ ≤ A * (1 + z ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (dl3_one_add_abs_sq_inv_le z) hA.le

/-! ## Part 2: the lacunary `min` sum -/

/-- For `0 < x ≤ 1` and `N ≥ 0`, `min x (x^{-N}) = x`. -/
lemma dl3_min_eq_left {x N : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hN : 0 ≤ N) :
    min x (x ^ (-N)) = x :=
  min_eq_left (le_trans hx1 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by linarith)))

/-- For `1 ≤ x` and `N ≥ 0`, `min x (x^{-N}) = x^{-N}`. -/
lemma dl3_min_eq_right {x N : ℝ} (hx : 1 ≤ x) (hN : 0 ≤ N) :
    min x (x ^ (-N)) = x ^ (-N) :=
  min_eq_right (le_trans (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith : -N ≤ 0)) hx)

/-- `(2:ℝ)^(-((n:ℤ)+1)) = (1/2)^(n+1)`. -/
lemma dl3_zpow_neg_succ (n : ℕ) : (2:ℝ)^(-((n:ℤ)+1)) = (1/2:ℝ)^(n+1) := by
  rw [show -((n:ℤ)+1) = -(((n+1:ℕ)):ℤ) by push_cast; ring, zpow_neg, zpow_natCast, ← inv_pow]
  norm_num

/-- `(2:ℝ)^((n:ℤ)+1) = 2^(n+1)`. -/
lemma dl3_zpow_pos_succ (n : ℕ) : (2:ℝ)^((n:ℤ)+1) = (2:ℝ)^(n+1) := by
  rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by push_cast; ring, zpow_natCast]

/-- `2 * 2^k = 2^(k+1)` for `k : ℤ`. -/
lemma dl3_two_mul_zpow (k : ℤ) : (2:ℝ) * (2:ℝ)^k = (2:ℝ)^(k+1) := by
  rw [mul_comm]
  exact (zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0) k).symm

/-- `(2:ℝ)^(n+1) = 2^n * 2`. -/
lemma dl3_two_pow_succ (n : ℕ) : (2:ℝ)^(n+1) = (2:ℝ)^n * 2 := pow_succ (2:ℝ) n

/-- `Summable (fun n => (1/2)^(n+1))`. -/
lemma dl3_summable_half : Summable (fun n : ℕ => (1/2:ℝ)^(n+1)) :=
  (summable_nat_add_iff 1).2
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))

/-- Bound for the positive ray: for `0 < c ≤ 1`, `c·(1/2)^{n+1} ≤ (1/2)^{n+1}`. -/
lemma dl3_pos_ray_le (c : ℝ) (hc1 : c ≤ 1) (n : ℕ) :
    c * (1/2:ℝ)^(n+1) ≤ (1/2:ℝ)^(n+1) := by
  calc c * (1/2:ℝ)^(n+1) ≤ 1 * (1/2:ℝ)^(n+1) :=
        mul_le_mul_of_nonneg_right hc1 (by positivity)
    _ = (1/2:ℝ)^(n+1) := one_mul _

/-- Bound for the negative ray: for `1/2 < c` and `N > 0`,
`(c·2^{n+1})^{-N} ≤ ((2^{-N}))^n`. -/
lemma dl3_neg_ray_le (c N : ℝ) (hc : 1/2 < c) (hN : 0 < N) (n : ℕ) :
    (c * (2:ℝ)^(n+1)) ^ (-N) ≤ ((2:ℝ)^(-N))^n := by
  have hx : (2:ℝ)^n ≤ c * (2:ℝ)^(n+1) := by
    have h2n : (0:ℝ) < (2:ℝ)^n := pow_pos (by norm_num) n
    nlinarith [hc, h2n, dl3_two_pow_succ n]
  calc (c * (2:ℝ)^(n+1)) ^ (-N) ≤ ((2:ℝ)^n) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num) n) hx (by linarith)
    _ = ((2:ℝ)^(-N))^n := by
        rw [← Real.rpow_natCast (2:ℝ) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [← Real.rpow_natCast ((2:ℝ)^(-N)) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1; push_cast; ring

/-- For `a > 0` there is an integer scale `l0` with `a * 2^{l0} ≤ 1 < a * 2^{l0+1}`. -/
lemma dl3_exists_scale (a : ℝ) (ha : 0 < a) :
    ∃ l0 : ℤ, a * (2:ℝ)^l0 ≤ 1 ∧ 1 < a * (2:ℝ)^(l0+1) := by
  have h2 : (1:ℝ) < 2 := by norm_num
  refine ⟨⌊Real.logb 2 a⁻¹⌋, ?_, ?_⟩
  · have h1 : ((⌊Real.logb 2 a⁻¹⌋ : ℤ) : ℝ) ≤ Real.logb 2 a⁻¹ := Int.floor_le _
    have h2' : (2:ℝ) ^ ((⌊Real.logb 2 a⁻¹⌋ : ℤ) : ℝ) ≤ (2:ℝ) ^ Real.logb 2 a⁻¹ :=
      (Real.rpow_le_rpow_left_iff h2).mpr h1
    rw [Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr ha), Real.rpow_intCast] at h2'
    have := mul_le_mul_of_nonneg_left h2' ha.le
    rwa [mul_inv_cancel₀ (ne_of_gt ha)] at this
  · have h1 : Real.logb 2 a⁻¹ < ((⌊Real.logb 2 a⁻¹⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h2' : (2:ℝ) ^ Real.logb 2 a⁻¹ < (2:ℝ) ^ (((⌊Real.logb 2 a⁻¹⌋ : ℤ) : ℝ) + 1) :=
      (Real.rpow_lt_rpow_left_iff h2).mpr h1
    rw [Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr ha)] at h2'
    have h3 : (2:ℝ) ^ (((⌊Real.logb 2 a⁻¹⌋ : ℤ) : ℝ) + 1) = (2:ℝ) ^ (⌊Real.logb 2 a⁻¹⌋ + 1) := by
      rw [← Real.rpow_intCast (2:ℝ) (⌊Real.logb 2 a⁻¹⌋ + 1)]
      congr 1; push_cast; ring
    rw [h3] at h2'
    have := mul_lt_mul_of_pos_left h2' ha
    rwa [mul_inv_cancel₀ (ne_of_gt ha)] at this

lemma dl3_rpow_neg_mul_shift (N : ℝ) (n : ℕ) :
    (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1) = ((2:ℝ)^(-N))^n := by
  have h1 : (2:ℝ)^N * (2:ℝ)^(-N) = 1 := by
    rw [show (-N:ℝ) = -(N) by ring, Real.rpow_neg (by positivity),
      mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) N))]
  rw [pow_succ, ← mul_assoc, mul_comm ((2:ℝ)^N) (((2:ℝ)^(-N))^n), mul_assoc, h1, mul_one]

lemma dl3_neg_ray_bound2 (c N : ℝ) (hc : 1/2 < c) (hN : 0 < N) (n : ℕ) :
    (c * (2:ℝ)^(n+1)) ^ (-N) ≤ (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1) := by
  have hx : (2:ℝ)^n ≤ c * (2:ℝ)^(n+1) := by
    rw [dl3_two_pow_succ n]
    have h2n : (0:ℝ) < (2:ℝ)^n := pow_pos (by norm_num) n
    nlinarith [hc, h2n]
  calc (c * (2:ℝ)^(n+1)) ^ (-N) ≤ ((2:ℝ)^n) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num) n) hx (by linarith)
    _ = ((2:ℝ)^(-N))^n := by
        rw [← Real.rpow_natCast (2:ℝ) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [← Real.rpow_natCast ((2:ℝ)^(-N)) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1; push_cast; ring
    _ = (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1) := (dl3_rpow_neg_mul_shift N n).symm

/-- **Lacunary `min` sum.** For `N > 0` there is `B > 0` with, for every `a > 0`, the family
`l ↦ min (a·2^l) ((a·2^l)^{-N})` is summable over `ℤ` with total `≤ B`. -/
lemma dl3_lacunary_min_sum (N : ℝ) (hN : 0 < N) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 < a →
      Summable (fun l : ℤ => min (a * (2:ℝ)^l) ((a * (2:ℝ)^l) ^ (-N))) ∧
      (∑' l : ℤ, min (a * (2:ℝ)^l) ((a * (2:ℝ)^l) ^ (-N))) ≤ B := by
  have h2lt : (2:ℝ)^(-N) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hNnn : (0:ℝ) ≤ N := hN.le
  refine ⟨2 + (1 - (2:ℝ)^(-N))⁻¹ + 1, by positivity, fun a ha => ?_⟩
  obtain ⟨l0, hl0a, hl0b⟩ := dl3_exists_scale a ha
  set c : ℝ := a * (2:ℝ)^l0 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := hl0a
  have hchalf : 1/2 < c := by
    have h2 : a * (2:ℝ)^(l0+1) = 2 * c := by
      rw [hc, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; ring
    rw [h2] at hl0b; linarith
  set G : ℤ → ℝ := fun k => min (c * (2:ℝ)^k) ((c * (2:ℝ)^k) ^ (-N)) with hG
  have hGpos : ∀ k : ℤ, 0 ≤ G k := fun k => le_min (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hfl : ∀ l : ℤ, min (a * (2:ℝ)^l) ((a * (2:ℝ)^l) ^ (-N)) = G (l - l0) := by
    intro l
    have h1 : a * (2:ℝ)^l = c * (2:ℝ)^(l - l0) := by
      rw [hc, show l - l0 = l + (-l0) by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      rw [show (-l0 : ℤ) = -l0 by rfl, zpow_neg]
      field_simp
    simp only [hG, h1]
  have hG1 : ∀ n : ℕ, G ((n:ℤ)+1) = (c * (2:ℝ)^((n:ℤ)+1)) ^ (-N) := by
    intro n
    simp only [hG]
    refine dl3_min_eq_right ?_ hNnn
    rw [dl3_zpow_pos_succ n]
    have h2n : (2:ℝ) ≤ (2:ℝ)^(n+1) := by
      calc (2:ℝ) = (2:ℝ)^1 := by ring
        _ ≤ (2:ℝ)^(n+1) := pow_le_pow_right₀ (by norm_num)
            (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
    nlinarith [hchalf, h2n]
  have hG2 : ∀ n : ℕ, G (-((n:ℤ)+1)) = c * (2:ℝ)^(-((n:ℤ)+1)) := by
    intro n
    simp only [hG]
    refine dl3_min_eq_left (by positivity) ?_ hNnn
    rw [dl3_zpow_neg_succ n]
    have hp1 : (1/2:ℝ)^(n+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [hc1, hp1, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (n+1)]
  have hG0 : G 0 = c := by
    simp only [hG, zpow_zero, mul_one]
    exact dl3_min_eq_left hcpos hc1 hNnn
  have hb1 : ∀ n : ℕ, G ((n:ℤ)+1) ≤ (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1) := by
    intro n
    rw [hG1 n, dl3_zpow_pos_succ n]
    exact dl3_neg_ray_bound2 c N hchalf hN n
  have hb2 : ∀ n : ℕ, G (-((n:ℤ)+1)) ≤ (1/2:ℝ)^(n+1) := by
    intro n
    rw [hG2 n, dl3_zpow_neg_succ n]
    exact dl3_pos_ray_le c hc1 n
  have hsumm1 : Summable (fun n : ℕ => G ((n:ℤ)+1)) := by
    refine Summable.of_nonneg_of_le (fun n => hGpos _) hb1 ?_
    have h := (summable_nat_add_iff 1).2
      (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (2:ℝ)^(-N)) h2lt)
    exact h.mul_left ((2:ℝ)^N)
  have hsumm2 : Summable (fun n : ℕ => G (-((n:ℤ)+1))) := by
    refine Summable.of_nonneg_of_le (fun n => hGpos _) hb2 dl3_summable_half
  have hsumm : Summable G := Summable.of_add_one_of_neg_add_one hsumm1 hsumm2
  have htsum1 : (∑' n : ℕ, G ((n:ℤ)+1)) ≤ (1 - (2:ℝ)^(-N))⁻¹ := by
    calc (∑' n : ℕ, G ((n:ℤ)+1)) ≤ ∑' n : ℕ, (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1) := by
          apply Summable.tsum_le_tsum hb1 hsumm1
          have h := (summable_nat_add_iff 1).2
            (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (2:ℝ)^(-N)) h2lt)
          exact h.mul_left ((2:ℝ)^N)
      _ = (1 - (2:ℝ)^(-N))⁻¹ := by
          rw [show (∑' n : ℕ, (2:ℝ)^N * ((2:ℝ)^(-N))^(n+1))
              = (2:ℝ)^N * ∑' n : ℕ, ((2:ℝ)^(-N))^(n+1) by rw [tsum_mul_left]]
          rw [show (∑' n : ℕ, ((2:ℝ)^(-N))^(n+1)) = (2:ℝ)^(-N) * ∑' n : ℕ, ((2:ℝ)^(-N))^n by
            rw [← tsum_mul_left]; apply tsum_congr; intro n; rw [pow_succ']]
          rw [tsum_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (2:ℝ)^(-N)) h2lt]
          rw [show (-N:ℝ) = -(N) by ring, Real.rpow_neg (by positivity)]
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) N)),
            one_mul]
  have htsum2 : (∑' n : ℕ, G (-((n:ℤ)+1))) ≤ 1 := by
    calc (∑' n : ℕ, G (-((n:ℤ)+1))) ≤ ∑' n : ℕ, (1/2:ℝ)^(n+1) :=
          Summable.tsum_le_tsum hb2 hsumm2 dl3_summable_half
      _ = 1 := by
          rw [show (∑' n : ℕ, (1/2:ℝ)^(n+1)) = ∑' n : ℕ, (1/2:ℝ) * (1/2:ℝ)^n by
            apply tsum_congr; intro n; rw [pow_succ']]
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
          norm_num
  have htsumG : (∑' k : ℤ, G k) ≤ 2 + (1 - (2:ℝ)^(-N))⁻¹ := by
    rw [tsum_of_add_one_of_neg_add_one hsumm1 hsumm2]
    have h0 : G 0 ≤ 1 := by rw [hG0]; exact hc1
    linarith
  constructor
  · rw [show (fun l : ℤ => min (a * (2:ℝ)^l) ((a * (2:ℝ)^l) ^ (-N)))
        = fun l : ℤ => G (l - l0) from funext hfl]
    exact (Equiv.summable_iff (Equiv.addRight (-l0))).mpr hsumm
  · rw [show (∑' l : ℤ, min (a * (2:ℝ)^l) ((a * (2:ℝ)^l) ^ (-N)))
        = ∑' l : ℤ, G (l - l0) from tsum_congr hfl]
    rw [show (∑' l : ℤ, G (l - l0)) = ∑' k : ℤ, G k from
      Equiv.tsum_eq (Equiv.addRight (-l0)) G]
    linarith [htsumG]


/-! ## Part 3: the linearized kernel, its Fourier transform -/

/-- The single dilated term `2^l · K(2^l ·)`. -/
noncomputable def dl3Phi (K : ℝ → ℂ) (l : ℤ) : ℝ → ℂ :=
  fun z => (2:ℝ)^l * K ((2:ℝ)^l * z)

/-- The linearized dyadic dilation kernel `∑_{l∈F} e_l · 2^l K(2^l ·)`. -/
noncomputable def dl3Kappa (K : ℝ → ℂ) (F : Finset ℤ) (e : ℤ → ℂ) : ℝ → ℂ :=
  fun z => ∑ l ∈ F, e l * dl3Phi K l z

/-- The kernel in the exact form appearing in the target statement. -/
lemma dl3Kappa_apply_eq (K : ℝ → ℂ) (F : Finset ℤ) (e : ℤ → ℂ) (x y : ℝ) :
    dl3Kappa K F e (x - y) = ∑ l ∈ F, e l * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l)) := by
  simp only [dl3Kappa, dl3Phi]
  apply Finset.sum_congr rfl
  intro l _
  congr 2
  rw [mul_comm]

/-- Norm of a dilated term. -/
lemma dl3Phi_norm (K : ℝ → ℂ) (l : ℤ) (z : ℝ) :
    ‖dl3Phi K l z‖ = (2:ℝ)^l * ‖K ((2:ℝ)^l * z)‖ := by
  rw [dl3Phi, norm_mul]
  congr 1
  rw [norm_zpow]
  have h : ‖(Complex.ofReal 2 : ℂ)‖ = (2:ℝ) := by norm_num
  rw [h]

/-- Integrability of a dilated term. -/
lemma dl3Phi_integrable (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K) (l : ℤ) :
    MeasureTheory.Integrable (dl3Phi K l) := by
  have hc : (0:ℝ) < (2:ℝ)^l := zpow_pos (by norm_num) l
  refine ((hK.comp_smul hc.ne').const_mul (Complex.ofReal ((2:ℝ)^l))).congr ?_
  filter_upwards with z
  simp only [dl3Phi, smul_eq_mul]
  rw [← Complex.ofReal_zpow]

/-- Integrability of the linearized kernel. -/
lemma dl3Kappa_integrable (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (F : Finset ℤ) (e : ℤ → ℂ) : MeasureTheory.Integrable (dl3Kappa K F e) := by
  classical
  show MeasureTheory.Integrable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
  exact integrable_finsetSum F (fun l _ => (dl3Phi_integrable K hK l).const_mul (e l))

/-- `dl3Kappa` is bounded when `K` is (with explicit constant). -/
lemma dl3Kappa_bound (K : ℝ → ℂ) (A : ℝ)
    (_hA : 0 ≤ A) (hKb : ∀ z : ℝ, ‖K z‖ ≤ A) (F : Finset ℤ) (e : ℤ → ℂ)
    (he : ∀ l, ‖e l‖ ≤ 1) :
    ∀ z : ℝ, ‖dl3Kappa K F e z‖ ≤ ∑ l ∈ F, A * (2:ℝ)^l := by
  intro z
  have h2l : ∀ l : ℤ, (0:ℝ) ≤ (2:ℝ)^l := fun l => zpow_nonneg (by norm_num) l
  calc ‖dl3Kappa K F e z‖ ≤ ∑ l ∈ F, ‖e l * dl3Phi K l z‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ F, A * (2:ℝ)^l := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul, dl3Phi_norm]
        calc ‖e l‖ * ((2:ℝ)^l * ‖K ((2:ℝ)^l * z)‖) ≤ 1 * ((2:ℝ)^l * A) := by
              apply mul_le_mul (he l) (mul_le_mul_of_nonneg_left (hKb _) (h2l l)) (by positivity)
                (by norm_num)
          _ = A * (2:ℝ)^l := by ring

/-- The Fourier transform, written with the explicit Fourier character. -/
lemma dl3_fourier_eq_mul (g : ℝ → ℂ) (w : ℝ) :
    𝓕 g w = ∫ v : ℝ, (Real.fourierChar (-(v * w)) : ℂ) * g v := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  rw [Circle.smul_def, smul_eq_mul, Real.inner_apply]

/-! ## Part 4: the symbol bound -/

/-- `‖e^{2πix} - 1‖ ≤ 2π|x|`. -/
lemma dl3_fourierChar_sub_one (x : ℝ) :
    ‖(Real.fourierChar x : ℂ) - 1‖ ≤ 2 * Real.pi * |x| := by
  rw [Real.fourierChar_apply]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * x)
  rw [mul_comm Complex.I (↑(2 * Real.pi * x) : ℂ)] at h
  calc ‖Complex.exp (↑(2 * Real.pi * x) * Complex.I) - 1‖ ≤ ‖(2 * Real.pi * x : ℝ)‖ := h
    _ = 2 * Real.pi * |x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg Real.pi_pos.le]

/-- **Vanishing of `𝓕K` at `0`** (with derivative bound): for a mean-zero `L¹` function `K` with
`x·K(x)` integrable, `‖𝓕K(u)‖ ≤ 2π|u| ∫‖xK(x)‖`. -/
lemma dl3_fourier_le_abs_mul_of_integral_zero (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x)) (h0 : ∫ x : ℝ, K x = 0)
    (u : ℝ) :
    ‖𝓕 K u‖ ≤ 2 * Real.pi * |u| * ∫ x : ℝ, ‖x • K x‖ := by
  have hφK : MeasureTheory.Integrable
      (fun v : ℝ => (Real.fourierChar (-(v * u)) : ℂ) * K v) :=
    hK.bdd_mul (c := 1) (f := fun v : ℝ => (Real.fourierChar (-(v * u)) : ℂ))
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun v => by rw [Circle.norm_coe]))
  rw [dl3_fourier_eq_mul K u]
  have hmain : (∫ v : ℝ, (Real.fourierChar (-(v * u)) : ℂ) * K v)
      = ∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v := by
    have h2 : (∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ) * K v - K v))
        = (∫ v : ℝ, (Real.fourierChar (-(v * u)) : ℂ) * K v) - ∫ v : ℝ, K v :=
      MeasureTheory.integral_sub hφK hK
    rw [h0, sub_zero] at h2
    rw [← h2]
    apply integral_congr_ae
    filter_upwards with v
    ring
  rw [hmain]
  have hint1 : MeasureTheory.Integrable
      (fun v : ℝ => ((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v) := by
    refine (hφK.sub hK).congr (Filter.Eventually.of_forall (fun v => ?_))
    change (Real.fourierChar (-(v * u)) : ℂ) * K v - K v
      = ((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v
    ring
  have hint2 : MeasureTheory.Integrable (fun v : ℝ => (2 * Real.pi * |u|) * ‖v • K v‖) :=
    hKx.norm.const_mul _
  have hpt : ∀ v : ℝ, ‖((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v‖
      ≤ (2 * Real.pi * |u|) * ‖v • K v‖ := by
    intro v
    have h1 := dl3_fourierChar_sub_one (-(v * u))
    rw [norm_mul, norm_smul, Real.norm_eq_abs]
    calc ‖(Real.fourierChar (-(v * u)) : ℂ) - 1‖ * ‖K v‖
        ≤ (2 * Real.pi * |(-(v * u))|) * ‖K v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 * Real.pi * |u|) * (|v| * ‖K v‖) := by rw [abs_neg, abs_mul]; ring
  calc ‖∫ v : ℝ, ((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v‖
      ≤ ∫ v : ℝ, ‖((Real.fourierChar (-(v * u)) : ℂ) - 1) * K v‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, (2 * Real.pi * |u|) * ‖v • K v‖ :=
        MeasureTheory.integral_mono hint1.norm hint2 hpt
    _ = 2 * Real.pi * |u| * ∫ x : ℝ, ‖x • K x‖ := MeasureTheory.integral_const_mul _ _

/-- `(1+u)^{-N} ≤ u^{-N}` for `u > 0`, `N > 0`. -/
lemma dl3_one_add_rpow_neg_le (N : ℝ) (hN : 0 < N) {u : ℝ} (hu : 0 < u) :
    (1 + u) ^ (-N) ≤ u ^ (-N) := by
  have h1 : u ^ N ≤ (1 + u) ^ N := Real.rpow_le_rpow hu.le (by linarith) hN.le
  rw [Real.rpow_neg hu.le, Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + u)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos hu _)).mpr h1

/-- **The symbol of the linearized operator is bounded**, uniformly in the finite scale set `F`
and the coefficients `e_l`, `‖e_l‖ ≤ 1`. -/
lemma dl3_symbol_bound (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x : ℝ, K x = 0) (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x))
    (C N : ℝ) (hC : 0 < C) (hN : 0 < N)
    (hdec : ∀ ξ : ℝ, ‖𝓕 K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ ξ : ℝ,
      ‖∑ l ∈ F, e l * 𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ A := by
  obtain ⟨B, hBpos, hB⟩ := dl3_lacunary_min_sum N hN
  set L : ℝ := 2 * Real.pi * ∫ x : ℝ, ‖x • K x‖ with hL
  have hLnn : 0 ≤ L := by rw [hL]; positivity
  have hLip : ∀ η : ℝ, ‖𝓕 K η‖ ≤ L * |η| := fun η => by
    have h := dl3_fourier_le_abs_mul_of_integral_zero K hK hKx hK0 η
    rw [hL]
    calc ‖𝓕 K η‖ ≤ 2 * Real.pi * |η| * ∫ x : ℝ, ‖x • K x‖ := h
      _ = (2 * Real.pi * ∫ x : ℝ, ‖x • K x‖) * |η| := by ring
  have hterm : ∀ ξ : ℝ, ∀ l : ℤ, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖
      ≤ max L C * min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) := by
    intro ξ l
    let u : ℝ := |ξ| * (2:ℝ)^(-l)
    have hu : u = |ξ| * (2:ℝ)^(-l) := rfl
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have h2lp : (0:ℝ) < (2:ℝ)^(-l) := zpow_pos (by norm_num) _
    have habs : |(2:ℝ)^(-l) * ξ| = u := by
      rw [hu, abs_mul, abs_of_pos h2lp, mul_comm]
    have hmax0 : 0 ≤ max L C := le_trans hC.le (le_max_right L C)
    have hmin : min (L * u) (C * (1 + u) ^ (-N)) ≤ max L C * min u ((1 + u) ^ (-N)) := by
      calc min (L * u) (C * (1 + u) ^ (-N))
          ≤ min (max L C * u) (max L C * (1 + u) ^ (-N)) :=
            min_le_min (mul_le_mul_of_nonneg_right (le_max_left L C) hu0)
              (mul_le_mul_of_nonneg_right (le_max_right L C) (by positivity))
        _ = max L C * min u ((1 + u) ^ (-N)) := (mul_min_of_nonneg u _ hmax0).symm
    have hcmp : min u ((1 + u) ^ (-N)) ≤ min u (u ^ (-N)) := by
      rcases eq_or_lt_of_le hu0 with h | h
      · have hz : (0:ℝ) ^ (-N) = 0 := Real.zero_rpow (by linarith : (-N) ≠ 0)
        rw [← h, add_zero, Real.one_rpow, hz, min_eq_left (by norm_num : (0:ℝ) ≤ 1), min_self]
      · exact min_le_min_left _ (dl3_one_add_rpow_neg_le N hN h)
    have h1 : ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ L * u := by
      have := hLip ((2:ℝ)^(-l) * ξ); rwa [habs] at this
    have h2b : ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ C * (1 + u) ^ (-N) := by
      have := hdec ((2:ℝ)^(-l) * ξ); rwa [habs] at this
    calc ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ ≤ min (L * u) (C * (1 + u) ^ (-N)) := le_min h1 h2b
      _ ≤ max L C * min u ((1 + u) ^ (-N)) := hmin
      _ ≤ max L C * min u (u ^ (-N)) := mul_le_mul_of_nonneg_left hcmp hmax0
  refine ⟨max L C * B + 1, by positivity, fun F e he ξ => ?_⟩
  have hmax0 : 0 ≤ max L C := le_trans hC.le (le_max_right L C)
  have hnonneg : ∀ l : ℤ, 0 ≤ min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) :=
    fun l => le_min (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hsum : ∑ l ∈ F, min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) ≤ B := by
    rcases eq_or_lt_of_le (abs_nonneg ξ) with hξ | hξ
    · have hξ0 : ξ = 0 := abs_eq_zero.mp hξ.symm
      have hzero : ∀ l : ℤ, min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) = 0 := by
        intro l
        rw [hξ0, abs_zero, zero_mul,
          Real.zero_rpow (by linarith : (-N) ≠ 0)]
        exact min_eq_left le_rfl
      rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const, smul_zero]
      exact hBpos.le
    · obtain ⟨hsumm, htsum⟩ := hB |ξ| hξ
      have hsumm' : Summable (fun l : ℤ => min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N))) :=
        (Equiv.summable_iff (Equiv.neg ℤ)
          (f := fun l : ℤ => min (|ξ| * (2:ℝ)^l) ((|ξ| * (2:ℝ)^l) ^ (-N)))).mpr hsumm
      refine le_trans (Summable.sum_le_tsum F (fun l _ => hnonneg l) hsumm') ?_
      rw [show (∑' l : ℤ, min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)))
          = ∑' l : ℤ, min (|ξ| * (2:ℝ)^l) ((|ξ| * (2:ℝ)^l) ^ (-N)) from
        Equiv.tsum_eq (Equiv.neg ℤ)
          (fun l : ℤ => min (|ξ| * (2:ℝ)^l) ((|ξ| * (2:ℝ)^l) ^ (-N)))]
      exact htsum
  calc ‖∑ l ∈ F, e l * 𝓕 K ((2:ℝ)^(-l) * ξ)‖
      ≤ ∑ l ∈ F, ‖e l * 𝓕 K ((2:ℝ)^(-l) * ξ)‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ F, ‖𝓕 K ((2:ℝ)^(-l) * ξ)‖ := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (he l)
    _ ≤ ∑ l ∈ F, max L C * min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) :=
        Finset.sum_le_sum (fun l _ => hterm ξ l)
    _ = max L C * ∑ l ∈ F, min (|ξ| * (2:ℝ)^(-l)) ((|ξ| * (2:ℝ)^(-l)) ^ (-N)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ max L C * B := mul_le_mul_of_nonneg_left hsum hmax0
    _ ≤ max L C * B + 1 := le_add_of_nonneg_right (by norm_num)


/-! ## Part 5: the `L²` bound -/

/-- The Fourier transform of an integrable function is continuous. -/
lemma dl3_continuous_fourier (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K) :
    Continuous (𝓕 K) :=
  VectorFourier.fourierIntegral_continuous (μ := MeasureTheory.volume)
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hK

/-- The linearized operator in "convolution" form: `f ↦ ∫ y, f y · κ(x - y)` with
`κ = ∑_{l∈F} e_l · 2^l K(2^l ·)`. -/
noncomputable def dl3Op (K : ℝ → ℂ) (F : Finset ℤ) (e : ℤ → ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ y : ℝ, f y * dl3Kappa K F e (x - y)

/-! ## Part 6: the lacunary kernel-difference sum and the weak `(1,1)` bound -/

/-- Volume of `{|u| ≤ R}`. -/
lemma dl3_volume_abs_le (R : ℝ) : MeasureTheory.volume {u : ℝ | |u| ≤ R} = ENNReal.ofReal (2*R) := by
  have h : {u : ℝ | |u| ≤ R} = Set.Icc (-R) R := by
    ext u; simp [abs_le]
  rw [h, Real.volume_Icc]; ring_nf

/-- `∫⁻_{u > R} (u^2)^{-1} = 1/R` for `R > 0`. -/
lemma dl3_lintegral_Ioi_inv_sq (R : ℝ) (hR : 0 < R) :
    ∫⁻ u : ℝ in Set.Ioi R, ENNReal.ofReal ((u^2)⁻¹) = ENNReal.ofReal (1/R) := by
  have h : ∫⁻ u : ℝ in Set.Ioi R, ENNReal.ofReal ((u^2)⁻¹)
      = ∫⁻ u : ℝ in Set.Ioi R, ENNReal.ofReal (u ^ (-2:ℝ)) := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only
    congr 1
    change (u^2)⁻¹ = u ^ (-2:ℝ)
    rw [show (-2:ℝ) = -(2:ℝ) by ring, Real.rpow_neg (le_of_lt (hR.trans hu))]
    exact (inv_inj.mpr (Real.rpow_natCast u 2)).symm
  rw [h, Commons.MeasureTheory.Integral.lintegral_Ioi_rpow_eq (-2) R (by norm_num) hR]
  congr 1
  rw [show ((-2:ℝ) + 1) = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- `∫⁻_{|u| > R} (u^2)^{-1} = 2/R` for `R > 0`. -/
lemma dl3_lintegral_abs_tail_inv_sq (R : ℝ) (hR : 0 < R) :
    ∫⁻ u : ℝ in {u : ℝ | R < |u|}, ENNReal.ofReal ((u^2)⁻¹) = ENNReal.ofReal (2/R) := by
  have hset : {u : ℝ | R < |u|} = Set.Ioi R ∪ Set.Iio (-R) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro h
      rcases lt_or_ge (0:ℝ) u with hu | hu
      · exact Or.inl (by rwa [abs_of_pos hu] at h)
      · exact Or.inr (by rw [abs_of_nonpos hu] at h; linarith)
    · rintro (h | h)
      · rw [abs_of_pos (hR.trans h)]; exact h
      · rw [abs_of_neg (by linarith)]; linarith
  have hdisj : Disjoint (Set.Ioi R) (Set.Iio (-R)) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_Ioi] at hu
    simp only [Set.mem_Iio] at hu'
    linarith
  have hrefl : ∫⁻ u : ℝ in Set.Iio (-R), ENNReal.ofReal ((u^2)⁻¹)
      = ∫⁻ u : ℝ in Set.Ioi R, ENNReal.ofReal ((u^2)⁻¹) := by
    have hmp : MeasureTheory.MeasurePreserving (fun u : ℝ => -u)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
      MeasureTheory.Measure.measurePreserving_neg _
    have hemb : MeasurableEmbedding (fun u : ℝ => -u) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [← MeasureTheory.lintegral_indicator measurableSet_Iio
        (f := fun u : ℝ => ENNReal.ofReal ((u^2)⁻¹)),
      ← MeasureTheory.lintegral_indicator measurableSet_Ioi
        (f := fun u : ℝ => ENNReal.ofReal ((u^2)⁻¹))]
    rw [← hmp.lintegral_comp_emb hemb (fun v : ℝ =>
      (Set.Ioi R).indicator (fun u => ENNReal.ofReal ((u^2)⁻¹)) v)]
    apply MeasureTheory.lintegral_congr
    intro u
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi, neg_neg]
    by_cases h : u < -R
    · rw [if_pos h, if_pos (by linarith)]; ring_nf
    · rw [if_neg h, if_neg (by linarith)]
  rw [hset, MeasureTheory.lintegral_union measurableSet_Iio hdisj, hrefl,
    dl3_lintegral_Ioi_inv_sq R hR]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  norm_num

/-- Scaling change of variables for a set-lintegral. -/
lemma dl3_setLIntegral_comp_mul_left (a R : ℝ) (ha : 0 < a) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|}, G (a * x)
      = ENNReal.ofReal (a⁻¹) * ∫⁻ u : ℝ in {u : ℝ | R * a ≤ |u|}, G u := by
  have hset : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const measurable_abs
  have hset' : MeasurableSet {u : ℝ | R * a ≤ |u|} := measurableSet_le measurable_const measurable_abs
  have key : ∀ x : ℝ, ({u : ℝ | R * a ≤ |u|}.indicator G) (a * x)
      = ({x : ℝ | R ≤ |x|}.indicator (fun x => G (a * x))) x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    have hx : (R * a ≤ |a * x|) ↔ (R ≤ |x|) := by
      rw [abs_mul, abs_of_pos ha]
      constructor <;> intro h <;> nlinarith
    by_cases h : R ≤ |x|
    · rw [if_pos (hx.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hx.mp hc)), if_neg h]
  rw [← MeasureTheory.lintegral_indicator hset]
  rw [show (∫⁻ x : ℝ, ({x : ℝ | R ≤ |x|}.indicator (fun x => G (a * x))) x)
      = ∫⁻ x : ℝ, ({u : ℝ | R * a ≤ |u|}.indicator G) (a * x) from
        MeasureTheory.lintegral_congr (fun x => (key x).symm)]
  rw [← MeasureTheory.lintegral_map (g := fun x : ℝ => a * x)
      (hf := hG.indicator hset') (hg := measurable_const_mul a)]
  rw [Real.map_volume_mul_left (ne_of_gt ha), MeasureTheory.lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr ha), smul_eq_mul]
  congr 1
  exact MeasureTheory.lintegral_indicator hset' G

/-- Splitting a set-lintegral of a sum. -/
lemma dl3_setLIntegral_add (s : Set ℝ) (f g : ℝ → ℝ≥0∞) (hs : MeasurableSet s)
    (hf : Measurable f) :
    ∫⁻ u : ℝ in s, (f u + g u) = (∫⁻ u : ℝ in s, f u) + (∫⁻ u : ℝ in s, g u) := by
  rw [← MeasureTheory.lintegral_indicator hs, ← MeasureTheory.lintegral_indicator hs,
    ← MeasureTheory.lintegral_indicator hs]
  rw [show (fun u : ℝ => s.indicator (fun u => f u + g u) u)
      = fun u => s.indicator f u + s.indicator g u from by
    funext u; by_cases h : u ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]]
  exact MeasureTheory.lintegral_add_left (hf.indicator hs) _

/-- `((1/4):ℝ)^(1/2) = 1/2`. -/
lemma dl3_quarter_rpow : ((1/4:ℝ)) ^ (1/2:ℝ) = 1/2 := by
  rw [show (1/4:ℝ) = (1/2)^2 by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

/-- The one-half power of `1/√2` is below `1`. -/
lemma dl3_inv_sqrt_two_lt_one : ((Real.sqrt 2))⁻¹ < 1 := by
  rw [inv_lt_one₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
  calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `2^{-N/2} = (1/√2)^N`. -/
lemma dl3_two_rpow_half_neg (N : ℕ) :
    (((2:ℝ) ^ N)⁻¹) ^ (1/2:ℝ) = ((Real.sqrt 2))⁻¹ ^ N := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  calc (((2:ℝ) ^ N)⁻¹) ^ (1/2:ℝ)
      = (((2:ℝ) ^ (N:ℝ))⁻¹) ^ (1/2:ℝ) := by rw [Real.rpow_natCast]
    _ = ((2:ℝ) ^ (-(N:ℝ))) ^ (1/2:ℝ) := by rw [Real.rpow_neg h2]
    _ = (2:ℝ) ^ ((-(N:ℝ)) * (1/2:ℝ)) := by rw [Real.rpow_mul h2]
    _ = (2:ℝ) ^ ((-((2:ℝ)⁻¹)) * (N:ℝ)) := by
        rw [show (-(N:ℝ)) * (1/2:ℝ) = (-((2:ℝ)⁻¹)) * (N:ℝ) by ring]
    _ = ((2:ℝ) ^ (-((2:ℝ)⁻¹))) ^ (N:ℝ) := by rw [Real.rpow_mul h2]
    _ = ((2:ℝ) ^ (-((2:ℝ)⁻¹))) ^ N := by rw [Real.rpow_natCast]
    _ = ((Real.sqrt 2))⁻¹ ^ N := by
        congr 1
        rw [show (-((2:ℝ)⁻¹)) = (-1:ℝ)/2 by norm_num]
        rw [Real.sqrt_eq_rpow (2:ℝ)]
        rw [show ((-1:ℝ)/2) = -((1:ℝ)/2) by norm_num]
        exact Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((1:ℝ)/2)

/-- `(√2)⁻¹ ≤ 3/4`. -/
lemma dl3_inv_sqrt_two_le_three_quarters : ((Real.sqrt 2))⁻¹ ≤ 3/4 := by
  have hp : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [inv_le_iff_one_le_mul₀ hp]
  nlinarith [hp, h2]

/-- **Lacunary lower sum.** If `c·2^m ≤ 1` and `s` consists of scales `l ≤ m`, then
`∑_{l∈s}(c·2^l)^{1/2} ≤ 4`. -/
lemma dl3_lacunary_low_sum (c : ℝ) (hc : 0 ≤ c) (m : ℤ) (s : Finset ℤ)
    (hcm : c * (2:ℝ)^m ≤ 1) (hs : ∀ l ∈ s, l ≤ m) :
    ∑ l ∈ s, (c * (2:ℝ)^l) ^ (1/2:ℝ) ≤ 4 := by
  have h2pos : ∀ l : ℤ, (0:ℝ) < (2:ℝ)^l := fun l => zpow_pos (by norm_num) l
  have hpt : ∀ l ∈ s, (c * (2:ℝ)^l) ^ (1/2:ℝ) ≤ ((Real.sqrt 2))⁻¹ ^ ((m - l).toNat) := by
    intro l hl
    have hl' : l ≤ m := hs l hl
    have hnl : (0:ℤ) ≤ m - l := by omega
    have h1 : c * (2:ℝ)^l ≤ (2:ℝ)^(-(m - l)) := by
      rw [zpow_neg, inv_eq_one_div, le_div_iff₀ (h2pos (m - l))]
      have hsplit : c * (2:ℝ)^l * (2:ℝ)^(m - l) = c * (2:ℝ)^m := by
        rw [mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        congr 2
        omega
      rw [hsplit]
      exact hcm
    have h2 : (c * (2:ℝ)^l) ^ (1/2:ℝ) ≤ ((2:ℝ)^(-(m - l))) ^ (1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((2:ℝ)^(-(m - l))) ^ (1/2:ℝ) = ((Real.sqrt 2))⁻¹ ^ ((m - l).toNat) := by
      rw [show (-(m - l) : ℤ) = -(((m - l).toNat : ℤ)) by rw [Int.toNat_of_nonneg hnl],
        zpow_neg, zpow_natCast]
      exact dl3_two_rpow_half_neg ((m - l).toNat)
    linarith [h2, le_of_eq h3]
  calc ∑ l ∈ s, (c * (2:ℝ)^l) ^ (1/2:ℝ)
      ≤ ∑ l ∈ s, ((Real.sqrt 2))⁻¹ ^ (m - l).toNat := Finset.sum_le_sum hpt
    _ = ∑ j ∈ s.image (fun l => (m - l).toNat), ((Real.sqrt 2))⁻¹ ^ j := by
        rw [Finset.sum_image]
        intro l1 hl1 l2 hl2 heq
        have h1 : (0:ℤ) ≤ m - l1 := by have := hs l1 hl1; omega
        have h2 : (0:ℤ) ≤ m - l2 := by have := hs l2 hl2; omega
        have h4 := congrArg (fun n : ℕ => (n : ℤ)) heq
        simp only [] at h4
        rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at h4
        omega
    _ ≤ ∑' j : ℕ, (3/4:ℝ) ^ j := by
        have h33 : (0:ℝ) ≤ 3/4 := by norm_num
        have h34 : (3:ℝ)/4 < 1 := by norm_num
        have hsum34 : Summable (fun j : ℕ => (3/4:ℝ)^j) :=
          summable_geometric_of_lt_one h33 h34
        have hsumR : Summable (fun j : ℕ => ((Real.sqrt 2))⁻¹ ^ j) :=
          summable_geometric_of_lt_one (by positivity) dl3_inv_sqrt_two_lt_one
        refine le_trans (Summable.sum_le_tsum (s.image (fun l => (m - l).toNat))
          (fun j _ => by positivity) hsumR) ?_
        exact Summable.tsum_le_tsum (fun j => pow_le_pow_left₀ (by positivity)
          dl3_inv_sqrt_two_le_three_quarters j) hsumR hsum34
    _ = 4 := by
        rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3:ℝ)/4 < 1)]
        norm_num

/-- **Lacunary upper sum.** If `s` consists of scales `l > m`, then
`∑_{l∈s} c·2^{-l} ≤ 2·c·2^{-m}`. -/
lemma dl3_lacunary_high_sum (c : ℝ) (hc : 0 ≤ c) (m : ℤ) (s : Finset ℤ)
    (hs : ∀ l ∈ s, m < l) :
    ∑ l ∈ s, c * (2:ℝ)^(-l) ≤ c * (2:ℝ)^(-m) := by
  have h2pos : ∀ l : ℤ, (0:ℝ) < (2:ℝ)^l := fun l => zpow_pos (by norm_num) l
  have hbase : c * (2:ℝ)^(-(m+1)) * 2 = c * (2:ℝ)^(-m) := by
    rw [show (-m : ℤ) = -(m+1) + 1 by ring, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
      zpow_one]
    ring
  have hpt : ∀ l ∈ s, c * (2:ℝ)^(-l) ≤ c * (2:ℝ)^(-(m+1)) * (1/2:ℝ)^((l-m-1).toNat) := by
    intro l hl
    have hl' : m < l := hs l hl
    have hnl : (0:ℤ) ≤ l - m - 1 := by omega
    have h1 : (2:ℝ)^(-l) = (2:ℝ)^(-(m+1)) * (2:ℝ)^(-(l - m - 1)) := by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      congr 1; omega
    have h2 : (2:ℝ)^(-(l - m - 1)) = (1/2:ℝ)^((l-m-1).toNat) := by
      rw [show (-(l-m-1) : ℤ) = -(((l-m-1).toNat : ℤ)) by rw [Int.toNat_of_nonneg hnl],
        zpow_neg, zpow_natCast]
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by rw [one_div], inv_pow]
    rw [h1, h2, mul_assoc]
  calc ∑ l ∈ s, c * (2:ℝ)^(-l)
      ≤ ∑ l ∈ s, c * (2:ℝ)^(-(m+1)) * (1/2:ℝ)^((l-m-1).toNat) := Finset.sum_le_sum hpt
    _ = c * (2:ℝ)^(-(m+1)) * ∑ l ∈ s, (1/2:ℝ)^((l-m-1).toNat) := by
        rw [Finset.mul_sum]
    _ ≤ c * (2:ℝ)^(-(m+1)) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ l ∈ s, (1/2:ℝ)^((l-m-1).toNat)
            = ∑ j ∈ s.image (fun l => (l-m-1).toNat), (1/2:ℝ)^j := by
              rw [Finset.sum_image]
              intro l1 hl1 l2 hl2 heq
              have h1 : (0:ℤ) ≤ l1 - m - 1 := by have := hs l1 hl1; omega
              have h2 : (0:ℤ) ≤ l2 - m - 1 := by have := hs l2 hl2; omega
              have h4 := congrArg (fun n : ℕ => (n : ℤ)) heq
              simp only [] at h4
              rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at h4
              omega
          _ ≤ ∑' j : ℕ, (1/2:ℝ)^j :=
              Summable.sum_le_tsum (f := fun j : ℕ => (1/2:ℝ)^j)
                (s.image (fun l => (l-m-1).toNat)) (fun j _ => by positivity)
                (summable_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
                  (show (1:ℝ)/2 < 1 by norm_num))
          _ = 2 := by
            rw [tsum_geometric_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
              (show (1:ℝ)/2 < 1 by norm_num)]
            norm_num
    _ = c * (2:ℝ)^(-m) := hbase



/-! ## Part 8: the adjoint kernel, the adjoint pairing and the `L^3` bound -/

/-- `conj (𝐞 t) = 𝐞 (-t)`. -/
lemma dl3_fourierChar_conj (t : ℝ) :
    star ((Real.fourierChar t : ℂ)) = (Real.fourierChar (-t) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply,
    show 2 * Real.pi * -t = -(2 * Real.pi * t) by ring, Complex.ofReal_neg, neg_mul,
    ← starRingEnd_apply, ← Complex.exp_conj, starRingEnd_apply]
  congr 1
  have hI : star Complex.I = -Complex.I := by simp [Complex.conj_I]
  have hr : star (((2:ℝ) * Real.pi * t : ℝ) : ℂ) = (((2:ℝ) * Real.pi * t : ℝ) : ℂ) := by
    simp
  rw [star_mul, hI, hr]
  ring

/-- `star (∫ f) = ∫ star f`. -/
lemma dl3_star_integral (f : ℝ → ℂ) : star (∫ x : ℝ, f x) = ∫ x : ℝ, star (f x) := by
  simp only [← starRingEnd_apply]
  exact integral_conj.symm

/-- The reflected conjugate kernel `K^♯(z) = conj (K (-z))`. -/
noncomputable def dl3Ksharp (K : ℝ → ℂ) : ℝ → ℂ := fun z => star (K (-z))

lemma dl3Ksharp_bounded (K : ℝ → ℂ) (A : ℝ)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2) :
    ∀ z : ℝ, ‖dl3Ksharp K z‖ ≤ A / (1 + |z|) ^ 2 := by
  intro z
  simpa [dl3Ksharp, norm_neg] using hKb (-z)

lemma dl3Ksharp_lipschitz (K : ℝ → ℂ) (B : ℝ)
    (hKlip : ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|) :
    ∀ u v : ℝ, ‖dl3Ksharp K u - dl3Ksharp K v‖ ≤ B * |u - v| := by
  intro u v
  have h1 : dl3Ksharp K u - dl3Ksharp K v = star (K (-u) - K (-v)) := by
    simp only [dl3Ksharp, ← star_sub]
  rw [h1, norm_star]
  have := hKlip (-u) (-v)
  rw [show -u - -v = -(u - v) by ring, abs_neg] at this
  exact this

lemma dl3Ksharp_integrable (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K) :
    MeasureTheory.Integrable (dl3Ksharp K) :=
  (hK.comp_neg).congr' ((hK.comp_neg).aestronglyMeasurable.star)
    (Filter.Eventually.of_forall (fun z => by simp [dl3Ksharp]))

lemma dl3Ksharp_x_integrable (K : ℝ → ℂ)
    (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x)) :
    MeasureTheory.Integrable (fun z : ℝ => z • dl3Ksharp K z) := by
  have h1 : MeasureTheory.Integrable
      (fun z : ℝ => star ((fun x : ℝ => x • K x) (-z))) :=
    (hKx.comp_neg).congr' ((hKx.comp_neg).aestronglyMeasurable.star)
      (Filter.Eventually.of_forall (fun z => by simp))
  refine h1.neg.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Pi.neg_apply, dl3Ksharp]
  rw [star_smul]
  rw [show star (-z : ℝ) = (-z) by simp]
  rw [neg_smul, neg_neg]

lemma dl3Ksharp_integral_zero (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x : ℝ, K x = 0) : ∫ z : ℝ, dl3Ksharp K z = 0 := by
  have hmp : MeasureTheory.MeasurePreserving (fun z : ℝ => -z)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_neg _
  have h1 : (∫ z : ℝ, dl3Ksharp K z) = ∫ z : ℝ, star (K z) := by
    refine hmp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding (fun z : ℝ => star (K z))
  rw [h1, ← dl3_star_integral, hK0, star_zero]

lemma dl3Ksharp_fourier (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K) (ξ : ℝ) :
    FourierTransform.fourier (dl3Ksharp K) ξ = star (FourierTransform.fourier K ξ) := by
  rw [dl3_fourier_eq_mul (dl3Ksharp K) ξ, dl3_fourier_eq_mul K ξ]
  simp only [dl3Ksharp]
  have hmp : MeasureTheory.MeasurePreserving (fun z : ℝ => -z)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_neg _
  have hstep : (∫ x : ℝ, (Real.fourierChar (-(x * ξ)) : ℂ) * star (K (-x)))
      = ∫ u : ℝ, (Real.fourierChar (u * ξ) : ℂ) * star (K u) := by
    rw [show (fun x : ℝ => (Real.fourierChar (-(x * ξ)) : ℂ) * star (K (-x)))
        = (fun x : ℝ => (Real.fourierChar ((-x) * ξ) : ℂ) * star (K (-x))) from by
      funext x; rw [show (-x) * ξ = -(x * ξ) by ring]]
    exact hmp.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
      (fun u : ℝ => (Real.fourierChar (u * ξ) : ℂ) * star (K u))
  rw [hstep, dl3_star_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [star_mul, ← dl3_fourierChar_conj (u * ξ), star_star]
  ring

end

/-! ## Part 9: the `L^3` bound and the main theorem -/

instance : ENNReal.HolderTriple (ENNReal.ofReal (3/2 : ℝ)) (ENNReal.ofReal 3) 1 := by
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3/2),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3),
      ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ (3/2)⁻¹) (by norm_num : (0:ℝ) ≤ 3⁻¹),
      show (3/2:ℝ)⁻¹ + 3⁻¹ = 1 by norm_num, ENNReal.ofReal_one, inv_one]

lemma dl3_memLp_inv_one_add_sq :
    MemLp (fun y : ℝ => (1 + y^2)⁻¹) (ENNReal.ofReal (3/2)) (volume : Measure ℝ) := by
  have hg_int : Integrable (fun y : ℝ => (1 + y^2)⁻¹) volume := integrable_inv_one_add_sq
  have hg_nn : ∀ y : ℝ, 0 ≤ (1 + y^2)⁻¹ := fun y => by positivity
  have hg_le1 : ∀ y : ℝ, (1 + y^2)⁻¹ ≤ 1 := fun y => by
    rw [inv_le_one₀ (by positivity : (0:ℝ) < 1 + y^2)]
    linarith [sq_nonneg y]
  have hmeas : AEStronglyMeasurable (fun y : ℝ => (1 + y^2)⁻¹) volume :=
    (measurable_inv.comp (by fun_prop)).aestronglyMeasurable
  · rw [memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by simp : (ENNReal.ofReal (3/2) : ℝ≥0∞) ≠ 0)
        (by simp : (ENNReal.ofReal (3/2) : ℝ≥0∞) ≠ ∞) hmeas,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/2)]
    have hpt : ∀ y : ℝ, ‖(1 + y^2)⁻¹‖ₑ ^ (3/2 : ℝ) ≤ ENNReal.ofReal ((1 + y^2)⁻¹) := by
      intro y
      rw [Real.enorm_eq_ofReal (hg_nn y),
        ENNReal.ofReal_rpow_of_nonneg (hg_nn y) (by norm_num)]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_self_of_le_one (hg_nn y) (hg_le1 y) (by norm_num))
    calc ∫⁻ y, ‖(1 + y^2)⁻¹‖ₑ ^ (3/2 : ℝ)
        ≤ ∫⁻ y, ENNReal.ofReal ((1 + y^2)⁻¹) := MeasureTheory.lintegral_mono hpt
      _ = ENNReal.ofReal (∫ y, (1 + y^2)⁻¹) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int
            (Filter.Eventually.of_forall hg_nn)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top

lemma dl3_memLp_K_l32 (K : ℝ → ℂ) (hK : Integrable K) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2) :
    MemLp K (ENNReal.ofReal (3/2)) (volume : Measure ℝ) := by
  have hg : MemLp (fun u : ℝ => A * (1 + u^2)⁻¹) (ENNReal.ofReal (3/2)) volume :=
    dl3_memLp_inv_one_add_sq.const_mul A
  refine MemLp.of_le hg hK.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => ?_))
  have hAu : 0 ≤ A * (1 + u^2)⁻¹ := by positivity
  calc ‖K u‖ ≤ A / (1 + |u|)^2 := hKb u
    _ = A * (1 + |u|)^(-2:ℤ) := by rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
    _ ≤ A * (1 + u^2)⁻¹ := mul_le_mul_of_nonneg_left (dl3_one_add_abs_sq_inv_le u) hA
    _ = ‖A * (1 + u^2)⁻¹‖ := by rw [Real.norm_of_nonneg hAu]

lemma dl3_memLp_comp_mul_left {g : ℝ → ℂ} (hg : MemLp g (ENNReal.ofReal (3/2)) volume)
    {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun z : ℝ => g (a * z)) (ENNReal.ofReal (3/2)) (volume : Measure ℝ) := by
  have hmap : MemLp g (ENNReal.ofReal (3/2)) (Measure.map (fun x : ℝ => a * x) volume) := by
    rw [Real.map_volume_mul_left ha]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact MemLp.comp_of_map hmap (measurable_const_mul a).aemeasurable

lemma dl3_memLp_dl3Phi (K : ℝ → ℂ) (hK : Integrable K) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2) (l : ℤ) :
    MemLp (dl3Phi K l) (ENNReal.ofReal (3/2)) (volume : Measure ℝ) := by
  have hc : (0:ℝ) < (2:ℝ)^l := zpow_pos (by norm_num) l
  have hKl : MemLp (fun z : ℝ => K ((2:ℝ)^l * z)) (ENNReal.ofReal (3/2)) volume :=
    dl3_memLp_comp_mul_left (dl3_memLp_K_l32 K hK A hA hKb) hc.ne'
  have h2 := hKl.const_mul (((2:ℝ)^l : ℂ))
  exact h2

lemma dl3_memLp_dl3Phi_shift (K : ℝ → ℂ) (hK : Integrable K) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2) (l : ℤ) (x : ℝ) :
    MemLp (fun y : ℝ => dl3Phi K l (x - y)) (ENNReal.ofReal (3/2)) (volume : Measure ℝ) :=
  (dl3_memLp_dl3Phi K hK A hA hKb l).comp_measurePreserving
    (Measure.measurePreserving_sub_left volume x)

lemma dl3Op_eq_sum (K : ℝ → ℂ) (hK : Integrable K)
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2)
    (F : Finset ℤ) (e : ℤ → ℂ) (f : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal 3) (volume : Measure ℝ)) (x : ℝ) :
    dl3Op K F e f x
      = ∑ l ∈ F, e l * ∫ y : ℝ, f y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l)) := by
  obtain ⟨A, hA, hKb'⟩ := hKb
  rw [dl3Op]
  rw [show (fun y : ℝ => f y * dl3Kappa K F e (x - y))
      = (fun y : ℝ => ∑ l ∈ F, f y * (e l * dl3Phi K l (x - y))) from by
    funext y
    rw [dl3Kappa, Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l hl
    have hInt : Integrable (fun y : ℝ => f y * dl3Phi K l (x - y)) := by
      have hmul : MemLp (fun y : ℝ => dl3Phi K l (x - y) * f y) 1 volume :=
        MemLp.mul' (dl3_memLp_dl3Phi_shift K hK A hA.le hKb' l x) hf
      exact (memLp_one_iff_integrable.mp hmul).congr
        (Filter.Eventually.of_forall (fun y => mul_comm _ _))
    have hstep : (∫ y : ℝ, f y * (e l * dl3Phi K l (x - y)))
        = e l * ∫ y : ℝ, f y * dl3Phi K l (x - y) := by
      rw [show (fun y : ℝ => f y * (e l * dl3Phi K l (x - y)))
          = (fun y : ℝ => e l * (f y * dl3Phi K l (x - y))) from by funext y; ring]
      exact MeasureTheory.integral_const_mul (e l) (fun y : ℝ => f y * dl3Phi K l (x - y))
    rw [hstep]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    unfold dl3Phi
    ring
  · intro l hl
    have hmul : MemLp (fun y : ℝ => dl3Phi K l (x - y) * f y) 1 volume :=
      MemLp.mul' (dl3_memLp_dl3Phi_shift K hK A hA.le hKb' l x) hf
    have hInt : Integrable (fun y : ℝ => f y * dl3Phi K l (x - y)) :=
      (memLp_one_iff_integrable.mp hmul).congr
        (Filter.Eventually.of_forall (fun y => mul_comm _ _))
    refine (hInt.const_mul (e l)).congr (Filter.Eventually.of_forall (fun y => ?_))
    ring

lemma dl3_star_phi (K : ℝ → ℂ) (l : ℤ) (t : ℝ) :
    star (dl3Phi K l (-t)) = dl3Phi (dl3Ksharp K) l t := by
  unfold dl3Phi dl3Ksharp
  rw [star_mul]
  rw [show star (((2:ℝ)^l : ℂ)) = (((2:ℝ)^l : ℂ)) by
    rw [← Complex.ofReal_zpow]; exact Complex.conj_ofReal _]
  rw [show (2:ℝ)^l * (-t) = -((2:ℝ)^l * t) by ring]
  ring

lemma dl3_star_kappa (K : ℝ → ℂ) (F : Finset ℤ) (e : ℤ → ℂ) (t : ℝ) :
    star (dl3Kappa K F e (-t))
      = dl3Kappa (dl3Ksharp K) F (fun l => star (e l)) t := by
  simp only [dl3Kappa]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [star_mul, dl3_star_phi K l t, mul_comm]

lemma dl3_adjoint_pairing (K : ℝ → ℂ) (hK : Integrable K)
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2)
    (F : Finset ℤ) (e : ℤ → ℂ) (he : ∀ l, ‖e l‖ ≤ 1) (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, star (dl3Op K F e f x) * g x)
      = ∫ x : ℝ, star (f x) * dl3Op (dl3Ksharp K) F (fun l => star (e l)) g x := by
  have hKb0 := hKb
  have hKlip0 := hKlip
  obtain ⟨A, hA, hKb'⟩ := hKb
  obtain ⟨B, hB, hKlip'⟩ := hKlip
  have hKcont : Continuous K := dl3_lipschitz_continuous K ⟨B, hB, hKlip'⟩
  have hκbdd : ∀ z : ℝ, ‖dl3Kappa K F e z‖ ≤ ∑ l ∈ F, A * (2:ℝ)^l :=
    dl3Kappa_bound K A hA.le (fun z => by
      calc ‖K z‖ ≤ A / (1 + |z|)^2 := hKb' z
        _ ≤ A := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + |z|)^2)]
            have hge : (1:ℝ) ≤ (1 + |z|)^2 := by nlinarith [abs_nonneg z, sq_nonneg (1 + |z|)]
            nlinarith [hA, hge]) F e he
  have hκmeas : Measurable (dl3Kappa K F e) := by
    show Measurable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (e l)
    change Measurable (fun z : ℝ => (2:ℝ)^l * K ((2:ℝ)^l * z))
    exact (hKcont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  have hmain := Commons.Analysis.Convolution.integral_inner_convolution_eq_adjoint_meas
    (dl3Kappa K F e) (∑ l ∈ F, A * (2:ℝ)^l) hκbdd hκmeas f g hf hg
  have hL : (∫ x : ℝ, inner ℂ (∫ y : ℝ, dl3Kappa K F e (x - y) • f y) (g x))
      = ∫ x : ℝ, star (dl3Op K F e f x) * g x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hx : (∫ y : ℝ, dl3Kappa K F e (x - y) • f y) = dl3Op K F e f x := by
      unfold dl3Op
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [smul_eq_mul, mul_comm]
    rw [hx, RCLike.inner_apply, mul_comm, starRingEnd_apply]
  have hR : (∫ x : ℝ, inner ℂ (f x)
        (∫ y : ℝ, (starRingEnd ℂ) (dl3Kappa K F e (y - x)) • g y))
      = ∫ x : ℝ, star (f x) * dl3Op (dl3Ksharp K) F (fun l => star (e l)) g x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hx : (∫ y : ℝ, (starRingEnd ℂ) (dl3Kappa K F e (y - x)) • g y)
        = dl3Op (dl3Ksharp K) F (fun l => star (e l)) g x := by
      unfold dl3Op
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      have hk : star (dl3Kappa K F e (y - x))
          = dl3Kappa (dl3Ksharp K) F (fun l => star (e l)) (x - y) := by
        rw [show y - x = -(x - y) by ring]
        exact dl3_star_kappa K F e (x - y)
      rw [starRingEnd_apply, smul_eq_mul, hk]
      exact mul_comm _ _
    rw [hx, RCLike.inner_apply, mul_comm, starRingEnd_apply]
  rw [← hL, ← hR]
  exact hmain

set_option maxHeartbeats 1000000 in
lemma dl3Op_aesm (K : ℝ → ℂ) (F : Finset ℤ) (e : ℤ → ℂ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) (hκ : Measurable (dl3Kappa K F e)) :
    AEStronglyMeasurable (dl3Op K F e f) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f p.2 * dl3Kappa K F e (p.1 - p.2)) (volume.prod volume) :=
    (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      ((hκ.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
  have h2 := hjoint.integral_prod_right'
  exact h2

lemma dl3_rpow_sq_half (a : ℝ) (ha : 0 ≤ a) : (a^2) ^ (3/2 : ℝ) = a^3 := by
  have h2 : (a^2 : ℝ) = a ^ (((2:ℕ):ℝ)) := (Real.rpow_natCast a 2).symm
  rw [h2, ← Real.rpow_mul ha (((2:ℕ):ℝ)) ((3:ℝ)/2)]
  rw [show ((2:ℕ):ℝ) * ((3:ℝ)/2) = ((3:ℕ):ℝ) by norm_num]
  exact Real.rpow_natCast a 3

lemma dl3_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

lemma dl3_star_mul_self (a : ℂ) :
    star a * (((‖a‖ : ℝ) : ℂ) * a) = (((‖a‖^3 : ℝ)) : ℂ) := by
  have h1 : star a * a = ((Complex.normSq a : ℝ) : ℂ) := by
    rw [mul_comm, ← starRingEnd_apply a, Complex.mul_conj]
  calc star a * (((‖a‖ : ℝ) : ℂ) * a)
      = ((‖a‖ : ℝ) : ℂ) * (star a * a) := by ring
    _ = ((‖a‖ : ℝ) : ℂ) * ((Complex.normSq a : ℝ) : ℂ) := by rw [h1]
    _ = (((‖a‖ : ℝ) * Complex.normSq a : ℝ) : ℂ) := by rw [Complex.ofReal_mul]
    _ = (((‖a‖^3 : ℝ)) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
        congr 1
        ring

lemma dl3_memLp_kappa (K : ℝ → ℂ) (hK : Integrable K) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2) (F : Finset ℤ) (e : ℤ → ℂ) :
    MemLp (dl3Kappa K F e) (ENNReal.ofReal (3/2)) (volume : Measure ℝ) := by
  have hsum := Finset.sum_induction (s := F) (f := fun l z => e l * dl3Phi K l z)
    (p := fun u => MemLp u (ENNReal.ofReal (3/2)) volume)
    (fun a b ha hb => ha.add hb) MemLp.zero
    (fun l _ => (dl3_memLp_dl3Phi K hK A hA hKb l).const_mul (e l))
  have heq : (∑ x ∈ F, fun z => e x * dl3Phi K x z) = dl3Kappa K F e := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rwa [heq] at hsum

set_option maxHeartbeats 2000000 in
theorem dl3_l3_bound (K : ℝ → ℂ)
    (Cp : ℝ) (hCp : 0 < Cp)
    (hκmeas : ∀ (F : Finset ℤ) (e : ℤ → ℂ), Measurable (dl3Kappa K F e))
    (hbdd : ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (f : ℝ → ℂ), Integrable f →
      eLpNorm (dl3Op K F e f) (ENNReal.ofReal 3) volume
        ≤ ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal 3) volume)
    (hκ : ∀ (F : Finset ℤ) (e : ℤ → ℂ),
      MemLp (dl3Kappa K F e) (ENNReal.ofReal (3/2)) volume) :
    ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (f : ℝ → ℂ),
      MemLp f (ENNReal.ofReal 3) (volume : Measure ℝ) →
      eLpNorm (dl3Op K F e f) (ENNReal.ofReal 3) volume
        ≤ ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal 3) volume := by
  intro F e he f hf
  by_cases htop : eLpNorm f (ENNReal.ofReal 3) volume = ⊤
  · rw [htop, ENNReal.mul_top (by positivity : (ENNReal.ofReal Cp : ℝ≥0∞) ≠ 0)]
    exact le_top
  let f' : ℝ → ℂ := hf.aestronglyMeasurable.mk f
  have hf'_meas : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf'_ae : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  let c : ℕ → ℝ := fun n => (n:ℝ) + 1
  let ftr : ℕ → ℝ → ℂ := fun n x => if ‖f' x‖ ≤ c n ∧ |x| ≤ c n then f' x else 0
  have hS : ∀ n, MeasurableSet {x : ℝ | ‖f' x‖ ≤ c n ∧ |x| ≤ c n} := fun n =>
    (measurableSet_le hf'_meas.norm measurable_const).inter
      (measurableSet_le measurable_abs measurable_const)
  have hcn : ∀ n, 0 ≤ c n := by intro n; simp only [c]; positivity
  have hftr_meas : ∀ n, Measurable (ftr n) := by
    intro n
    simp only [ftr]
    exact Measurable.ite (hS n) hf'_meas measurable_const
  have hftr_int : ∀ n, Integrable (ftr n) := by
    intro n
    have hvol : (volume : Measure ℝ) {x : ℝ | |x| ≤ c n} ≠ ⊤ := by
      rw [dl3_volume_abs_le]; exact ENNReal.ofReal_ne_top
    have hms : MeasurableSet {x : ℝ | |x| ≤ c n} :=
      measurableSet_le measurable_abs measurable_const
    have h1 : Integrable (fun x : ℝ => if |x| ≤ c n then c n else 0) volume := by
      rw [show (fun x : ℝ => if |x| ≤ c n then c n else 0)
          = Set.indicator {x : ℝ | |x| ≤ c n} (fun _ => c n) from rfl]
      exact (MeasureTheory.integrableOn_const (s := {x : ℝ | |x| ≤ c n}) (C := c n)
        (hs := hvol)).integrable_indicator hms
    refine Integrable.mono' h1 ((hftr_meas n).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ftr]
    by_cases hcon : ‖f' x‖ ≤ c n ∧ |x| ≤ c n
    · rw [if_pos hcon, if_pos hcon.2]
      exact hcon.1
    · rw [if_neg hcon]
      by_cases hR : |x| ≤ c n
      · rw [if_pos hR]; simpa using hcn n
      · rw [if_neg hR]; simp
  have hftr_lp : ∀ n, eLpNorm (ftr n) (ENNReal.ofReal 3) volume
      ≤ eLpNorm f (ENNReal.ofReal 3) volume := by
    intro n
    refine eLpNorm_mono_ae (hftr_meas n).aestronglyMeasurable ?_
    filter_upwards [hf'_ae] with x hx
    simp only [ftr]
    by_cases hcon : ‖f' x‖ ≤ c n ∧ |x| ≤ c n
    · rw [if_pos hcon, ← hx]
    · rw [if_neg hcon]; simp
  have hconv : ∀ x : ℝ, Tendsto (fun n => dl3Op K F e (ftr n) x) atTop (𝓝 (dl3Op K F e f x)) := by
    intro x
    have hκsh : MemLp (fun y : ℝ => dl3Kappa K F e (x - y)) (ENNReal.ofReal (3/2)) volume :=
      (hκ F e).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    have hprod : MemLp (fun y : ℝ => dl3Kappa K F e (x - y) * f y) 1 volume := MemLp.mul' hκsh hf
    have hInt : Integrable (fun y : ℝ => f y * dl3Kappa K F e (x - y)) :=
      (memLp_one_iff_integrable.mp hprod).congr
        (Filter.Eventually.of_forall (fun y => mul_comm _ _))
    have hbound_int : Integrable (fun y : ℝ => ‖f y * dl3Kappa K F e (x - y)‖) volume := hInt.norm
    have hlim : ∀ᵐ y : ℝ ∂volume, Tendsto (fun n => ftr n y * dl3Kappa K F e (x - y)) atTop
        (𝓝 (f y * dl3Kappa K F e (x - y))) := by
      filter_upwards [hf'_ae] with y hy
      have hfy : Tendsto (fun n : ℕ => ftr n y) atTop (𝓝 (f y)) := by
        refine Tendsto.congr' ?_ tendsto_const_nhds
        have h1 : ∀ᶠ n : ℕ in atTop, ‖f' y‖ ≤ c n ∧ |y| ≤ c n := by
          obtain ⟨n1, hn1⟩ := exists_nat_gt ‖f' y‖
          obtain ⟨n2, hn2⟩ := exists_nat_gt |y|
          refine Filter.eventually_atTop.mpr ⟨max n1 n2, fun n hn => ?_⟩
          have hc1 : ‖f' y‖ ≤ c n := by
            simp only [c]
            have : (n1:ℝ) ≤ (n:ℕ) := by
              exact_mod_cast le_trans (le_max_left n1 n2) hn
            linarith
          have hc2 : |y| ≤ c n := by
            simp only [c]
            have : (n2:ℝ) ≤ (n:ℕ) := by
              exact_mod_cast le_trans (le_max_right n1 n2) hn
            linarith
          exact ⟨hc1, hc2⟩
        filter_upwards [h1] with n hn
        simp only [ftr]; rw [if_pos hn]; exact hy
      exact hfy.mul_const _
    have hb : ∀ n : ℕ, ∀ᵐ y : ℝ ∂volume,
        ‖ftr n y * dl3Kappa K F e (x - y)‖ ≤ ‖f y * dl3Kappa K F e (x - y)‖ := by
      intro n
      filter_upwards [hf'_ae] with y hy
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simp only [ftr]
      by_cases hcon : ‖f' y‖ ≤ c n ∧ |y| ≤ c n
      · rw [if_pos hcon, ← hy]
      · rw [if_neg hcon]; simp
    have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun y : ℝ => ‖f y * dl3Kappa K F e (x - y)‖)
      (fun n => ((hftr_meas n).mul
        ((hκmeas F e).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
      hbound_int hb hlim
    unfold dl3Op
    exact hmain
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (u := atTop) (p := ENNReal.ofReal 3)
    (f := fun n : ℕ => dl3Op K F e (ftr n))
    (C := ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal 3) volume) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => le_trans (hbdd F e he (ftr n) (hftr_int n))
      (mul_le_mul_of_nonneg_left (hftr_lp n) (by positivity)))
  · intro n
    exact dl3Op_aesm K F e (ftr n) (hftr_meas n).aestronglyMeasurable (hκmeas F e)
  · exact dl3Op_aesm K F e f hf.aestronglyMeasurable (hκmeas F e)
  · exact Filter.Eventually.of_forall hconv

end Commons.Analysis.Fourier
