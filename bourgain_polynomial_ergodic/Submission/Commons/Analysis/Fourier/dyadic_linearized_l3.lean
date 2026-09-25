import Mathlib
import Submission.Commons.Analysis.Fourier.multiplier_eq_convolution_ae
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.separated_real_line_bandpass_maximal_l2
import Submission.Commons.Analysis.CalderonZygmund.cz_weak_type_one_lintegral
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
import Submission.Commons.Analysis.Convolution.integral_inner_convolution_eq_adjoint_meas

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

/-- The Fourier transform of a single dilated term. -/
lemma dl3_fourier_single (K : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun z : ℝ => (c : ℂ) * K (c * z)) ξ = 𝓕 K (ξ / c) :=
  fourier_dilation hc ξ

/-- Fourier transform of a dilated term. -/
lemma dl3Phi_fourier (K : ℝ → ℂ) (l : ℤ) (ξ : ℝ) :
    𝓕 (dl3Phi K l) ξ = 𝓕 K ((2:ℝ)^(-l) * ξ) := by
  rw [show dl3Phi K l = (fun z : ℝ => Complex.ofReal ((2:ℝ)^l) * K ((2:ℝ)^l * z)) from by
    funext z
    simp only [dl3Phi]
    rw [← Complex.ofReal_zpow]]
  rw [dl3_fourier_single K (zpow_pos (by norm_num) l) ξ]
  congr 1
  rw [div_eq_mul_inv, ← zpow_neg, mul_comm]

/-- **Fourier transform of the linearized kernel.** -/
lemma dl3_fourier_kappa (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (F : Finset ℤ) (e : ℤ → ℂ) (ξ : ℝ) :
    𝓕 (dl3Kappa K F e) ξ = ∑ l ∈ F, e l * 𝓕 K ((2:ℝ)^(-l) * ξ) := by
  classical
  have h2l : ∀ l : ℤ, (0:ℝ) < (2:ℝ)^l := fun l => zpow_pos (by norm_num) l
  rw [dl3_fourier_eq_mul (dl3Kappa K F e) ξ]
  rw [show (fun z : ℝ => (Real.fourierChar (-(z * ξ)) : ℂ) * (dl3Kappa K F e z))
      = (fun z : ℝ => ∑ l ∈ F, e l *
          ((Real.fourierChar (-(z * ξ)) : ℂ) * dl3Phi K l z)) from by
    funext z
    simp only [dl3Kappa]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l _
    rw [integral_const_mul]
    congr 1
    rw [← dl3_fourier_eq_mul (dl3Phi K l) ξ, dl3Phi_fourier K l ξ]
  · intro l _
    refine ((dl3Phi_integrable K hK l).bdd_mul (c := 1)
      (f := fun z : ℝ => (Real.fourierChar (-(z * ξ)) : ℂ))
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall (fun z => ?_))).const_mul (e l)
    rw [Circle.norm_coe]

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

/-- **The linearized operator is bounded on `L²`**, uniformly in the finite scale set `F` and the
coefficients `e_l`, `‖e_l‖ ≤ 1`. -/
theorem dl3_l2_bound (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x : ℝ, K x = 0) (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x))
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ, ‖𝓕 K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ A2 : ℝ, 0 < A2 ∧ ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (f : ℝ → ℂ),
      MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.eLpNorm (dl3Op K F e f) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C, N, hC, hN, hdec'⟩ := hdec
  obtain ⟨A, hApos, hAsym⟩ := dl3_symbol_bound K hK hK0 hKx C N hC hN hdec'
  refine ⟨A, hApos, fun F e he f hf => ?_⟩
  set κ : ℝ → ℂ := dl3Kappa K F e with hκ
  have hκint : MeasureTheory.Integrable κ := by rw [hκ]; exact dl3Kappa_integrable K hK F e
  have hsym : ∀ ξ : ℝ, 𝓕 κ ξ = ∑ l ∈ F, e l * 𝓕 K ((2:ℝ)^(-l) * ξ) := fun ξ => by
    rw [hκ]; exact dl3_fourier_kappa K hK F e ξ
  have hmA : ∀ ξ : ℝ, ‖𝓕 κ ξ‖ ≤ A := fun ξ => by rw [hsym ξ]; exact hAsym F e he ξ
  have hm : MeasureTheory.MemLp (fun ξ : ℝ => 𝓕 κ ξ) ⊤ MeasureTheory.volume :=
    memLp_top_of_bound (dl3_continuous_fourier κ hκint).aestronglyMeasurable A
      (Filter.Eventually.of_forall hmA)
  -- the convolution form is a.e. the multiplier operator
  have hbridge : (fun x : ℝ => ∫ y : ℝ, f y * κ (x - y))
      =ᵐ[MeasureTheory.volume]
        (fun x : ℝ => (BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f) :
          ℝ → ℂ) x) := by
    have h1 : (fun x : ℝ => ∫ y : ℝ, (hf.toLp f : ℝ → ℂ) y * κ (x - y))
        = (fun x : ℝ => ∫ y : ℝ, f y * κ (x - y)) := by
      funext x
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with y hy
      rw [hy]
    have h2 := multiplier_eq_convolution_ae κ hκint hm (hf.toLp f)
    rw [h1] at h2
    exact h2
  -- ENNReal bound for the multiplier
  have hbound : ‖BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f)‖ₑ
      ≤ ENNReal.ofReal A * ‖hf.toLp f‖ₑ := by
    have hsq : ‖BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f)‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal (A ^ (2:ℝ)) * ‖hf.toLp f‖ₑ ^ (2:ℝ) := by
      rw [BoundaryLayer.enorm_multiplier_sq]
      have hpt : ∀ ξ : ℝ, ‖𝓕 κ ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A ^ (2:ℝ)) := by
        intro ξ
        rw [BoundaryLayer.enorm_eq_ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (norm_nonneg _) (hmA ξ) (by norm_num))
      calc ∫⁻ ξ, ‖𝓕 κ ξ‖ₑ ^ (2:ℝ) * ‖(𝓕 (hf.toLp f)) ξ‖ₑ ^ (2:ℝ)
          ≤ ∫⁻ ξ, ENNReal.ofReal (A ^ (2:ℝ)) * ‖(𝓕 (hf.toLp f)) ξ‖ₑ ^ (2:ℝ) := by
            apply MeasureTheory.lintegral_mono
            intro ξ
            exact mul_le_mul' (hpt ξ) le_rfl
        _ = ENNReal.ofReal (A ^ (2:ℝ)) * ∫⁻ ξ, ‖(𝓕 (hf.toLp f)) ξ‖ₑ ^ (2:ℝ) :=
            MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (A ^ (2:ℝ)) * ‖hf.toLp f‖ₑ ^ (2:ℝ) := by
            rw [← BoundaryLayer.lp_enorm_sq_eq_lintegral (𝓕 (hf.toLp f)),
              BoundaryLayer.enorm_fourier]
    have hA2 : (A ^ (2:ℝ)) ^ (1/2:ℝ) = A := by
      rw [← Real.rpow_mul hApos.le]; norm_num
    calc ‖BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f)‖ₑ
        = (‖BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f)‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ (ENNReal.ofReal (A ^ (2:ℝ)) * ‖hf.toLp f‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) :=
          ENNReal.rpow_le_rpow hsq (by norm_num)
      _ = ENNReal.ofReal A * ‖hf.toLp f‖ₑ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
            ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ A ^ (2:ℝ))
              (by norm_num : (0:ℝ) ≤ 1/2),
            hA2, ← ENNReal.rpow_mul]
          norm_num
  have hOp : dl3Op K F e f = (fun x : ℝ => ∫ y : ℝ, f y * κ (x - y)) := by
    rw [hκ]; rfl
  rw [hOp, MeasureTheory.eLpNorm_congr_ae hbridge]
  calc MeasureTheory.eLpNorm (fun x : ℝ =>
        (BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f) : ℝ → ℂ) x) 2
        MeasureTheory.volume
      = ‖BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 κ ξ) hm (hf.toLp f)‖ₑ :=
        (MeasureTheory.Lp.enorm_def _).symm
    _ ≤ ENNReal.ofReal A * ‖hf.toLp f‖ₑ := hbound
    _ = ENNReal.ofReal A * MeasureTheory.eLpNorm f 2 MeasureTheory.volume := by
        rw [MeasureTheory.Lp.enorm_def]
        congr 1
        exact MeasureTheory.eLpNorm_congr_ae hf.coeFn_toLp


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

/-- Tail bound for a translate of `K`: for `R ≥ 2` and `|c| ≤ R/2`,
`∫⁻_{|u|>R} ‖K(u-c)‖ ≤ 8A/R`. -/
lemma dl3_tail_shift (K : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (c R : ℝ) (hR : 2 ≤ R) (hc : |c| ≤ R/2) :
    ∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K (u - c)‖ₑ ≤ ENNReal.ofReal (8 * A / R) := by
  have hRpos : 0 < R := by linarith
  have hpt : ∀ u : ℝ, R < |u| →
      ‖K (u - c)‖ₑ ≤ ENNReal.ofReal (4 * A) * ENNReal.ofReal ((u^2)⁻¹) := by
    intro u hu
    have h1 : |u| / 2 ≤ |u - c| := by
      have h2 := abs_sub_abs_le_abs_sub u c
      nlinarith [abs_nonneg u, abs_nonneg c, hu, hc]
    have h3 : ‖K (u - c)‖ ≤ A / (1 + |u - c|) ^ 2 := hKb _
    have h4 : (1 + |u - c|) ^ 2 ≥ (|u| / 2) ^ 2 := by
      nlinarith [h1, abs_nonneg u, abs_nonneg (u - c)]
    have h5 : A / (1 + |u - c|) ^ 2 ≤ 4 * A * (u^2)⁻¹ := by
      have h6 : (0:ℝ) < (|u|/2)^2 := by nlinarith [abs_nonneg u, hu]
      have h7 : A / (1 + |u - c|)^2 ≤ A / (|u|/2)^2 :=
        div_le_div_of_nonneg_left hA (by positivity) h4
      have h8 : A / (|u|/2)^2 = 4 * A * (u^2)⁻¹ := by
        rw [div_pow, sq_abs]; field_simp; ring
      linarith [h7, le_of_eq h8]
    rw [BoundaryLayer.enorm_eq_ofReal_norm, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*A)]
    exact ENNReal.ofReal_le_ofReal (le_trans h3 h5)
  rw [← MeasureTheory.lintegral_indicator
    (show MeasurableSet {u : ℝ | R < |u|} from measurableSet_lt measurable_const measurable_abs)]
  calc ∫⁻ u : ℝ, ({u : ℝ | R < |u|}.indicator (fun u => ‖K (u - c)‖ₑ)) u
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (4 * A) *
          ({u : ℝ | R < |u|}.indicator (fun u => ENNReal.ofReal ((u^2)⁻¹))) u := by
        apply MeasureTheory.lintegral_mono
        intro u
        simp only
        by_cases h : R < |u|
        · rw [Set.indicator_of_mem (s := {u : ℝ | R < |u|}) h,
            Set.indicator_of_mem (s := {u : ℝ | R < |u|}) h]
          exact hpt u h
        · rw [Set.indicator_of_notMem (s := {u : ℝ | R < |u|}) h,
            Set.indicator_of_notMem (s := {u : ℝ | R < |u|}) h, mul_zero]
    _ = ENNReal.ofReal (4 * A) * ∫⁻ u : ℝ,
          ({u : ℝ | R < |u|}.indicator (fun u => ENNReal.ofReal ((u^2)⁻¹))) u := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (4 * A) * ENNReal.ofReal (2/R) := by
        rw [MeasureTheory.lintegral_indicator
          (show MeasurableSet {u : ℝ | R < |u|} from
            measurableSet_lt measurable_const measurable_abs),
          dl3_lintegral_abs_tail_inv_sq R hRpos]
    _ = ENNReal.ofReal (8 * A / R) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*A)]
        congr 1
        field_simp
        ring

/-- Full-line bound for a translate of `K` with the elementary bound `4A`. -/
lemma dl3_full_tail (K : ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2) (c : ℝ) :
    ∫⁻ u : ℝ, ‖K (u - c)‖ₑ ≤ ENNReal.ofReal (4 * A) := by
  have hpt : ∀ u : ℝ, ‖K (u - c)‖ₑ ≤ ENNReal.ofReal A * ENNReal.ofReal ((1 + (u - c)^2)⁻¹) := by
    intro u
    rw [BoundaryLayer.enorm_eq_ofReal_norm, ← ENNReal.ofReal_mul hA]
    apply ENNReal.ofReal_le_ofReal
    calc ‖K (u - c)‖ ≤ A / (1 + |u - c|) ^ 2 := hKb _
      _ ≤ A * (1 + (u - c) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left
            (by
              apply inv_anti₀ (by positivity)
              nlinarith [abs_nonneg (u - c), sq_abs (u - c)]) hA
  calc ∫⁻ u : ℝ, ‖K (u - c)‖ₑ
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal A * ENNReal.ofReal ((1 + (u - c)^2)⁻¹) :=
        MeasureTheory.lintegral_mono hpt
    _ = ENNReal.ofReal A * ∫⁻ u : ℝ, ENNReal.ofReal ((1 + (u - c)^2)⁻¹) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal A * ∫⁻ v : ℝ, ENNReal.ofReal ((1 + v^2)⁻¹) := by
        congr 1
        have hmp : MeasureTheory.MeasurePreserving (fun u : ℝ => u - c)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
          MeasureTheory.measurePreserving_sub_right _ c
        exact hmp.lintegral_comp_emb (Homeomorph.subRight c).measurableEmbedding
          (fun v : ℝ => ENNReal.ofReal ((1 + v^2)⁻¹))
    _ = ENNReal.ofReal A * ENNReal.ofReal Real.pi := by
        congr 1
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (integrable_inv_one_add_sq) (Filter.Eventually.of_forall (fun x => by positivity))]
        rw [integral_univ_inv_one_add_sq]
    _ ≤ ENNReal.ofReal (4 * A) := by
        rw [← ENNReal.ofReal_mul hA]
        apply ENNReal.ofReal_le_ofReal
        nlinarith [Real.pi_lt_four, hA]


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

/-- The single-scale kernel-difference bound for `|w| ≤ 1`. -/
lemma dl3_single_scale_le_one (K : ℝ → ℂ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hKlip : ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ w : ℝ, |w| ≤ 1 →
      ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (C₁ * |w| ^ (1/2:ℝ)) := by
  have hKmeas : Measurable K := (dl3_lipschitz_continuous K ⟨B, hB, hKlip⟩).measurable
  refine ⟨2 * B + 32 * A + 4, by positivity, fun w hw => ?_⟩
  have hAnn : ∀ u : ℝ, ‖K (u - w) - K u‖ₑ ≤ ‖K (u - w)‖ₑ + ‖K u‖ₑ := by
    intro u
    simpa [sub_eq_add_neg] using enorm_add_le (K (u - w)) (-(K u))
  rcases eq_or_ne w 0 with rfl | hwne
  · simp only [abs_zero, mul_zero, sub_zero, sub_self, enorm_zero]
    simp
  have hwpos : 0 < |w| := abs_pos.mpr hwne
  by_cases hw4 : |w| ≤ 1/4
  · set R : ℝ := |w| ^ (-(1/2):ℝ) with hRdef
    have hRpos : 0 < R := by
      rw [hRdef]; exact Real.rpow_pos_of_pos hwpos _
    have hR2 : 2 ≤ R := by
      rw [hRdef, Real.rpow_neg (abs_nonneg w)]
      have h2 : |w| ^ (1/2:ℝ) ≤ (1/2:ℝ) := by
        have := Real.rpow_le_rpow (abs_nonneg w) hw4 (by norm_num : (0:ℝ) ≤ 1/2)
        rwa [dl3_quarter_rpow] at this
      have h3 : (0:ℝ) < |w| ^ (1/2:ℝ) := Real.rpow_pos_of_pos hwpos _
      rw [inv_eq_one_div, le_div_iff₀ h3]
      linarith
    have hpart1 : ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ (∫⁻ u : ℝ in {u : ℝ | |u| ≤ R}, ‖K (u - w) - K u‖ₑ)
          + (∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K (u - w) - K u‖ₑ) := by
      refine le_trans (MeasureTheory.lintegral_mono_set ?_) (MeasureTheory.lintegral_union_le _ _ _)
      intro u hu
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hu ⊢
      by_cases h : |u| ≤ R
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge h)
    have hboundA : ∫⁻ u : ℝ in {u : ℝ | |u| ≤ R}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (B * |w| * (2 * R)) := by
      have h1 : ∫⁻ u : ℝ in {u : ℝ | |u| ≤ R}, ‖K (u - w) - K u‖ₑ
          ≤ ∫⁻ u : ℝ in {u : ℝ | |u| ≤ R}, ENNReal.ofReal (B * |w|) := by
        apply MeasureTheory.lintegral_mono
        intro u
        simp only []
        rw [BoundaryLayer.enorm_eq_ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by simpa using hKlip (u - w) u)
      rw [MeasureTheory.setLIntegral_const] at h1
      refine le_trans h1 (le_of_eq ?_)
      rw [dl3_volume_abs_le R]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ B * |w|)]
    have hboundB : ∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (16 * A / R) := by
      have hsm : MeasurableSet {u : ℝ | R < |u|} := measurableSet_lt measurable_const measurable_abs
      have hf1 : Measurable (fun u : ℝ => ‖K (u - w)‖ₑ) :=
        (hKmeas.comp (measurable_id.sub_const w)).enorm
      calc ∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K (u - w) - K u‖ₑ
          ≤ ∫⁻ u : ℝ in {u : ℝ | R < |u|}, (‖K (u - w)‖ₑ + ‖K u‖ₑ) := by
            apply MeasureTheory.lintegral_mono
            intro u
            simp only []
            exact hAnn u
        _ = (∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K (u - w)‖ₑ)
            + (∫⁻ u : ℝ in {u : ℝ | R < |u|}, ‖K u‖ₑ) :=
            dl3_setLIntegral_add _ _ _ hsm hf1
        _ ≤ ENNReal.ofReal (8 * A / R) + ENNReal.ofReal (8 * A / R) := by
            refine add_le_add ?_ ?_
            · refine dl3_tail_shift K A hA.le hKb w R hR2 ?_
              have ht : |w| ^ (1/2:ℝ) ≤ 1/2 := by
                have := Real.rpow_le_rpow (abs_nonneg w) hw4 (by norm_num : (0:ℝ) ≤ 1/2)
                rwa [dl3_quarter_rpow] at this
              have htpos : 0 < |w| ^ (1/2:ℝ) := Real.rpow_pos_of_pos hwpos _
              have hsq : (|w| ^ (1/2:ℝ))^2 = |w| := by
                rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num]
                exact Real.rpow_inv_natCast_pow (abs_nonneg w) (by norm_num : (2:ℕ) ≠ 0)
              rw [hRdef, Real.rpow_neg (abs_nonneg w),
                show ((|w| ^ (1/2:ℝ))⁻¹ / 2) = 1 / (2 * |w| ^ (1/2:ℝ)) by
                  rw [inv_eq_one_div]; field_simp]
              rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * |w| ^ (1/2:ℝ))]
              nlinarith [ht, htpos, hsq, sq_nonneg (|w| ^ (1/2:ℝ))]

            · have hc0 : |(0:ℝ)| ≤ R / 2 := by rw [abs_zero]; linarith [hR2]
              simpa using dl3_tail_shift K A hA.le hKb 0 R hR2 hc0
        _ = ENNReal.ofReal (16 * A / R) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    have hfin : ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (B * |w| * (2 * R)) + ENNReal.ofReal (16 * A / R) :=
      le_trans hpart1 (add_le_add hboundA hboundB)
    have hsqw : (|w| ^ (1/2:ℝ))^2 = |w| := by
      rw [show (1/2:ℝ) = ((2:ℝ))⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow (abs_nonneg w) (by norm_num : (2:ℕ) ≠ 0)
    have htw : (0:ℝ) < |w| ^ (1/2:ℝ) := Real.rpow_pos_of_pos hwpos _
    have hRw : R * |w| = |w| ^ (1/2:ℝ) := by
      rw [hRdef, Real.rpow_neg (abs_nonneg w), inv_mul_eq_div, div_eq_iff htw.ne']
      rw [← sq, hsqw]
    have hRinv : R⁻¹ = |w| ^ (1/2:ℝ) := by
      rw [hRdef, Real.rpow_neg (abs_nonneg w), inv_inv]
    refine le_trans hfin ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [show 16 * A / R = 16 * A * |w| ^ (1/2:ℝ) by rw [div_eq_mul_inv, hRinv],
      show B * |w| * (2 * R) = 2 * B * |w| ^ (1/2:ℝ) by rw [← hRw]; ring]
    nlinarith [Real.rpow_nonneg (abs_nonneg w) (1/2:ℝ), hA, hB]
  · -- middle case
    push Not at hw4
    have hfull : ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (8 * A) := by
      have hsm : MeasurableSet {u : ℝ | 2 * |w| < |u|} :=
        measurableSet_lt measurable_const measurable_abs
      have hf1 : Measurable (fun u : ℝ => ‖K (u - w)‖ₑ) :=
        (hKmeas.comp (measurable_id.sub_const w)).enorm
      calc ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
          ≤ ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, (‖K (u - w)‖ₑ + ‖K u‖ₑ) := by
            apply MeasureTheory.lintegral_mono
            intro u
            simp only []
            exact hAnn u
        _ = (∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w)‖ₑ)
            + (∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K u‖ₑ) :=
            dl3_setLIntegral_add _ _ _ hsm hf1
        _ ≤ ENNReal.ofReal (4 * A) + ENNReal.ofReal (4 * A) := by
            refine add_le_add ?_ ?_
            · calc ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w)‖ₑ
                  ≤ ∫⁻ u : ℝ, ‖K (u - w)‖ₑ := by
                    rw [← MeasureTheory.lintegral_indicator hsm]
                    refine MeasureTheory.lintegral_mono (fun u => ?_)
                    by_cases h : u ∈ {u : ℝ | 2 * |w| < |u|}
                    · rw [Set.indicator_of_mem h]
                    · rw [Set.indicator_of_notMem h]; positivity
                _ ≤ ENNReal.ofReal (4 * A) := dl3_full_tail K A hA.le hKb w
            · calc ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K u‖ₑ
                  ≤ ∫⁻ u : ℝ, ‖K u‖ₑ := by
                    rw [← MeasureTheory.lintegral_indicator hsm]
                    refine MeasureTheory.lintegral_mono (fun u => ?_)
                    by_cases h : u ∈ {u : ℝ | 2 * |w| < |u|}
                    · rw [Set.indicator_of_mem h]
                    · rw [Set.indicator_of_notMem h]; positivity
                _ ≤ ENNReal.ofReal (4 * A) := by simpa using dl3_full_tail K A hA.le hKb 0
        _ = ENNReal.ofReal (8 * A) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    refine le_trans hfull ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1/2:ℝ) ≤ |w| ^ (1/2:ℝ) := by
      calc (1/2:ℝ) = (1/4:ℝ)^(1/2:ℝ) := by rw [dl3_quarter_rpow]
        _ ≤ |w| ^ (1/2:ℝ) := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1/4) hw4.le
            (by norm_num : (0:ℝ) ≤ 1/2)
    nlinarith [h1, Real.rpow_nonneg (abs_nonneg w) (1/2:ℝ)]

/-- The single-scale kernel-difference bound for `|w| ≥ 1`. -/
lemma dl3_single_scale_ge_one (K : ℝ → ℂ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hKlip : ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|) :
    ∀ w : ℝ, 1 ≤ |w| →
      ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
        ≤ ENNReal.ofReal (8 * A / |w|) := by
  have hKmeas : Measurable K := (dl3_lipschitz_continuous K ⟨B, hB, hKlip⟩).measurable
  intro w hw
  have hwpos : 0 < |w| := by linarith
  have hAnn : ∀ u : ℝ, ‖K (u - w) - K u‖ₑ ≤ ‖K (u - w)‖ₑ + ‖K u‖ₑ := by
    intro u
    simpa [sub_eq_add_neg] using enorm_add_le (K (u - w)) (-(K u))
  have hsm : MeasurableSet {u : ℝ | 2 * |w| < |u|} := measurableSet_lt measurable_const measurable_abs
  have hf1 : Measurable (fun u : ℝ => ‖K (u - w)‖ₑ) :=
    (hKmeas.comp (measurable_id.sub_const w)).enorm
  have hR2 : 2 ≤ 2 * |w| := by linarith
  calc ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w) - K u‖ₑ
      ≤ ∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, (‖K (u - w)‖ₑ + ‖K u‖ₑ) := by
        apply MeasureTheory.lintegral_mono
        intro u
        simp only []
        exact hAnn u
    _ = (∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K (u - w)‖ₑ)
        + (∫⁻ u : ℝ in {u : ℝ | 2 * |w| < |u|}, ‖K u‖ₑ) :=
        dl3_setLIntegral_add _ _ _ hsm hf1
    _ ≤ ENNReal.ofReal (8 * A / (2 * |w|)) + ENNReal.ofReal (8 * A / (2 * |w|)) := by
        have hc1 : |w| ≤ (2 * |w|) / 2 := by
          rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
        have hc0 : |(0:ℝ)| ≤ (2 * |w|) / 2 := by
          rw [abs_zero]; positivity
        exact add_le_add (dl3_tail_shift K A hA.le hKb w (2 * |w|) hR2 hc1)
          (by simpa using dl3_tail_shift K A hA.le hKb 0 (2 * |w|) hR2 hc0)
    _ = ENNReal.ofReal (8 * A / |w|) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring


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



/-- **The lacunary sum of the kernel-difference integrals.** -/
theorem dl3_kernel_diff_tsum (K : ℝ → ℂ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hKb : ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hKlip : ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ℤ) (y : ℝ),
      (∑ l ∈ F, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
        ‖K (u - (2:ℝ)^l * y) - K u‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := dl3_single_scale_le_one K A B hA hB hKb hKlip
  have hge := dl3_single_scale_ge_one K A B hA hB hKb hKlip
  refine ⟨4 * C₁ + 16 * A + 1, by positivity, fun F y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · have hzero : ∀ l : ℤ, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * (0:ℝ)| < |u|},
        ‖K (u - (2:ℝ)^l * 0) - K u‖ₑ = 0 := by
      intro l
      have : (fun u : ℝ => ‖K (u - (2:ℝ)^l * 0) - K u‖ₑ) = fun _ => 0 := by
        funext u; simp
      rw [this]
      exact MeasureTheory.lintegral_zero
    rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const, smul_zero]
    positivity
  · have hypos : 0 < |y| := abs_pos.mpr hy
    obtain ⟨m, hm1, hm2⟩ := dl3_exists_scale |y| hypos
    -- hm1 : |y| * 2^m ≤ 1, hm2 : 1 < |y| * 2^(m+1)
    set Flo := F.filter (fun l => l ≤ m) with hFlo
    set Fhi := F.filter (fun l => ¬ (l ≤ m)) with hFhi
    have h2pos : ∀ l : ℤ, (0:ℝ) < (2:ℝ)^l := fun l => zpow_pos (by norm_num) l
    have hy2l : ∀ l : ℤ, |(2:ℝ)^l * y| = (2:ℝ)^l * |y| := by
      intro l
      rw [abs_mul, abs_of_pos (h2pos l)]
    -- lower part
    have hlo : ∑ l ∈ Flo, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
        ‖K (u - (2:ℝ)^l * y) - K u‖ₑ ≤ ENNReal.ofReal (4 * C₁) := by
      have hstep : ∀ l ∈ Flo, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
          ‖K (u - (2:ℝ)^l * y) - K u‖ₑ
            ≤ ENNReal.ofReal (C₁ * |(2:ℝ)^l * y| ^ (1/2:ℝ)) := by
        intro l hl
        have hl' : l ≤ m := (Finset.mem_filter.mp hl).2
        have hw1 : |(2:ℝ)^l * y| ≤ 1 := by
          rw [hy2l l]
          calc (2:ℝ)^l * |y| ≤ (2:ℝ)^m * |y| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg y)
                exact zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl'
            _ = |y| * (2:ℝ)^m := by ring
            _ ≤ 1 := hm1
        exact hC₁ ((2:ℝ)^l * y) hw1
      calc ∑ l ∈ Flo, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
            ‖K (u - (2:ℝ)^l * y) - K u‖ₑ
          ≤ ∑ l ∈ Flo, ENNReal.ofReal (C₁ * |(2:ℝ)^l * y| ^ (1/2:ℝ)) :=
            Finset.sum_le_sum hstep
        _ = ∑ l ∈ Flo, ENNReal.ofReal (C₁ * (|y| * (2:ℝ)^l) ^ (1/2:ℝ)) := by
            apply Finset.sum_congr rfl
            intro l _
            have h1 : |(2:ℝ)^l * y| = |y| * (2:ℝ)^l := by rw [hy2l l, mul_comm]
            rw [h1]
        _ = ENNReal.ofReal (∑ l ∈ Flo, C₁ * (|y| * (2:ℝ)^l) ^ (1/2:ℝ)) :=
            (ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)).symm
        _ = ENNReal.ofReal (C₁ * ∑ l ∈ Flo, (|y| * (2:ℝ)^l) ^ (1/2:ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal (C₁ * 4) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_left
              (dl3_lacunary_low_sum |y| (abs_nonneg y) m Flo hm1
                (fun l hl => (Finset.mem_filter.mp hl).2)) hC₁pos.le
        _ = ENNReal.ofReal (4 * C₁) := by rw [mul_comm]
    -- upper part
    have hhi : ∑ l ∈ Fhi, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
        ‖K (u - (2:ℝ)^l * y) - K u‖ₑ ≤ ENNReal.ofReal (16 * A) := by
      have hstep : ∀ l ∈ Fhi, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
          ‖K (u - (2:ℝ)^l * y) - K u‖ₑ ≤ ENNReal.ofReal (8 * A / ((2:ℝ)^l * |y|)) := by
        intro l hl
        have hl' : ¬ (l ≤ m) := (Finset.mem_filter.mp hl).2
        have hml : m < l := by omega
        have hw1 : 1 ≤ |(2:ℝ)^l * y| := by
          rw [hy2l l]
          calc (1:ℝ) ≤ (2:ℝ)^(m+1) * |y| := le_of_lt (by rw [mul_comm]; exact hm2)
            _ ≤ (2:ℝ)^l * |y| := mul_le_mul_of_nonneg_right
                (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)) (abs_nonneg y)
        have hw := hge ((2:ℝ)^l * y) hw1
        rw [show 8 * A / |(2:ℝ)^l * y| = 8 * A / ((2:ℝ)^l * |y|) by rw [hy2l l]] at hw
        exact hw
      have hsum : ∑ l ∈ Fhi, 8 * A / ((2:ℝ)^l * |y|) ≤ 16 * A := by
        have hconst : ∀ l : ℤ, 8 * A / ((2:ℝ)^l * |y|) = (8 * A / |y|) * (2:ℝ)^(-l) := by
          intro l
          rw [zpow_neg]
          field_simp
        calc ∑ l ∈ Fhi, 8 * A / ((2:ℝ)^l * |y|)
            = ∑ l ∈ Fhi, (8 * A / |y|) * (2:ℝ)^(-l) :=
              Finset.sum_congr rfl (fun l _ => hconst l)
          _ ≤ (8 * A / |y|) * (2:ℝ)^(-m) :=
              dl3_lacunary_high_sum (8 * A / |y|) (by positivity) m Fhi (fun l hl => by
                have := (Finset.mem_filter.mp hl).2
                push Not at this
                exact this)
          _ ≤ 16 * A := by
              have h2m : (1:ℝ)/2 < (2:ℝ)^m * |y| := by
                have h := hm2
                rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)] at h
                nlinarith [h, hypos, h2pos m]
              rw [zpow_neg]
              rw [show (8 * A / |y|) * ((2:ℝ)^m)⁻¹ = 8 * A / ((2:ℝ)^m * |y|) by
                rw [inv_eq_one_div]; field_simp]
              rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^m * |y|)]
              nlinarith [h2m, hA]
      calc ∑ l ∈ Fhi, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
            ‖K (u - (2:ℝ)^l * y) - K u‖ₑ
          ≤ ∑ l ∈ Fhi, ENNReal.ofReal (8 * A / ((2:ℝ)^l * |y|)) := Finset.sum_le_sum hstep
        _ = ENNReal.ofReal (∑ l ∈ Fhi, 8 * A / ((2:ℝ)^l * |y|)) :=
            (ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity)).symm
        _ ≤ ENNReal.ofReal (16 * A) := ENNReal.ofReal_le_ofReal hsum
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun l => l ≤ m)
      (fun l : ℤ => ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
        ‖K (u - (2:ℝ)^l * y) - K u‖ₑ)
    rw [← hsplit]
    refine le_trans (add_le_add hlo hhi) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith


/-- The `enorm` of `2^l` as a complex number. -/
lemma dl3_enorm_two_zpow (l : ℤ) : ‖(((2:ℝ)^l : ℂ))‖ₑ = ENNReal.ofReal ((2:ℝ)^l) := by
  rw [BoundaryLayer.enorm_eq_ofReal_norm, norm_zpow]
  have h : ‖(Complex.ofReal 2 : ℂ)‖ = (2:ℝ) := by norm_num
  rw [h]

/-- **Weak `(1,1)` bound for the linearized operator.** -/
theorem dl3_weak_type (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x : ℝ, K x = 0) (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x))
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | lam < ‖dl3Op K F e f x‖}
        ≤ ENNReal.ofReal (A0 / lam) * MeasureTheory.eLpNorm f 1
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨A, hA, hKb'⟩ := hKb
  obtain ⟨B, hB, hKlip'⟩ := hKlip
  obtain ⟨A2, hA2, hL2⟩ := dl3_l2_bound K hK hK0 hKx hdec
  obtain ⟨Ck, hCk, hker⟩ := dl3_kernel_diff_tsum K A B hA hB hKb' hKlip'
  have hKcont : Continuous K := dl3_lipschitz_continuous K ⟨B, hB, hKlip'⟩
  refine ⟨24 * A2 ^ 2 + 4 * Ck + 100, by positivity, fun F e he f hf lam hlam => ?_⟩
  have hbdd : ∀ z : ℝ, ‖dl3Kappa K F e z‖ ≤ ∑ l ∈ F, A * (2:ℝ)^l :=
    dl3Kappa_bound K A hA.le (fun z => by
      calc ‖K z‖ ≤ A / (1 + |z|) ^ 2 := hKb' z
        _ ≤ A := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + |z|) ^ 2)]
            have hge : (1:ℝ) ≤ (1 + |z|) ^ 2 := by nlinarith [abs_nonneg z, sq_nonneg (1 + |z|)]
            nlinarith [hA, hge]) F e he
  have hmeas : Measurable (dl3Kappa K F e) := by
    show Measurable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (e l)
    change Measurable (fun z : ℝ => (2:ℝ)^l * K ((2:ℝ)^l * z))
    exact (hKcont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  have hstrong : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ, dl3Kappa K F e (x - y) • g y) 2
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm g 2 := by
    intro g hg
    by_cases hg2 : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)
    · have h1 := hL2 F e he g hg2
      refine le_trans (le_of_eq (eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_)))) h1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [smul_eq_mul, mul_comm]
    · have htop : MeasureTheory.eLpNorm g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) = ⊤ := by
        by_contra h
        exact hg2 (lt_top_iff_ne_top.mpr h)
      rw [htop, ENNReal.mul_top (by positivity)]
      exact le_top
  have hker' : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∫⁻ x : ℝ in {x : ℝ | 50 * L ≤ |x|},
        ‖dl3Kappa K F e (x - y) - dl3Kappa K F e x‖ₑ ≤ ENNReal.ofReal Ck := by
    intro L hL y hy
    have hset : MeasurableSet {x : ℝ | 50 * L ≤ |x|} :=
      measurableSet_le measurable_const measurable_abs
    -- pointwise triangle inequality
    have hpoint : ∀ x : ℝ, ‖dl3Kappa K F e (x - y) - dl3Kappa K F e x‖ₑ
        ≤ ∑ l ∈ F, ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ := by
      intro x
      have h1 : dl3Kappa K F e (x - y) - dl3Kappa K F e x
          = ∑ l ∈ F, (e l * dl3Phi K l (x - y) - e l * dl3Phi K l x) := by
        rw [dl3Kappa, dl3Kappa, ← Finset.sum_sub_distrib]
      rw [h1]
      refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum (fun l _ => ?_))
      rw [← mul_sub]
      calc ‖e l * (dl3Phi K l (x - y) - dl3Phi K l x)‖ₑ
          = ‖e l‖ₑ * ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ := enorm_mul _ _
        _ ≤ 1 * ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ := by
            apply mul_le_mul' _ le_rfl
            rw [show (1:ℝ≥0∞) = ‖(1:ℂ)‖ₑ by simp, enorm_le_iff_norm_le]
            simpa using he l
        _ = _ := one_mul _
    have hmeas2 : ∀ l ∈ F, Measurable (fun x : ℝ => ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ) := by
      intro l _
      refine Measurable.enorm ?_
      refine Measurable.sub ?_ ?_
      · refine Measurable.const_mul ?_ _
        exact hKcont.measurable.comp ((measurable_id.sub_const y).const_mul _)
      · refine Measurable.const_mul ?_ _
        exact hKcont.measurable.comp (measurable_id.const_mul _)
    have hscale : ∀ l : ℤ, ∫⁻ x : ℝ in {x : ℝ | 50 * L ≤ |x|},
        ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ
          = ∫⁻ u : ℝ in {u : ℝ | 50 * L * (2:ℝ)^l ≤ |u|},
            ‖K (u - (2:ℝ)^l * y) - K u‖ₑ := by
      intro l
      have h2l : (0:ℝ) < (2:ℝ)^l := zpow_pos (by norm_num) l
      have hpt : ∀ x : ℝ, ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ
          = ENNReal.ofReal ((2:ℝ)^l) * ‖K ((2:ℝ)^l * (x - y)) - K ((2:ℝ)^l * x)‖ₑ := by
        intro x
        rw [dl3Phi, dl3Phi, ← mul_sub, enorm_mul, dl3_enorm_two_zpow]
      rw [MeasureTheory.lintegral_congr hpt,
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [show (fun a : ℝ => ‖K ((2:ℝ)^l * (a - y)) - K ((2:ℝ)^l * a)‖ₑ)
          = (fun a : ℝ => ‖K ((2:ℝ)^l * a - (2:ℝ)^l * y) - K ((2:ℝ)^l * a)‖ₑ) from by
        funext a; rw [mul_sub]]
      rw [dl3_setLIntegral_comp_mul_left ((2:ℝ)^l) (50 * L) h2l
        (fun u : ℝ => ‖K (u - (2:ℝ)^l * y) - K u‖ₑ) (by
          refine Measurable.enorm ?_
          refine Measurable.sub ?_ ?_
          · exact hKcont.measurable.comp (measurable_id.sub_const _)
          · exact hKcont.measurable)]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^l),
        mul_inv_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < (2:ℝ)^l)), ENNReal.ofReal_one, one_mul]
    calc ∫⁻ x : ℝ in {x : ℝ | 50 * L ≤ |x|},
          ‖dl3Kappa K F e (x - y) - dl3Kappa K F e x‖ₑ
        ≤ ∫⁻ x : ℝ in {x : ℝ | 50 * L ≤ |x|},
            ∑ l ∈ F, ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ :=
          MeasureTheory.lintegral_mono hpoint
      _ = ∑ l ∈ F, ∫⁻ x : ℝ in {x : ℝ | 50 * L ≤ |x|},
            ‖dl3Phi K l (x - y) - dl3Phi K l x‖ₑ :=
          MeasureTheory.lintegral_finsetSum F hmeas2
      _ = ∑ l ∈ F, ∫⁻ u : ℝ in {u : ℝ | 50 * L * (2:ℝ)^l ≤ |u|},
            ‖K (u - (2:ℝ)^l * y) - K u‖ₑ := Finset.sum_congr rfl (fun l _ => hscale l)
      _ ≤ ∑ l ∈ F, ∫⁻ u : ℝ in {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|},
            ‖K (u - (2:ℝ)^l * y) - K u‖ₑ := by
          apply Finset.sum_le_sum
          intro l _
          have h2l : (0:ℝ) < (2:ℝ)^l := zpow_pos (by norm_num) l
          have hsub : {u : ℝ | 50 * L * (2:ℝ)^l ≤ |u|} ⊆ {u : ℝ | 2 * |(2:ℝ)^l * y| < |u|} := by
            intro u hu
            simp only [Set.mem_ofPred_eq] at hu ⊢
            rw [abs_mul, abs_of_pos h2l]
            have h1 : 2 * |y| ≤ L := by linarith
            have h2 : 2 * ((2:ℝ)^l * |y|) < 50 * L * (2:ℝ)^l := by nlinarith [h1, h2l, hL]
            linarith
          exact MeasureTheory.lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal Ck := hker F y
  have hmain := CalderonZygmund.cz_weak_type_one_measurable_bounded (dl3Kappa K F e)
    A2 Ck (∑ l ∈ F, A * (2:ℝ)^l) hA2 hCk.le hbdd hmeas hker' hstrong f hf lam hlam
  have hOp : dl3Op K F e f = (fun x : ℝ => ∫ y : ℝ, dl3Kappa K F e (x - y) • f y) := by
    funext x
    rw [dl3Op]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul, mul_comm]
  rw [hOp]
  refine le_trans hmain (le_of_eq ?_)
  rw [div_eq_mul_inv]


/-- The boundedness of the linearized operator on `L^p`, `1 < p < 2` (Calder\'on--Zygmund +
Marcinkiewicz), uniformly in `F` and `e`. -/
theorem dl3_lt_two_bound (K : ℝ → ℂ) (hK : MeasureTheory.Integrable K)
    (hK0 : ∫ x : ℝ, K x = 0) (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x))
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier K ξ‖ ≤ C * (1 + |ξ|) ^ (-N))
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f →
      MeasureTheory.eLpNorm (dl3Op K F e f) (ENNReal.ofReal p)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal Cp * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨A, hA, hKb'⟩ := hKb
  obtain ⟨B, hB, hKlip'⟩ := hKlip
  obtain ⟨A2, hA2, hL2⟩ := dl3_l2_bound K hK hK0 hKx hdec
  obtain ⟨A0, hA0, hweak⟩ := dl3_weak_type K hK hK0 hKx ⟨B, hB, hKlip'⟩ ⟨A, hA, hKb'⟩ hdec
  have hKcont : Continuous K := dl3_lipschitz_continuous K ⟨B, hB, hKlip'⟩
  have hCp : (0:ℝ) < 12 * A0 * (2:ℝ) ^ (p - 1) / (p - 1) + 16 * A2 ^ 2 / (2 - p) := by
    have h1 : (0:ℝ) < 12 * A0 * (2:ℝ) ^ (p - 1) / (p - 1) :=
      div_pos (by positivity) (by linarith)
    have h2 : (0:ℝ) < 16 * A2 ^ 2 / (2 - p) :=
      div_pos (by positivity) (by linarith)
    linarith
  refine ⟨(12 * A0 * (2:ℝ) ^ (p - 1) / (p - 1) + 16 * A2 ^ 2 / (2 - p)) ^ (1 / p),
    Real.rpow_pos_of_pos hCp _, fun F e he f hf => ?_⟩
  have hbdd : ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) →
      ∀ z : ℝ, ‖dl3Kappa K F e z‖ ≤ ∑ l ∈ F, A * (2:ℝ)^l :=
    fun F e he z => dl3Kappa_bound K A hA.le (fun z => by
      calc ‖K z‖ ≤ A / (1 + |z|) ^ 2 := hKb' z
        _ ≤ A := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + |z|) ^ 2)]
            have hge : (1:ℝ) ≤ (1 + |z|) ^ 2 := by
              nlinarith [abs_nonneg z, sq_nonneg (1 + |z|)]
            nlinarith [hA, hge]) F e he z
  have hmeas : Measurable (dl3Kappa K F e) := by
    show Measurable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (e l)
    change Measurable (fun z : ℝ => (2:ℝ)^l * K ((2:ℝ)^l * z))
    exact (hKcont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  have hadd : ∀ g h : ℝ → ℂ, MeasureTheory.Integrable g → MeasureTheory.Integrable h →
      dl3Op K F e (g + h) = dl3Op K F e g + dl3Op K F e h := by
    intro g h hg hh
    funext x
    have h1 : MeasureTheory.Integrable
        (fun y : ℝ => g y * dl3Kappa K F e (x - y)) :=
      hg.mul_bdd (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => hbdd F e he (x - y)))
    have h2 : MeasureTheory.Integrable
        (fun y : ℝ => h y * dl3Kappa K F e (x - y)) :=
      hh.mul_bdd (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => hbdd F e he (x - y)))
    simp only [dl3Op, Pi.add_apply]
    rw [show (∫ y : ℝ, (g y + h y) * dl3Kappa K F e (x - y))
        = ∫ y : ℝ, (g y * dl3Kappa K F e (x - y) + h y * dl3Kappa K F e (x - y)) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring]
    rw [MeasureTheory.integral_add h1 h2]
  exact Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
    (dl3Op K F e) hadd hA0 hA2 (fun g lam hg hlam => hweak F e he g hg lam hlam)
    (fun g hg => by
      by_cases hg2 : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      · exact hL2 F e he g hg2
      · have htop : MeasureTheory.eLpNorm g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) = ⊤ := by
          by_contra h
          exact hg2 (lt_top_iff_ne_top.mpr h)
        rw [htop, ENNReal.mul_top (by positivity)]
        exact le_top) hp1 hp2 f hf


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

lemma dl3_holder_pair (f w : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) (hw : AEStronglyMeasurable w volume) :
    ‖∫ x : ℝ, star (f x) * w x‖ₑ
      ≤ eLpNorm f (ENNReal.ofReal 3) volume * eLpNorm w (ENNReal.ofReal (3/2)) volume := by
  calc ‖∫ x : ℝ, star (f x) * w x‖ₑ
      ≤ ∫⁻ x : ℝ, ‖star (f x) * w x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ * ‖w x‖ₑ := by
        apply MeasureTheory.lintegral_congr
        intro x
        rw [enorm_mul, BoundaryLayer.enorm_eq_ofReal_norm, BoundaryLayer.enorm_eq_ofReal_norm,
          BoundaryLayer.enorm_eq_ofReal_norm, norm_star]
    _ ≤ (∫⁻ x : ℝ, ‖f x‖ₑ ^ (3:ℝ)) ^ (1/3:ℝ) *
          (∫⁻ x : ℝ, ‖w x‖ₑ ^ ((3/2):ℝ)) ^ (1/(3/2):ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume
          (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
          hf.enorm hw.enorm
    _ = eLpNorm f (ENNReal.ofReal 3) volume * eLpNorm w (ENNReal.ofReal (3/2)) volume := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal 3) (by simp) (by simp) hf,
            eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal (3/2)) (by simp) (by simp)
              hw,
            ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3),
            ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/2)]

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

set_option maxHeartbeats 2000000 in
theorem dl3_l3_bound_of_adjoint (K : ℝ → ℂ) (hK : Integrable K)
    (hKlip : ∃ B : ℝ, 0 < B ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ B * |u - v|)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|)^2)
    (Cp : ℝ) (hCp : 0 < Cp)
    (hadj : ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (g : ℝ → ℂ), Integrable g →
      eLpNorm (dl3Op (dl3Ksharp K) F (fun l => star (e l)) g) (ENNReal.ofReal (3/2)) volume
        ≤ ENNReal.ofReal Cp * eLpNorm g (ENNReal.ofReal (3/2)) volume) :
    ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (f : ℝ → ℂ), Integrable f →
      eLpNorm (dl3Op K F e f) (ENNReal.ofReal 3) volume
        ≤ ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal 3) volume := by
  intro F e he f hf
  by_cases htop : eLpNorm f (ENNReal.ofReal 3) volume = ⊤
  · rw [htop, ENNReal.mul_top (by positivity : (ENNReal.ofReal Cp : ℝ≥0∞) ≠ 0)]
    exact le_top
  have hKb0 := hKb
  have hKlip0 := hKlip
  obtain ⟨A, hA, hKb'⟩ := hKb
  obtain ⟨B, hB, hKlip'⟩ := hKlip
  have hKcont : Continuous K := dl3_lipschitz_continuous K ⟨B, hB, hKlip'⟩
  have hKscont : Continuous (dl3Ksharp K) :=
    dl3_lipschitz_continuous _ ⟨B, hB, dl3Ksharp_lipschitz K B hKlip'⟩
  have hκmeas : Measurable (dl3Kappa K F e) := by
    show Measurable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (e l)
    change Measurable (fun z : ℝ => (2:ℝ)^l * K ((2:ℝ)^l * z))
    exact (hKcont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  have hκsmeas : Measurable (dl3Kappa (dl3Ksharp K) F (fun l => star (e l))) := by
    show Measurable (fun z : ℝ => ∑ l ∈ F, star (e l) * dl3Phi (dl3Ksharp K) l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (star (e l))
    change Measurable (fun z : ℝ => (2:ℝ)^l * dl3Ksharp K ((2:ℝ)^l * z))
    exact (hKscont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  set h : ℝ → ℂ := dl3Op K F e f with hhdef
  have hh_aesm : AEStronglyMeasurable h volume := by
    rw [hhdef]; exact dl3Op_aesm K F e f hf.aestronglyMeasurable hκmeas
  have hh_meas : Measurable h := by
    have hf'_meas : Measurable (hf.aestronglyMeasurable.mk f) :=
      hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hf'_ae : f =ᵐ[volume] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
    have hjoint : StronglyMeasurable
        (Function.uncurry (fun x y : ℝ =>
          hf.aestronglyMeasurable.mk f y * dl3Kappa K F e (x - y))) :=
      ((hf'_meas.comp measurable_snd).mul
        (hκmeas.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
    have h1 : StronglyMeasurable
        (fun x : ℝ => ∫ y : ℝ, hf.aestronglyMeasurable.mk f y * dl3Kappa K F e (x - y)) :=
      hjoint.integral_prod_right
    have h2 : h = (fun x : ℝ => ∫ y : ℝ,
        hf.aestronglyMeasurable.mk f y * dl3Kappa K F e (x - y)) := by
      rw [hhdef]
      funext x
      unfold dl3Op
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hf'_ae] with y hy
      rw [hy]
    rw [h2]
    exact h1.measurable
  set F3 : ℝ := (eLpNorm f (ENNReal.ofReal 3) volume).toReal with hF3def
  have hF3nn : 0 ≤ F3 := by rw [hF3def]; exact ENNReal.toReal_nonneg
  have hF3eq : eLpNorm f (ENNReal.ofReal 3) volume = ENNReal.ofReal F3 := by
    rw [hF3def]; exact (ENNReal.ofReal_toReal htop).symm
  set D : ℝ := F3 * Cp with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  set c : ℕ → ℝ := fun m => (m:ℝ) + 1 with hcdef
  set R : ℕ → ℝ := fun m => (m:ℝ) + 1 with hRdef
  set S : ℕ → Set ℝ := fun m => {x : ℝ | ‖h x‖ ≤ c m ∧ |x| ≤ R m} with hSdef
  set g : ℕ → ℝ → ℂ := fun m x => if x ∈ S m then (((‖h x‖ : ℝ)) : ℂ) * h x else 0 with hgdef
  set u : ℕ → ℝ → ℝ := fun m x => if x ∈ S m then ‖h x‖^3 else 0 with hudef
  set Am : ℕ → ℝ := fun m => ∫ x : ℝ, u m x with hAmdef
  have hcpos : ∀ m, 0 < c m := fun m => by rw [hcdef]; positivity
  have hRpos : ∀ m, 0 < R m := fun m => by rw [hRdef]; positivity
  have hSmeas : ∀ m, MeasurableSet (S m) := by
    intro m
    rw [hSdef]
    exact (measurableSet_le hh_meas.norm measurable_const).inter
      (measurableSet_le measurable_abs measurable_const)
  have hg_meas : ∀ m, Measurable (g m) := by
    intro m
    simp only [hgdef]
    refine Measurable.ite (hSmeas m) ?_ measurable_const
    exact (Complex.continuous_ofReal.measurable.comp hh_meas.norm).mul hh_meas
  have hu_meas : ∀ m, Measurable (u m) := by
    intro m
    simp only [hudef]
    refine Measurable.ite (hSmeas m) ?_ measurable_const
    exact (hh_meas.norm.pow_const 3)
  have hD2_int : ∀ m, Integrable (fun x : ℝ => if |x| ≤ R m then (c m)^2 else 0) := by
    intro m
    have hvol : (volume : Measure ℝ) {x : ℝ | |x| ≤ R m} ≠ ⊤ := by
      rw [dl3_volume_abs_le]; exact ENNReal.ofReal_ne_top
    have hms : MeasurableSet {x : ℝ | |x| ≤ R m} :=
      measurableSet_le measurable_abs measurable_const
    have h1 : Integrable (Set.indicator {x : ℝ | |x| ≤ R m} (fun _ : ℝ => (c m)^2)) volume :=
      (MeasureTheory.integrableOn_const (s := {x : ℝ | |x| ≤ R m}) (C := (c m)^2)
        (hs := hvol)).integrable_indicator hms
    rw [show (fun x : ℝ => if |x| ≤ R m then (c m)^2 else 0)
        = Set.indicator {x : ℝ | |x| ≤ R m} (fun _ => (c m)^2) from rfl]
    exact h1
  have hD3_int : ∀ m, Integrable (fun x : ℝ => if |x| ≤ R m then (c m)^3 else 0) := by
    intro m
    have hvol : (volume : Measure ℝ) {x : ℝ | |x| ≤ R m} ≠ ⊤ := by
      rw [dl3_volume_abs_le]; exact ENNReal.ofReal_ne_top
    have hms : MeasurableSet {x : ℝ | |x| ≤ R m} :=
      measurableSet_le measurable_abs measurable_const
    have h1 : Integrable (Set.indicator {x : ℝ | |x| ≤ R m} (fun _ : ℝ => (c m)^3)) volume :=
      (MeasureTheory.integrableOn_const (s := {x : ℝ | |x| ≤ R m}) (C := (c m)^3)
        (hs := hvol)).integrable_indicator hms
    rw [show (fun x : ℝ => if |x| ≤ R m then (c m)^3 else 0)
        = Set.indicator {x : ℝ | |x| ≤ R m} (fun _ => (c m)^3) from rfl]
    exact h1
  have hg_int : ∀ m, Integrable (g m) := by
    intro m
    refine Integrable.mono' (hD2_int m) ((hg_meas m).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hgdef, hSdef, Set.mem_setOf_eq]
    by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
    · rw [if_pos hcon, if_pos hcon.2, norm_mul, dl3_norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      nlinarith [norm_nonneg (h x), hcon.1]
    · rw [if_neg hcon]
      by_cases hR : |x| ≤ R m
      · rw [if_pos hR]; simpa using pow_nonneg (hcpos m).le 2
      · rw [if_neg hR]; simp
  have hu_int : ∀ m, Integrable (u m) := by
    intro m
    refine Integrable.mono' (hD3_int m) ((hu_meas m).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hudef, hSdef, Set.mem_setOf_eq]
    by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
    · rw [if_pos hcon, if_pos hcon.2, Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hcon.1 3
    · rw [if_neg hcon]
      by_cases hR : |x| ≤ R m
      · rw [if_pos hR]; simpa using pow_nonneg (hcpos m).le 3
      · rw [if_neg hR]; simp
  have hAm_nn : ∀ m, 0 ≤ Am m := by
    intro m
    rw [hAmdef]
    refine MeasureTheory.integral_nonneg (fun x => ?_)
    simp only [hudef, hSdef, Set.mem_setOf_eq]
    split_ifs with hcon
    · positivity
    · exact le_refl 0
  have hpoint : ∀ m x, star (h x) * g m x = ((u m x : ℝ) : ℂ) := by
    intro m x
    simp only [hudef, hgdef, hSdef, Set.mem_setOf_eq]
    by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
    · rw [if_pos hcon, if_pos hcon, dl3_star_mul_self]
    · rw [if_neg hcon, if_neg hcon, mul_zero, Complex.ofReal_zero]
  have hInt_eq : ∀ m, (∫ x : ℝ, star (h x) * g m x) = ((Am m : ℝ) : ℂ) := by
    intro m
    rw [show (∫ x : ℝ, star (h x) * g m x) = ∫ x : ℝ, ((u m x : ℝ) : ℂ) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hpoint m))]
    rw [hAmdef]
    exact integral_ofReal
  have hEnorm : ∀ m, ‖∫ x : ℝ, star (h x) * g m x‖ₑ = ENNReal.ofReal (Am m) := by
    intro m
    rw [hInt_eq m, BoundaryLayer.enorm_eq_ofReal_norm, dl3_norm_ofReal,
      abs_of_nonneg (hAm_nn m)]
  have hkey : ∀ m, Am m ≤ D^3 := by
    intro m
    have hpair := dl3_adjoint_pairing K hK hKlip0 hKb0 F e he f (g m) hf (hg_int m)
    have hw_aesm : AEStronglyMeasurable
        (dl3Op (dl3Ksharp K) F (fun l => star (e l)) (g m)) volume :=
      dl3Op_aesm _ _ _ _ (hg_int m).aestronglyMeasurable hκsmeas
    have hHolder := dl3_holder_pair f _ hf.aestronglyMeasurable hw_aesm
    have hgm_lp : ∫⁻ x : ℝ, ‖g m x‖ₑ ^ (3/2 : ℝ) = ENNReal.ofReal (Am m) := by
      have hpt : ∀ x : ℝ, ‖g m x‖ₑ ^ (3/2 : ℝ) = ENNReal.ofReal (u m x) := by
        intro x
        simp only [hudef, hgdef, hSdef, Set.mem_setOf_eq]
        by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
        · rw [if_pos hcon, if_pos hcon]
          rw [BoundaryLayer.enorm_eq_ofReal_norm, norm_mul, dl3_norm_ofReal,
            abs_of_nonneg (norm_nonneg _)]
          rw [show ‖h x‖ * ‖h x‖ = ‖h x‖^2 by ring]
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            dl3_rpow_sq_half _ (norm_nonneg _)]
        · rw [if_neg hcon, if_neg hcon]
          simp
      rw [MeasureTheory.lintegral_congr hpt, hAmdef]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hu_int m)
        (Filter.Eventually.of_forall (fun x => by
          simp only [hudef, hSdef, Set.mem_setOf_eq]
          split_ifs with hcon
          · positivity
          · exact le_refl 0))).symm
    have hstep1 : ENNReal.ofReal (Am m)
        ≤ eLpNorm f (ENNReal.ofReal 3) volume *
          eLpNorm (dl3Op (dl3Ksharp K) F (fun l => star (e l)) (g m))
            (ENNReal.ofReal (3/2)) volume := by
      rw [← hEnorm m, hpair]
      exact hHolder
    have hstep2 : eLpNorm (dl3Op (dl3Ksharp K) F (fun l => star (e l)) (g m))
          (ENNReal.ofReal (3/2)) volume
        ≤ ENNReal.ofReal Cp * ENNReal.ofReal (Am m) ^ (2/3 : ℝ) := by
      refine (hadj F e he (g m) (hg_int m)).trans (le_of_eq ?_)
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal (3/2))
            (by simp) (by simp) (hg_meas m).aestronglyMeasurable,
          ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/2), hgm_lp]
      norm_num
    have hcomb : ENNReal.ofReal (Am m)
        ≤ ENNReal.ofReal F3 * (ENNReal.ofReal Cp * ENNReal.ofReal (Am m) ^ (2/3 : ℝ)) := by
      refine hstep1.trans ?_
      rw [hF3eq]
      exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
    have hcomb2 : ENNReal.ofReal (Am m)
        ≤ ENNReal.ofReal (D * (Am m) ^ (2/3 : ℝ)) := by
      refine hcomb.trans (le_of_eq ?_)
      rw [hDdef, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ F3 * Cp),
          ENNReal.ofReal_rpow_of_nonneg (hAm_nn m) (by norm_num : (0:ℝ) ≤ 2/3),
          ENNReal.ofReal_mul hF3nn]
      ring
    have hreal : Am m ≤ D * (Am m) ^ (2/3 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ) ≤ D * (Am m) ^ (2/3 : ℝ))).mp hcomb2
    set a : ℝ := (Am m) ^ ((3:ℝ)⁻¹) with hadef
    have ha_nn : 0 ≤ a := by rw [hadef]; exact Real.rpow_nonneg (hAm_nn m) _
    have ha3 : a^3 = Am m := by rw [hadef]; exact Real.rpow_inv_natCast_pow (hAm_nn m) (by norm_num)
    have ha2 : a^2 = (Am m) ^ (2/3 : ℝ) := by
      have h1 : a^2 = ((Am m) ^ ((3:ℝ)⁻¹)) ^ (((2:ℕ)) : ℝ) := by
        rw [hadef]; exact (Real.rpow_natCast _ 2).symm
      rw [h1, ← Real.rpow_mul (hAm_nn m) ((3:ℝ)⁻¹) (((2:ℕ)) : ℝ),
        show (3:ℝ)⁻¹ * (((2:ℕ)) : ℝ) = 2/3 by norm_num]
    have h4 : a^3 ≤ D * a^2 := by rw [ha3, ha2]; exact hreal
    have h5 : a ≤ D := by
      by_cases ha0 : a = 0
      · rw [ha0]; exact hDnn
      · have hapos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha0)
        by_contra hcon
        push_neg at hcon
        have hpos : 0 < a^2 * (a - D) := mul_pos (pow_pos hapos 2) (by linarith)
        have hzero : a^2 * (a - D) ≤ 0 := by nlinarith [h4]
        linarith
    calc Am m = a^3 := ha3.symm
      _ ≤ D^3 := pow_le_pow_left₀ ha_nn h5 3
  have hu_lintegral : ∀ m, ∫⁻ x : ℝ, ENNReal.ofReal (u m x) = ENNReal.ofReal (Am m) := by
    intro m
    rw [hAmdef]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hu_int m)
      (Filter.Eventually.of_forall (fun x => by
        simp only [hudef, hSdef, Set.mem_setOf_eq]
        split_ifs with hcon
        · positivity
        · exact le_refl 0))).symm
  have hU_meas : ∀ m, AEMeasurable (fun x : ℝ => ENNReal.ofReal (u m x)) volume :=
    fun m => (hu_meas m).ennreal_ofReal.aemeasurable
  have hU_mono : ∀ᵐ x : ℝ ∂volume, Monotone fun m => ENNReal.ofReal (u m x) := by
    filter_upwards with x
    refine monotone_nat_of_le_succ (fun m => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hudef, hSdef, Set.mem_setOf_eq]
    by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
    · have hc : c m ≤ c (m+1) := by
        simp only [hcdef, hRdef]; push_cast; linarith
      have hR : R m ≤ R (m+1) := by
        simp only [hRdef]; push_cast; linarith
      rw [if_pos hcon, if_pos ⟨le_trans hcon.1 hc, le_trans hcon.2 hR⟩]
    · rw [if_neg hcon]; positivity
  have hEnorm3 : ∀ x : ℝ, ENNReal.ofReal (‖h x‖^3) = ‖h x‖ₑ ^ (3:ℝ) := by
    intro x
    rw [BoundaryLayer.enorm_eq_ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (h x)) (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    exact (Real.rpow_natCast (‖h x‖) 3).symm
  have hsup : ∫⁻ x : ℝ, ‖h x‖ₑ ^ (3:ℝ) ≤ ENNReal.ofReal (D^3) := by
    have hpt : ∀ x : ℝ, (⨆ m : ℕ, ENNReal.ofReal (u m x)) = ‖h x‖ₑ ^ (3:ℝ) := by
      intro x
      refine le_antisymm (iSup_le (fun m => ?_)) ?_
      · rw [← hEnorm3 x]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hudef, hSdef, Set.mem_setOf_eq]
        by_cases hcon : ‖h x‖ ≤ c m ∧ |x| ≤ R m
        · rw [if_pos hcon]
        · rw [if_neg hcon]; positivity
      · rw [← hEnorm3 x]
        obtain ⟨n1, hn1⟩ := exists_nat_gt ‖h x‖
        obtain ⟨n2, hn2⟩ := exists_nat_gt |x|
        set m0 : ℕ := max n1 n2 with hm0
        have hm1 : ‖h x‖ ≤ c m0 := by
          simp only [hcdef, hRdef, hm0]
          have h2 : (n1 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_left n1 n2
          linarith
        have hm2 : |x| ≤ R m0 := by
          simp only [hRdef, hm0]
          have h2 : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
          linarith
        have hu0 : u m0 x = ‖h x‖^3 := by
          simp only [hudef, hSdef, Set.mem_setOf_eq]
          rw [if_pos ⟨hm1, hm2⟩]
        calc ENNReal.ofReal (‖h x‖^3) = ENNReal.ofReal (u m0 x) := by rw [hu0]
          _ ≤ ⨆ m, ENNReal.ofReal (u m x) :=
              le_iSup (fun m : ℕ => ENNReal.ofReal (u m x)) m0
    have h2 : ∫⁻ x : ℝ, ‖h x‖ₑ ^ (3:ℝ) = ⨆ m : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal (u m x) := by
      rw [← MeasureTheory.lintegral_iSup' hU_meas hU_mono, MeasureTheory.lintegral_congr hpt]
    rw [h2]
    refine iSup_le (fun m => ?_)
    rw [hu_lintegral m]
    exact ENNReal.ofReal_le_ofReal (hkey m)
  have hfin : eLpNorm h (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal D := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal 3) (by simp) (by simp)
        hh_meas.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3)]
    calc (∫⁻ x : ℝ, ‖h x‖ₑ ^ (3:ℝ)) ^ ((1:ℝ)/3)
        ≤ (ENNReal.ofReal (D^3)) ^ ((1:ℝ)/3) := ENNReal.rpow_le_rpow hsup (by norm_num)
      _ = ENNReal.ofReal D := by
          rw [ENNReal.ofReal_pow hDnn 3, ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_mul (ENNReal.ofReal D) (((3:ℕ)):ℝ) ((1:ℝ)/3),
            show (((3:ℕ)):ℝ) * ((1:ℝ)/3) = 1 by norm_num, ENNReal.rpow_one]
  refine le_trans hfin ?_
  rw [hDdef, hF3eq, ENNReal.ofReal_mul hF3nn]
  exact le_of_eq (mul_comm _ _)

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

set_option maxHeartbeats 2000000 in
theorem dyadic_linearized_l3 (K : ℝ → ℂ)
    (hKb : ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, ‖K z‖ ≤ A / (1 + |z|) ^ 2)
    (hKx : MeasureTheory.Integrable (fun x : ℝ => x • K x) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hKlip : ∃ A : ℝ, 0 < A ∧ ∀ u v : ℝ, ‖K u - K v‖ ≤ A * |u - v|)
    (hK0 : (∫ x : ℝ, K x) = 0)
    (hdec : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier K ξ‖ ≤ C * (1 + |ξ|) ^ (-N)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f (ENNReal.ofReal 3)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.eLpNorm (fun x : ℝ =>
          ∑ l ∈ F, e l * (∫ y : ℝ, f y * ((2:ℝ)^l * K ((x - y) * (2:ℝ)^l))))
        (ENNReal.ofReal 3) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm f (ENNReal.ofReal 3)
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨A, hA, hKb'⟩ := hKb
  obtain ⟨B, hB, hKlip'⟩ := hKlip
  have hK : MeasureTheory.Integrable K volume := dl3_integrable K A hA hKb' ⟨B, hB, hKlip'⟩
  have hdec' : ∃ C N : ℝ, 0 < C ∧ 0 < N ∧ ∀ ξ : ℝ,
      ‖FourierTransform.fourier (dl3Ksharp K) ξ‖ ≤ C * (1 + |ξ|) ^ (-N) := by
    obtain ⟨C, N, hC, hN, h⟩ := hdec
    exact ⟨C, N, hC, hN, fun ξ => by rw [dl3Ksharp_fourier K hK ξ, norm_star]; exact h ξ⟩
  obtain ⟨Cp, hCp, hadj0⟩ := dl3_lt_two_bound (dl3Ksharp K) (dl3Ksharp_integrable K hK)
    (dl3Ksharp_integral_zero K hK hK0) (dl3Ksharp_x_integrable K hKx)
    ⟨B, hB, dl3Ksharp_lipschitz K B hKlip'⟩ ⟨A, hA, dl3Ksharp_bounded K A hKb'⟩ hdec'
    (3/2) (by norm_num) (by norm_num)
  have hadj : ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (g : ℝ → ℂ),
      MeasureTheory.Integrable g volume →
      MeasureTheory.eLpNorm (dl3Op (dl3Ksharp K) F (fun l => star (e l)) g)
          (ENNReal.ofReal (3/2)) volume
        ≤ ENNReal.ofReal Cp * MeasureTheory.eLpNorm g (ENNReal.ofReal (3/2)) volume :=
    fun F e he g hg =>
      hadj0 F (fun l => star (e l)) (fun l => by rw [norm_star]; exact he l) g hg
  have hbdd : ∀ (F : Finset ℤ) (e : ℤ → ℂ), (∀ l, ‖e l‖ ≤ 1) → ∀ (f : ℝ → ℂ),
      MeasureTheory.Integrable f volume →
      MeasureTheory.eLpNorm (dl3Op K F e f) (ENNReal.ofReal 3) volume
        ≤ ENNReal.ofReal Cp * MeasureTheory.eLpNorm f (ENNReal.ofReal 3) volume :=
    dl3_l3_bound_of_adjoint K hK ⟨B, hB, hKlip'⟩ ⟨A, hA, hKb'⟩ Cp hCp hadj
  have hKcont : Continuous K := dl3_lipschitz_continuous K ⟨B, hB, hKlip'⟩
  have hκmeas : ∀ (F : Finset ℤ) (e : ℤ → ℂ), Measurable (dl3Kappa K F e) := by
    intro F e
    show Measurable (fun z : ℝ => ∑ l ∈ F, e l * dl3Phi K l z)
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.const_mul ?_ (e l)
    change Measurable (fun z : ℝ => (2:ℝ)^l * K ((2:ℝ)^l * z))
    exact (hKcont.measurable.comp (measurable_const.mul measurable_id)).const_mul _
  have hκ : ∀ (F : Finset ℤ) (e : ℤ → ℂ),
      MeasureTheory.MemLp (dl3Kappa K F e) (ENNReal.ofReal (3/2)) volume :=
    fun F e => dl3_memLp_kappa K hK A hA.le hKb' F e
  refine ⟨Cp, hCp, fun F e he f hf => ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.eLpNorm_congr_ae ?_))
    (dl3_l3_bound K Cp hCp hκmeas hbdd hκ F e he f hf)
  exact Filter.Eventually.of_forall (fun x =>
    (dl3Op_eq_sum K hK ⟨B, hB, hKlip'⟩ ⟨A, hA, hKb'⟩ F e f hf x).symm)


end Commons.Analysis.Fourier
