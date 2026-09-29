import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed

open Filter
open scoped BigOperators Topology
noncomputable section

namespace Commons.Analysis.InfiniteSum



lemma pow_geom_inv (r t : ℝ) (hr : r ≠ 0) (m j : ℕ) :
    t ^ m * (r ^ (m + j))⁻¹ = (t / r) ^ m * (r ^ j)⁻¹ := by
  rw [pow_add]
  rw [mul_inv_rev]
  calc
    t ^ m * ((r ^ j)⁻¹ * (r ^ m)⁻¹)
        = (t ^ m * (r ^ m)⁻¹) * (r ^ j)⁻¹ := by
          rw [mul_comm (r ^ j)⁻¹ (r ^ m)⁻¹]
          rw [mul_assoc]
    _ = (t / r) ^ m * (r ^ j)⁻¹ := by
          congr 1
          rw [div_pow]
          field_simp

lemma tail_bound {b : ℕ → ℂ} {r : ℝ} (hr : 0 < r) {C : ℝ}
    (hC : ∀ n : ℕ, ‖b n‖ * r ^ n ≤ C) (hC0 : 0 ≤ C)
    {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r / 2) :
    (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) ≤ 2 * (C / r ^ (k + 1)) := by
  let q : ℝ := t / r
  let A : ℝ := C / r ^ (k + 1)
  have hq0 : 0 ≤ q := by dsimp [q]; exact div_nonneg ht0 hr.le
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hr).mpr (by linarith)
  have hq12 : q ≤ 1 / 2 := by
    dsimp [q]
    calc
      t / r ≤ (r / 2) / r := div_le_div_of_nonneg_right htr hr.le
      _ = 1 / 2 := by field_simp [hr.ne']
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg hC0 (pow_nonneg hr.le _)
  have hgeo : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0 hq1
  have hf : Summable (fun m : ℕ => A * q ^ m) := hgeo.mul_left A
  have hterm : ∀ m : ℕ, ‖b (m + k + 1)‖ * t ^ m ≤ A * q ^ m := by
    intro m
    have hb := hC (m + k + 1)
    have hb' : ‖b (m + k + 1)‖ ≤ C / r ^ (m + k + 1) := by
      rw [le_div_iff₀ (pow_pos hr (m + k + 1))]
      exact hb
    have hmul0 : ‖b (m + k + 1)‖ * t ^ m ≤ (C / r ^ (m + k + 1)) * t ^ m := by
      exact mul_le_mul_of_nonneg_right hb' (pow_nonneg ht0 m)
    calc
      ‖b (m + k + 1)‖ * t ^ m ≤ (C / r ^ (m + k + 1)) * t ^ m := hmul0
      _ = C * (t ^ m * (r ^ (m + k + 1))⁻¹) := by ring
      _ = C * ((t / r) ^ m * (r ^ (k + 1))⁻¹) := by
        rw [show m + k + 1 = m + (k + 1) by omega]
        rw [pow_geom_inv r t (ne_of_gt hr) m (k + 1)]
      _ = A * q ^ m := by
        dsimp [A, q]
        ring
  have hg0 : ∀ m : ℕ, 0 ≤ ‖b (m + k + 1)‖ * t ^ m := by
    intro m
    exact mul_nonneg (norm_nonneg _) (pow_nonneg ht0 m)
  have hg : Summable (fun m : ℕ => ‖b (m + k + 1)‖ * t ^ m) := by
    exact Summable.of_nonneg_of_le hg0 hterm hf
  have hsum1 : (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) ≤ (∑' m : ℕ, A * q ^ m) := by
    exact Summable.tsum_le_tsum hterm hg hf
  have hgeo_sum : (∑' m : ℕ, q ^ m) = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
  have hsum2 : (∑' m : ℕ, A * q ^ m) = A * (1 - q)⁻¹ := by
    rw [tsum_mul_left, hgeo_sum]
  have hle_inv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    rw [show (2 : ℝ) = 1 / (1 / 2) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) (by linarith)
  calc
    (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) ≤ (∑' m : ℕ, A * q ^ m) := hsum1
    _ = A * (1 - q)⁻¹ := hsum2
    _ ≤ A * 2 := by
      exact mul_le_mul_of_nonneg_left hle_inv hA0
    _ = 2 * A := by ring
    _ = 2 * (C / r ^ (k + 1)) := by rfl

-- absolute summability of shifted family
lemma summable_norm_shift_pow {b : ℕ → ℂ} {r : ℝ} (hr : 0 < r) {C : ℝ}
    (hC : ∀ n : ℕ, ‖b n‖ * r ^ n ≤ C) {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htr : t < r) :
    Summable (fun m : ℕ => ‖b (m + k) * (t : ℂ) ^ m‖) := by
  let q : ℝ := t / r
  have hq0 : 0 ≤ q := by dsimp [q]; exact div_nonneg ht0 hr.le
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hr).mpr htr
  have hgeo : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0 hq1
  refine Summable.of_norm_bounded (g := fun m : ℕ => (C * (r ^ k)⁻¹) * q ^ m) ?_ ?_
  · exact hgeo.mul_left (C * (r ^ k)⁻¹)
  · intro m
    have hb := hC (m + k)
    have hb' : ‖b (m + k)‖ ≤ C / r ^ (m + k) := by
      rw [le_div_iff₀ (pow_pos hr (m + k))]
      exact hb
    have hmul0 : ‖b (m + k)‖ * t ^ m ≤ (C / r ^ (m + k)) * t ^ m := by
      exact mul_le_mul_of_nonneg_right hb' (pow_nonneg ht0 m)
    have hmain : ‖b (m + k) * (t : ℂ) ^ m‖ ≤ (C * (r ^ k)⁻¹) * q ^ m := by
      calc
        ‖b (m + k) * (t : ℂ) ^ m‖ = ‖b (m + k)‖ * t ^ m := by
          rw [norm_mul, norm_pow]
          simp [abs_of_nonneg ht0]
        _ ≤ (C / r ^ (m + k)) * t ^ m := hmul0
        _ = C * (t ^ m * (r ^ (m + k))⁻¹) := by ring
        _ = C * ((t / r) ^ m * (r ^ k)⁻¹) := by
          rw [pow_geom_inv r t (ne_of_gt hr) m k]
        _ = (C * (r ^ k)⁻¹) * q ^ m := by
          dsimp [q]
          ring
    -- goal: ‖(‖b (m+k)*(t:ℂ)^m‖)‖ ≤ ...
    simpa using hmain

-- coeff bound
lemma coeff_bound_of_hasSum_pos {b : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hHas : HasSum (fun n : ℕ => b n * (r : ℂ) ^ n) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖b n‖ * r ^ n ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq hHas.tendsto_sum_nat.cauchySeq
  refine ⟨C, ?_, fun n => ?_⟩
  · have := hC 0
    have hn0 : 0 ≤ ‖b 0 * (r : ℂ) ^ 0‖ := norm_nonneg _
    linarith
  · have h := hC n
    rw [norm_mul, norm_pow] at h
    simpa [abs_of_nonneg hr.le] using h

-- b0
lemma b0_eq_zero {b : ℕ → ℂ} (h0 : HasSum (fun n : ℕ => b n * (0 : ℂ) ^ n) 0) : b 0 = 0 := by
  have ht : (∑' n : ℕ, b n * (0 : ℂ) ^ n) = 0 := h0.tsum_eq
  have hsum : (∑' n : ℕ, b n * (0 : ℂ) ^ n) = b 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      cases n with
      | zero => contradiction
      | succ n => simp
  rw [hsum] at ht
  exact ht

-- shifted HasSum zero
lemma hasSum_shifted_zero {b : ℕ → ℂ} {k : ℕ} (hb : ∀ j < k, b j = 0)
    {ε : ℝ} (hP : ∀ t : ℝ, |t| < ε → HasSum (fun n : ℕ => b n * (t : ℂ) ^ n) 0)
    {t : ℝ} (ht0 : 0 < t) (htε : t < ε) :
    HasSum (fun m : ℕ => b (m + k) * (t : ℂ) ^ m) 0 := by
  have hsum : HasSum (fun n : ℕ => b n * (t : ℂ) ^ n) 0 := hP t (by simpa [abs_of_pos ht0] using htε)
  have hfk : (∑ i ∈ Finset.range k, b i * (t : ℂ) ^ i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hb i (Finset.mem_range.mp hi)]
  have hshift : HasSum (fun m : ℕ => b (m + k) * (t : ℂ) ^ (m + k)) 0 := by
    have hiff := (hasSum_nat_add_iff (f := fun n : ℕ => b n * (t : ℂ) ^ n) (g := 0) (k := k))
    exact hiff.mpr (by simpa [hfk] using hsum)
  have htz : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  let c : ℂ := ((t : ℂ) ^ k)⁻¹
  have hmul : HasSum (fun m : ℕ => c * (b (m + k) * (t : ℂ) ^ (m + k))) (c * 0) :=
    hshift.mul_left c
  have hmul' : HasSum (fun m : ℕ => c * (b (m + k) * (t : ℂ) ^ (m + k))) 0 := by
    simpa using hmul
  have hfac : ∀ m : ℕ, c * (b (m + k) * (t : ℂ) ^ (m + k)) = b (m + k) * (t : ℂ) ^ m := by
    intro m
    dsimp [c]
    have hz : (t : ℂ) ^ k ≠ 0 := pow_ne_zero k htz
    calc
      ((t : ℂ) ^ k)⁻¹ * (b (m + k) * (t : ℂ) ^ (m + k))
          = ((t : ℂ) ^ k)⁻¹ * (t : ℂ) ^ (m + k) * b (m + k) := by ring
      _ = b (m + k) * (t : ℂ) ^ m * (((t : ℂ) ^ k)⁻¹ * (t : ℂ) ^ k) := by
        rw [add_comm m k, pow_add]
        ring
      _ = b (m + k) * (t : ℂ) ^ m := by
        rw [inv_mul_cancel₀ hz, mul_one]
  simpa [hfac] using hmul'

-- norm |∑'w - b k| ≤ t * tail
lemma norm_tsum_shift_sub_head {b : ℕ → ℂ} {t : ℝ} (ht0 : 0 ≤ t) (k : ℕ)
    (hwAbs : Summable (fun m : ℕ => ‖b (m + k) * (t : ℂ) ^ m‖)) :
    ‖(∑' m : ℕ, b (m + k) * (t : ℂ) ^ m) - b k‖ ≤
      t * (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) := by
  let w : ℕ → ℂ := fun m => b (m + k) * (t : ℂ) ^ m
  have hw : Summable w := hwAbs.of_norm
  have hw0 : w 0 = b k := by simp [w]
  have hshift : (∑' m : ℕ, w (m + 1)) = (∑' m : ℕ, w m) - w 0 := by
    have hg : HasSum (fun m : ℕ => w (m + 1)) ((∑' m : ℕ, w m) - w 0) := by
      rw [hasSum_nat_add_iff (f := w) (g := (∑' m : ℕ, w m) - w 0) (k := 1)]
      simpa using hw.hasSum
    exact hg.tsum_eq
  have hnorm : ‖(∑' m : ℕ, w (m + 1))‖ ≤ (∑' m : ℕ, ‖w (m + 1)‖) := by
    exact norm_tsum_le_tsum_norm
      ((summable_nat_add_iff (f := fun m : ℕ => ‖w m‖) (k := 1)).mpr hwAbs)
  have hterm : ∀ m : ℕ, ‖w (m + 1)‖ = t * (‖b (m + k + 1)‖ * t ^ m) := by
    intro m
    dsimp [w]
    have hmk : m + 1 + k = m + k + 1 := by omega
    rw [hmk]
    rw [norm_mul, norm_pow]
    have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht0]
    rw [hnt, pow_succ]
    ring
  calc
    ‖(∑' m : ℕ, b (m + k) * (t : ℂ) ^ m) - b k‖
        = ‖(∑' m : ℕ, w m) - w 0‖ := by
          rw [← hw0]
    _ = ‖∑' m : ℕ, w (m + 1)‖ := by rw [← hshift]
    _ ≤ ∑' m : ℕ, ‖w (m + 1)‖ := hnorm
    _ = ∑' m : ℕ, t * (‖b (m + k + 1)‖ * t ^ m) := by
      exact tsum_congr hterm
    _ = t * (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) := by
      rw [tsum_mul_left]

-- extract interval from nhds
lemma abs_lt_eventually_nhds {p : ℝ → Prop} (hp : ∀ᶠ t : ℝ in 𝓝 0, p t) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → p t := by
  rw [Metric.eventually_nhds_iff] at hp
  rcases hp with ⟨ε, hε, h⟩
  refine ⟨ε, hε, fun t ht => h ?_⟩
  simpa using ht

theorem hasSum_pow_eq_zero_of_eventually_zero {b : ℕ → ℂ}
    (hb : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasSum (fun n : ℕ => b n * (t : ℂ) ^ n) 0) :
    ∀ n : ℕ, b n = 0 := by
  obtain ⟨ε, hε0, hP⟩ := abs_lt_eventually_nhds hb
  let r : ℝ := ε / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrε : r < ε := by dsimp [r]; linarith
  have hPr : ∀ t : ℝ, |t| < r → HasSum (fun n : ℕ => b n * (t : ℂ) ^ n) 0 := fun t ht => hP t (by linarith)
  have hHasR : HasSum (fun n : ℕ => b n * (r : ℂ) ^ n) 0 := hP r (by simpa [abs_of_pos hr0] using hrε)
  obtain ⟨C, hC0, hC⟩ := coeff_bound_of_hasSum_pos hr0 hHasR
  have hb0 : b 0 = 0 := b0_eq_zero (hP 0 (by simpa using hε0))
  have step : ∀ k : ℕ, (∀ j, j < k → b j = 0) → b k = 0 := by
    intro k hbk
    by_contra hk
    have hnormpos : 0 < ‖b k‖ := norm_pos_iff.mpr hk
    let K : ℝ := 2 * (C / r ^ (k + 1))
    have hK0 : 0 ≤ K := by
      dsimp [K]
      positivity
    have hmain_ineq : ∀ t : ℝ, 0 < t → t ≤ r / 2 → ‖b k‖ ≤ K * t := by
      intro t ht0 htr
      have hG : HasSum (fun m : ℕ => b (m + k) * (t : ℂ) ^ m) 0 :=
        hasSum_shifted_zero hbk hPr ht0 (by linarith)
      have hGtsum : (∑' m : ℕ, b (m + k) * (t : ℂ) ^ m) = 0 := hG.tsum_eq
      have hAbs : Summable (fun m : ℕ => ‖b (m + k) * (t : ℂ) ^ m‖) :=
        summable_norm_shift_pow hr0 hC ht0.le (by linarith)
      have hnorm := norm_tsum_shift_sub_head ht0.le k hAbs
      have htail : (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) ≤ K := by
        simpa [K] using tail_bound hr0 hC hC0 ht0.le htr
      calc
        ‖b k‖ = ‖(∑' m : ℕ, b (m + k) * (t : ℂ) ^ m) - b k‖ := by
          rw [hGtsum]
          simp
        _ ≤ t * (∑' m : ℕ, ‖b (m + k + 1)‖ * t ^ m) := hnorm
        _ ≤ t * K := by
          exact mul_le_mul_of_nonneg_left htail ht0.le
        _ = K * t := by ring
    by_cases hKz : K = 0
    · have h := hmain_ineq (r / 2) (by linarith) (le_refl _)
      have : ‖b k‖ ≤ 0 := by simpa [hKz] using h
      linarith
    · have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKz)
      let t0 : ℝ := min (r / 2) (‖b k‖ / (2 * K))
      have ht0pos : 0 < t0 := by
        dsimp [t0]
        exact lt_min (by linarith) (div_pos hnormpos (by positivity))
      have ht0le : t0 ≤ r / 2 := min_le_left _ _
      have h := hmain_ineq t0 ht0pos ht0le
      have h2 : K * t0 ≤ ‖b k‖ / 2 := by
        have ht0b : t0 ≤ ‖b k‖ / (2 * K) := min_le_right _ _
        have h2K : (2 : ℝ) * K ≠ 0 := mul_ne_zero (by norm_num) hKz
        have hcalc : K * (‖b k‖ / (2 * K)) = ‖b k‖ / 2 := by
          field_simp [h2K]
        calc
          K * t0 ≤ K * (‖b k‖ / (2 * K)) := mul_le_mul_of_nonneg_left ht0b hK0
          _ = ‖b k‖ / 2 := hcalc
      linarith
  have hall : ∀ k : ℕ, ∀ j, j < k → b j = 0 := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
        intro j hj
        by_cases hjk : j = k
        · subst j; exact step k ih
        · have hjl : j < k := by omega
          exact ih j hjl
  intro n
  exact hall (n + 1) n (by omega)


end Commons.Analysis.InfiniteSum