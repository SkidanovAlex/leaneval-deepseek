import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal Topology BigOperators
namespace Commons.Analysis.Calculus
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

lemma integral_sub_rpow (a b r : ℝ) (hab : a ≤ b) (hr : -1 < r) :
    ∫ x in a..b, (x - a) ^ r = (b - a) ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ r) a]
  simp only [sub_self]
  rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), sub_zero]

def knotGaps (n : ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j + 1 < n then b (j + 1) - b j else 0

def knotPowSum (n : ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, (knotGaps n b j) ^ (3/2:ℝ)

def knotQ (n : ℕ) (b : ℕ → ℝ) : ℝ :=
  (Real.sqrt 2)⁻¹ * knotPowSum n b n + (1 - b (n-1))^(3/2:ℝ)

def knotA (n : ℕ) (b : ℕ → ℝ) : ℝ := (knotQ n b)⁻¹

def knotTime (n : ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  knotA n b * (Real.sqrt 2)⁻¹ * knotPowSum n b i

lemma knotPowSum_succ (n : ℕ) (b : ℕ → ℝ) (i : ℕ) :
    knotPowSum n b (i+1) = knotPowSum n b i + (knotGaps n b i) ^ (3/2:ℝ) := by
  simp [knotPowSum, Finset.sum_range_succ]

lemma knotTime_zero (n : ℕ) (b : ℕ → ℝ) : knotTime n b 0 = 0 := by
  simp [knotTime, knotPowSum]

lemma knotTime_succ_sub (n : ℕ) (b : ℕ → ℝ) (i : ℕ) :
    knotTime n b (i+1) - knotTime n b i
      = knotA n b * (Real.sqrt 2)⁻¹ * (knotGaps n b i) ^ (3/2:ℝ) := by
  rw [knotTime, knotTime, knotPowSum_succ]; ring

lemma b_le_of_le {n : ℕ} {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) :
    ∀ i j, i ≤ j → j < n → b i ≤ b j := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
      have hkn : k < n := by omega
      have h1 : b k < b (k+1) := hbmono k (by omega)
      have h2 : b i ≤ b k := ih (by omega)
      linarith

lemma b_nonneg {n : ℕ} {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) {j : ℕ} (hj : j < n) : 0 ≤ b j := by
  have := b_le_of_le hbmono 0 j (by omega) hj
  linarith

lemma knotGaps_nonneg {n : ℕ} {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (j : ℕ) : 0 ≤ knotGaps n b j := by
  unfold knotGaps
  split_ifs with h
  · have : b j ≤ b (j+1) := le_of_lt (hbmono j h); linarith
  · norm_num

lemma knotGaps_eq {n : ℕ} {b : ℕ → ℝ} {j : ℕ} (h : j + 1 < n) :
    knotGaps n b j = b (j+1) - b j := by simp [knotGaps, h]

lemma knotGaps_zero {n : ℕ} {b : ℕ → ℝ} {j : ℕ} (h : ¬ j + 1 < n) : knotGaps n b j = 0 := by
  simp [knotGaps, h]

lemma knotGaps_pos {n : ℕ} {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    {j : ℕ} (h : j+1 < n) : 0 < knotGaps n b j := by
  rw [knotGaps_eq h]; linarith [hbmono j h]

lemma knotQ_pos {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) : 0 < knotQ n b := by
  have h1 : 0 < 1 - b (n-1) := by linarith
  have h2 : 0 < (1 - b (n-1))^(3/2:ℝ) := Real.rpow_pos_of_pos h1 _
  have h3 : 0 ≤ (Real.sqrt 2)⁻¹ * knotPowSum n b n := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro j hj
    exact Real.rpow_nonneg (knotGaps_nonneg hbmono j) _
  unfold knotQ; linarith

lemma knotA_pos {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) : 0 < knotA n b := by
  rw [knotA]; exact inv_pos.mpr (knotQ_pos hn hbmono hbtop)

lemma knotPowSum_nonneg {n : ℕ} {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (i : ℕ) : 0 ≤ knotPowSum n b i := by
  apply Finset.sum_nonneg; intro j hj
  exact Real.rpow_nonneg (knotGaps_nonneg hbmono j) _

lemma knotTime_nonneg {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) (i : ℕ) : 0 ≤ knotTime n b i := by
  rw [knotTime]
  exact mul_nonneg (mul_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) (by positivity))
    (knotPowSum_nonneg hbmono i)

lemma rpow_add_le_add_rpow {p : ℝ} (hp : 1 ≤ p) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ p + y ^ p ≤ (x + y) ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hy0 : 0 ≤ p - 1 := by linarith
  have hp1 : p - 1 + 1 ≠ 0 := by linarith
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hexp : (x + y) ^ p = x * (x + y) ^ (p - 1) + y * (x + y) ^ (p - 1) := by
    rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one' hxy hp1]
    ring_nf
  have hx' : x ^ p = x * x ^ (p - 1) := by
    rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one' hx hp1]
    ring_nf
  have hy' : y ^ p = y * y ^ (p - 1) := by
    rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one' hy hp1]
    ring_nf
  have h1 : x * x ^ (p - 1) ≤ x * (x + y) ^ (p - 1) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx (le_add_of_nonneg_right hy) hy0) hx
  have h2 : y * y ^ (p - 1) ≤ y * (x + y) ^ (p - 1) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy (le_add_of_nonneg_left hx) hy0) hy
  rw [hx', hy', hexp]
  linarith

lemma finset_sum_rpow_le {p : ℝ} (hp : 1 ≤ p) {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) : ∑ i ∈ s, (f i) ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Real.zero_rpow (by linarith : p ≠ 0)]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hfs
      calc f a ^ p + ∑ i ∈ s, (f i) ^ p ≤ f a ^ p + (∑ i ∈ s, f i) ^ p :=
            add_le_add le_rfl (ih hfs)
        _ ≤ (f a + ∑ i ∈ s, f i) ^ p := rpow_add_le_add_rpow hp hfa hsn

lemma knotPowSum_le_top {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) :
    knotPowSum n b n ≤ (b (n-1)) ^ (3/2:ℝ) := by
  have hn' : n = (n-1)+1 := by omega
  have hsum_succ : knotPowSum n b n
      = knotPowSum n b (n-1) + (knotGaps n b (n-1))^(3/2:ℝ) := by
    conv_lhs => rw [knotPowSum, hn', Finset.sum_range_succ]
    rw [knotPowSum, show n - 1 + 1 = n by omega]
  rw [hsum_succ, knotGaps_zero (by omega), Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0), add_zero]
  have hcongr : knotPowSum n b (n-1)
      = ∑ j ∈ Finset.range (n-1), (b (j+1) - b j) ^ (3/2:ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < n-1 := Finset.mem_range.mp hj
    rw [knotGaps_eq (by omega)]
  rw [hcongr]
  have hle := finset_sum_rpow_le (by norm_num : (1:ℝ) ≤ 3/2) (Finset.range (n-1))
    (f := fun j => b (j+1) - b j) (fun j hj => by
      have hj' : j < n-1 := Finset.mem_range.mp hj
      have := hbmono j (by omega); linarith)
  rw [Finset.sum_range_sub b (n-1), hb0, sub_zero] at hle
  exact hle

lemma rpow_three_halves_add_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t ^ (3/2:ℝ) + (1 - t) ^ (3/2:ℝ) ≤ 1 := by
  have ht : t ^ (3/2:ℝ) ≤ t := Real.rpow_le_self_of_le_one h0 h1 (by norm_num)
  have hu : (1 - t) ^ (3/2:ℝ) ≤ 1 - t :=
    Real.rpow_le_self_of_le_one (by linarith) (by linarith) (by norm_num)
  linarith

lemma knotQ_le_one {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    knotQ n b ≤ 1 := by
  have htop0 : 0 ≤ b (n-1) := b_nonneg hb0 hbmono (by omega)
  have htop1 : b (n-1) ≤ 1 := by linarith
  have hps := knotPowSum_le_top hn hb0 hbmono
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.mpr (by norm_num))]
    exact Real.one_le_sqrt.mpr (by norm_num)
  unfold knotQ
  have h1 : (Real.sqrt 2)⁻¹ * knotPowSum n b n ≤ (b (n-1)) ^ (3/2:ℝ) := by
    have h2 : (Real.sqrt 2)⁻¹ * knotPowSum n b n
        ≤ (Real.sqrt 2)⁻¹ * (b (n-1)) ^ (3/2:ℝ) :=
      mul_le_mul_of_nonneg_left hps (by positivity)
    have h3 : (Real.sqrt 2)⁻¹ * (b (n-1)) ^ (3/2:ℝ) ≤ 1 * (b (n-1)) ^ (3/2:ℝ) :=
      mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg htop0 _)
    linarith
  have h4 := rpow_three_halves_add_le_one htop0 htop1
  linarith

lemma knotA_ge_one {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    1 ≤ knotA n b := by
  rw [knotA]
  exact (one_le_inv₀ (knotQ_pos hn hbmono hbtop)).mpr (knotQ_le_one hn hb0 hbmono hbtop)

lemma knotA_rpow_neg_le_one {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) {q : ℝ}
    (hq : q ≤ 0) : (knotA n b) ^ q ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (knotA_ge_one hn hb0 hbmono hbtop) hq

lemma knotQ_ge_rpow {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1/2) : c ^ (3/2:ℝ) ≤ knotQ n b := by
  have h1 : c ^ (3/2:ℝ) ≤ (1/2:ℝ) ^ (3/2:ℝ) := Real.rpow_le_rpow hc0.le hc (by norm_num)
  have h2 : (1/2:ℝ) ^ (3/2:ℝ) ≤ (1 - b (n-1)) ^ (3/2:ℝ) :=
    Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have h3 : (1 - b (n-1)) ^ (3/2:ℝ) ≤ knotQ n b := by
    unfold knotQ
    have h4 : 0 ≤ (Real.sqrt 2)⁻¹ * knotPowSum n b n := by
      apply mul_nonneg (by positivity)
      exact knotPowSum_nonneg hbmono n
    linarith
  linarith

lemma knotA_le_of_le_half {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1/2) : knotA n b ≤ c ^ (-(3/2):ℝ) := by
  have hge := knotQ_ge_rpow hn hb0 hbmono hbtop hc0 hc
  have hcpos : 0 < c ^ (3/2:ℝ) := Real.rpow_pos_of_pos hc0 _
  have hQpos : 0 < knotQ n b := knotQ_pos hn hbmono hbtop
  have h1 : (knotQ n b)⁻¹ ≤ (c ^ (3/2:ℝ))⁻¹ := (inv_le_inv₀ hQpos hcpos).mpr hge
  have h2 : (c ^ (3/2:ℝ))⁻¹ = c ^ (-(3/2):ℝ) := by
    rw [← Real.rpow_neg hc0.le]
  rw [h2] at h1
  rw [knotA]
  exact h1

lemma knotA_rpow_ge_c {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1/2) : c ≤ (knotA n b) ^ (-(2/3):ℝ) := by
  have hle := knotA_le_of_le_half hn hb0 hbmono hbtop hc0 hc
  have hApos : 0 < knotA n b := knotA_pos hn hbmono hbtop
  have h1 : (c ^ (-(3/2):ℝ)) ^ (-(2/3):ℝ) ≤ (knotA n b) ^ (-(2/3):ℝ) :=
    Real.rpow_le_rpow_of_nonpos hApos hle (by norm_num)
  have h2 : (c ^ (-(3/2):ℝ)) ^ (-(2/3):ℝ) = c := by
    rw [← Real.rpow_mul hc0.le]
    norm_num
  linarith [h1, h2.symm ▸ h1]

lemma knotTime_lt_succ {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) {k : ℕ} (hk : k+1 < n) :
    knotTime n b k < knotTime n b (k+1) := by
  have hA : 0 < knotA n b := knotA_pos hn hbmono hbtop
  have hgp : 0 < knotGaps n b k := knotGaps_pos hbmono hk
  have hpos : 0 < knotA n b * (Real.sqrt 2)⁻¹ * (knotGaps n b k) ^ (3/2:ℝ) := by
    have := Real.rpow_pos_of_pos hgp (3/2:ℝ)
    positivity
  have := knotTime_succ_sub n b k
  linarith

lemma knotTime_mono {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) :
    ∀ i j, i ≤ j → j < n → knotTime n b i ≤ knotTime n b j := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
      have hkn : k < n := by omega
      have h1 : knotTime n b i ≤ knotTime n b k := ih hkn
      have h2 : knotTime n b k ≤ knotTime n b (k+1) :=
        le_of_lt (knotTime_lt_succ hn hbmono hbtop (k := k) (by omega))
      linarith

lemma knotTime_lt {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) :
    ∀ i j, i < j → j < n → knotTime n b i < knotTime n b j := by
  intro i j hij hjn
  have h1 : knotTime n b i < knotTime n b (i+1) :=
    knotTime_lt_succ hn hbmono hbtop (k := i) (by omega)
  have h2 : knotTime n b (i+1) ≤ knotTime n b j :=
    knotTime_mono hn hbmono hbtop (i+1) j (by omega) hjn
  linarith


lemma knotPowSum_stable (n : ℕ) (b : ℕ → ℝ) :
    ∀ i, n-1 ≤ i → knotPowSum n b i = knotPowSum n b (n-1) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      rw [knotPowSum_succ, ih, knotGaps_zero (by omega), Real.zero_rpow (by norm_num : (3/2:ℝ) ≠ 0), add_zero]

lemma knotTime_stable (n : ℕ) (b : ℕ → ℝ) :
    ∀ i, n-1 ≤ i → knotTime n b i = knotTime n b (n-1) := by
  intro i hi
  simp only [knotTime, knotPowSum_stable n b i hi]

lemma one_sub_knotTime_top {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    1 - knotTime n b (n-1) = knotA n b * (1 - b (n-1)) ^ (3/2:ℝ) := by
  have hQ : knotQ n b = (Real.sqrt 2)⁻¹ * knotPowSum n b n + (1 - b (n-1)) ^ (3/2:ℝ) := rfl
  have hkey : (Real.sqrt 2)⁻¹ * knotPowSum n b (n-1)
      = knotQ n b - (1 - b (n-1)) ^ (3/2:ℝ) := by
    rw [hQ, knotPowSum_stable n b n (by omega)]
    ring
  have hkt : knotTime n b (n-1) = knotA n b * (knotQ n b - (1 - b (n-1)) ^ (3/2:ℝ)) := by
    rw [knotTime, mul_assoc, hkey]
  have hA : knotA n b * knotQ n b = 1 := by
    rw [knotA]; exact inv_mul_cancel₀ (ne_of_gt (knotQ_pos hn hbmono hbtop))
  rw [hkt]
  have hexp : knotA n b * (knotQ n b - (1 - b (n-1)) ^ (3/2:ℝ))
      = knotA n b * knotQ n b - knotA n b * (1 - b (n-1)) ^ (3/2:ℝ) := by ring
  rw [hexp, hA]
  ring

lemma knotTime_top_lt_one {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    knotTime n b (n-1) < 1 := by
  have h := one_sub_knotTime_top hn hbmono hbtop
  have hpos : 0 < knotA n b * (1 - b (n-1)) ^ (3/2:ℝ) := by
    have h1 : 0 < 1 - b (n-1) := by linarith
    exact mul_pos (knotA_pos hn hbmono hbtop) (Real.rpow_pos_of_pos h1 _)
  linarith [h]


def distK (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ((Finset.range n).image (fun j => |t - knotTime n b j|)).min'
    (Finset.image_nonempty.mpr ⟨0, Finset.mem_range.mpr hn⟩)

lemma distK_nonneg (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) : 0 ≤ distK n hn b t := by
  rw [distK, Finset.le_min'_iff]
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  exact abs_nonneg _

lemma distK_le (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) (j : ℕ) (hj : j < n) :
    distK n hn b t ≤ |t - knotTime n b j| := by
  unfold distK
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)

lemma distK_cell {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) (l : ℕ) (hl : l+1 < n) (t : ℝ)
    (ht : t ∈ Icc (knotTime n b l) (knotTime n b (l+1))) :
    distK n hn b t = min (t - knotTime n b l) (knotTime n b (l+1) - t) := by
  apply le_antisymm
  · have h1 : knotTime n b l ≤ t := ht.1
    have h2 : t ≤ knotTime n b (l+1) := ht.2
    have hle1 : distK n hn b t ≤ t - knotTime n b l := by
      simpa [abs_of_nonneg (sub_nonneg.mpr h1)] using distK_le n hn b t l (by omega)
    have hle2 : distK n hn b t ≤ knotTime n b (l+1) - t := by
      simpa [abs_of_nonpos (sub_nonpos.mpr h2), neg_sub] using distK_le n hn b t (l+1) hl
    exact le_min hle1 hle2
  · rw [distK, Finset.le_min'_iff]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hjn : j < n := Finset.mem_range.mp hj
    rcases lt_trichotomy j l with hjl | heq | hjl
    · have h1 : knotTime n b j ≤ knotTime n b l :=
        knotTime_mono hn hbmono hbtop j l (le_of_lt hjl) (by omega)
      have h2 : knotTime n b j ≤ t := le_trans h1 ht.1
      rw [abs_of_nonneg (sub_nonneg.mpr h2)]
      exact le_trans (min_le_left _ _) (by linarith)
    · subst heq
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact min_le_left _ _
    · have h1 : knotTime n b (l+1) ≤ knotTime n b j :=
        knotTime_mono hn hbmono hbtop (l+1) j (by omega) hjn
      have h2 : t ≤ knotTime n b j := le_trans ht.2 h1
      rw [abs_of_nonpos (sub_nonpos.mpr h2), neg_sub]
      exact le_trans (min_le_right _ _) (by linarith)

lemma distK_last {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hbmono : ∀ j, j + 1 < n → b j < b (j+1))
    (hbtop : b (n-1) ≤ 1/2) (t : ℝ)
    (ht : t ∈ Icc (knotTime n b (n-1)) 1) :
    distK n hn b t = t - knotTime n b (n-1) := by
  apply le_antisymm
  · simpa [abs_of_nonneg (sub_nonneg.mpr ht.1)] using distK_le n hn b t (n-1) (by omega)
  · rw [distK, Finset.le_min'_iff]
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hjn : j < n := Finset.mem_range.mp hj
    have h1 : knotTime n b j ≤ knotTime n b (n-1) := knotTime_mono hn hbmono hbtop j (n-1) (by omega) (by omega)
    have h2 : knotTime n b j ≤ t := le_trans h1 ht.1
    rw [abs_of_nonneg (sub_nonneg.mpr h2)]
    linarith




lemma distK_lipschitz (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) :
    LipschitzWith 1 (distK n hn b) := by
  refine LipschitzWith.of_le_add (fun t s => ?_)
  have hmem : distK n hn b s ∈ (Finset.range n).image (fun j => |s - knotTime n b j|) := by
    rw [distK]; exact Finset.min'_mem _ _
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hmem
  have hj' : j < n := Finset.mem_range.mp hj
  have h1 : distK n hn b t ≤ |t - knotTime n b j| := distK_le n hn b t j hj'
  have h2 : |t - knotTime n b j| ≤ |t - s| + |s - knotTime n b j| := by
    have := abs_add_le (t - s) (s - knotTime n b j)
    rwa [show t - s + (s - knotTime n b j) = t - knotTime n b j by ring] at this
  rw [← hval, Real.dist_eq]
  linarith

lemma distK_continuous (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) : Continuous (distK n hn b) :=
  (distK_lipschitz n hn b).continuous

lemma distK_measurable (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) : Measurable (distK n hn b) :=
  (distK_continuous n hn b).measurable

lemma intervalIntegrable_abs_sub_rpow_unit {c r : ℝ} (hr : -1 < r) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume 0 1 := by
  have hleft : IntervalIntegrable (fun x : ℝ => (c - x) ^ r) volume 0 c := by
    have h := (intervalIntegrable_rpow' hr (a := c) (b := (0:ℝ))).comp_sub_left c
    simpa using h
  have hright : IntervalIntegrable (fun x : ℝ => (x - c) ^ r) volume c 1 := by
    have h := (intervalIntegrable_rpow' hr (a := (0:ℝ)) (b := 1 - c)).comp_sub_right c
    simpa using h
  have h1 : IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume 0 c := by
    refine IntervalIntegrable.congr (f := fun x : ℝ => (c - x) ^ r) ?_ hleft
    intro x hx
    rw [uIoc_of_le hc0] at hx
    show (c - x) ^ r = |x - c| ^ r
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), show c - x = -(x - c) by ring]
  have h2 : IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume c 1 := by
    refine IntervalIntegrable.congr (f := fun x : ℝ => (x - c) ^ r) ?_ hright
    intro x hx
    rw [uIoc_of_le hc1] at hx
    show (x - c) ^ r = |x - c| ^ r
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
  exact h1.trans h2

def gK (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  (2/3) * (knotA n b) ^ (-2/3:ℝ) * (distK n hn b t) ^ (-1/3:ℝ)

def FK (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) : ℝ := ∫ s in 0..t, gK n hn b s

lemma gK_nonneg {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) (t : ℝ) :
    0 ≤ gK n hn b t := by
  rw [gK]
  exact mul_nonneg (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) _))
    (Real.rpow_nonneg (distK_nonneg n hn b t) _)

lemma gK_eq_inv {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) (t : ℝ) :
    gK n hn b t
      = (2/3) * (knotA n b) ^ (-2/3:ℝ) * ((distK n hn b t ^ (1/3:ℝ))⁻¹) := by
  rw [gK, ← Real.rpow_neg_one (distK n hn b t ^ (1/3:ℝ)),
    ← Real.rpow_mul (distK_nonneg n hn b t) (1/3:ℝ) (-1:ℝ)]
  norm_num

lemma gK_measurable {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) : Measurable (gK n hn b) := by
  have hcont : Continuous (fun t => distK n hn b t ^ (1/3:ℝ)) :=
    (Real.continuous_rpow_const (by norm_num)).comp (distK_continuous n hn b)
  rw [show gK n hn b = fun t => (2/3) * (knotA n b) ^ (-2/3:ℝ)
      * ((distK n hn b t ^ (1/3:ℝ))⁻¹) from funext (gK_eq_inv hn b)]
  exact measurable_const.mul hcont.measurable.inv

lemma gK_le_sum {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) (t : ℝ) :
    gK n hn b t ≤ (2/3) * (knotA n b) ^ (-2/3:ℝ)
      * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-1/3:ℝ) := by
  have hmem : distK n hn b t ∈ (Finset.range n).image (fun j => |t - knotTime n b j|) := by
    rw [distK]; exact Finset.min'_mem _ _
  obtain ⟨j0, hj0, hval⟩ := Finset.mem_image.mp hmem
  have hterm : |t - knotTime n b j0| ^ (-1/3:ℝ)
      ≤ ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-1/3:ℝ) :=
    Finset.single_le_sum (f := fun j => |t - knotTime n b j| ^ (-1/3:ℝ))
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) hj0
  have hdist : distK n hn b t ^ (-1/3:ℝ) = |t - knotTime n b j0| ^ (-1/3:ℝ) := by
    rw [← hval]
  have hA : 0 ≤ (2/3) * (knotA n b) ^ (-2/3:ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) _)
  rw [gK, hdist]
  exact mul_le_mul_of_nonneg_left hterm hA

lemma intervalIntegrable_gK {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    IntervalIntegrable (gK n hn b) volume 0 1 := by
  have htop1 : knotTime n b (n-1) < 1 := knotTime_top_lt_one hn hbmono hbtop
  have htop1 : knotTime n b (n-1) < 1 := knotTime_top_lt_one hn hbmono hbtop
  have hsumint : IntervalIntegrable
      (fun t => ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-1/3:ℝ)) volume 0 1 := by
    have key : ∀ j ∈ Finset.range n,
        IntervalIntegrable (fun t => |t - knotTime n b j| ^ (-1/3:ℝ)) volume 0 1 := by
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hc0 : 0 ≤ knotTime n b j := knotTime_nonneg hn hbmono hbtop j
      have hc1 : knotTime n b j ≤ 1 := by
        have hm := knotTime_mono hn hbmono hbtop j (n-1) (by omega) (by omega)
        linarith
      exact intervalIntegrable_abs_sub_rpow_unit (by norm_num) hc0 hc1
    have this := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) (Finset.range n)
      (f := fun j t => |t - knotTime n b j| ^ (-1/3:ℝ)) key
    exact this.congr (fun t _ => by rw [Finset.sum_apply])
  have hdom : IntervalIntegrable
      (fun t => (2/3) * (knotA n b) ^ (-2/3:ℝ)
        * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-1/3:ℝ)) volume 0 1 :=
    hsumint.const_mul _
  rw [intervalIntegrable_iff] at hdom ⊢
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hdom ⊢
  refine Integrable.mono' hdom (gK_measurable hn b).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (gK_nonneg hn hbmono hbtop t)]
  exact gK_le_sum hn hbmono hbtop t

lemma intervalIntegrable_abs_sub_rpow_of_le {c r : ℝ} (hr : -1 < r) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume a b := by
  rcases le_total b c with hbc | hcb
  · have h := (intervalIntegrable_rpow' hr (a := c-a) (b := c-b)).comp_sub_left c
    rw [show c - (c - a) = a by ring, show c - (c - b) = b by ring] at h
    refine h.congr (fun t ht => ?_)
    rw [uIoc_of_le hab] at ht
    show (c - t) ^ r = |t - c| ^ r
    rw [abs_of_nonpos (sub_nonpos.mpr (le_trans ht.2 hbc)), show c - t = -(t - c) by ring]
  · rcases le_total a c with hac | hca
    · have h1 : IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume a c := by
        have h := (intervalIntegrable_rpow' hr (a := c-a) (b := c-c)).comp_sub_left c
        rw [show c - (c - a) = a by ring, show c - (c - c) = c by ring] at h
        refine h.congr (fun t ht => ?_)
        rw [uIoc_of_le hac] at ht
        show (c - t) ^ r = |t - c| ^ r
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), show c - t = -(t - c) by ring]
      have h2 : IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume c b := by
        have h := (intervalIntegrable_rpow' hr (a := c-c) (b := b-c)).comp_sub_right c
        rw [show c - c + c = c by ring, show b - c + c = b by ring] at h
        refine h.congr (fun t ht => ?_)
        rw [uIoc_of_le hcb] at ht
        show (t - c) ^ r = |t - c| ^ r
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      exact h1.trans h2
    · have h := (intervalIntegrable_rpow' hr (a := a-c) (b := b-c)).comp_sub_right c
      rw [show a - c + c = a by ring, show b - c + c = b by ring] at h
      refine h.congr (fun t ht => ?_)
      rw [uIoc_of_le hab] at ht
      show (t - c) ^ r = |t - c| ^ r
      rw [abs_of_nonneg (sub_nonneg.mpr (le_trans hca ht.1.le))]

lemma intervalIntegrable_abs_sub_rpow {c r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |t - c| ^ r) volume a b := by
  rcases le_total a b with hab | hab
  · exact intervalIntegrable_abs_sub_rpow_of_le hr hab
  · exact (intervalIntegrable_abs_sub_rpow_of_le hr hab).symm

lemma integral_abs_sub_rpow_neg_two_thirds_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ t in (0:ℝ)..1, |t - c| ^ (-2/3:ℝ) ≤ 6 := by
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => |u| ^ (-2/3:ℝ)) c]
  have h0 : (-c) ≤ 0 := by linarith
  have h1 : 0 ≤ 1 - c := by linarith
  have hL : IntervalIntegrable (fun u : ℝ => |u| ^ (-2/3:ℝ)) volume (-c) 0 := by
    simpa only [sub_zero] using
      (intervalIntegrable_abs_sub_rpow_of_le (c := 0) (r := (-2/3:ℝ)) (by norm_num) h0)
  have hR : IntervalIntegrable (fun u : ℝ => |u| ^ (-2/3:ℝ)) volume 0 (1-c) := by
    simpa only [sub_zero] using
      (intervalIntegrable_abs_sub_rpow_of_le (c := 0) (r := (-2/3:ℝ)) (by norm_num) h1)
  simp only [zero_sub]
  rw [(intervalIntegral.integral_add_adjacent_intervals hL hR).symm]
  have hrpow : ((-2/3:ℝ) + 1) = 1/3 := by norm_num
  have e1 : ∫ u in (-c)..0, |u| ^ (-2/3:ℝ) = 3 * c ^ (1/3:ℝ) := by
    have h := intervalIntegral.integral_comp_neg (fun u : ℝ => |u| ^ (-2/3:ℝ)) (a := (0:ℝ)) (b := c)
    rw [neg_zero] at h
    rw [← h]
    rw [show (∫ x in (0:ℝ)..c, |(-x)| ^ (-2/3:ℝ)) = ∫ x in (0:ℝ)..c, x ^ (-2/3:ℝ) from
      intervalIntegral.integral_congr (fun x hx => by
        rw [uIcc_of_le hc0] at hx
        rw [abs_of_nonpos (by linarith [hx.1] : -x ≤ 0), neg_neg])]
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -2/3)), hrpow,
      Real.zero_rpow (by norm_num : (1/3:ℝ) ≠ 0), sub_zero, div_eq_mul_inv,
      show ((1/3:ℝ))⁻¹ = 3 by norm_num, mul_comm]
  have e2 : ∫ u in (0:ℝ)..(1-c), |u| ^ (-2/3:ℝ) = 3 * (1-c) ^ (1/3:ℝ) := by
    rw [show (∫ x in (0:ℝ)..(1-c), |x| ^ (-2/3:ℝ)) = ∫ x in (0:ℝ)..(1-c), x ^ (-2/3:ℝ) from
      intervalIntegral.integral_congr (fun x hx => by
        rw [uIcc_of_le h1] at hx
        rw [abs_of_nonneg hx.1])]
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -2/3)), hrpow,
      Real.zero_rpow (by norm_num : (1/3:ℝ) ≠ 0), sub_zero, div_eq_mul_inv,
      show ((1/3:ℝ))⁻¹ = 3 by norm_num, mul_comm]
  rw [e1, e2]
  have h3 : c ^ (1/3:ℝ) ≤ 1 := Real.rpow_le_one hc0 hc1 (by norm_num)
  have h4 : (1-c) ^ (1/3:ℝ) ≤ 1 := Real.rpow_le_one h1 (by linarith) (by norm_num)
  linarith


lemma uIoc_subset_uIoc_of {a b c d : ℝ} (h1 : c ≤ a) (h2 : c ≤ b) (h3 : a ≤ d) (h4 : b ≤ d) :
    uIoc a b ⊆ uIoc c d := by
  rw [uIoc, uIoc]
  exact Ioc_subset_Ioc (le_trans (min_le_left c d) (le_min h1 h2))
    (max_le (le_trans h3 (le_max_right c d)) (le_trans h4 (le_max_right c d)))

lemma knotTime_mem_Icc {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) {j : ℕ} (hj : j < n) :
    knotTime n b j ∈ Icc (0:ℝ) 1 :=
  ⟨knotTime_nonneg hn hbmono hbtop j,
    le_of_lt (lt_of_le_of_lt (knotTime_mono hn hbmono hbtop j (n-1) (by omega) (by omega))
      (knotTime_top_lt_one hn hbmono hbtop))⟩

lemma gK_intervalIntegrable_sub {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (gK n hn b) volume x y := by
  rw [intervalIntegrable_iff]
  refine (intervalIntegrable_iff.mp (intervalIntegrable_gK hn hbmono hbtop)).mono_set ?_
  exact uIoc_subset_uIoc_of hx.1 hy.1 hx.2 hy.2

lemma knotTime_inv_sqrt (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    (knotTime n b (j+1) - knotTime n b j)
      = knotA n b * (2:ℝ)^(-1/2:ℝ) * (knotGaps n b j)^(3/2:ℝ) := by
  rw [knotTime_succ_sub]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  ring_nf

lemma cellIntegral {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {l : ℕ} (hl : l+1 < n) :
    ∫ t in (knotTime n b l)..(knotTime n b (l+1)), gK n hn b t = knotGaps n b l := by
  set tl := knotTime n b l with htl
  set tr := knotTime n b (l+1) with htr
  set A := knotA n b with hA
  set gp := knotGaps n b l with hgp
  have htlIcc : tl ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop (by omega)
  have htrIcc : tr ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop hl
  have hApos : 0 < A := knotA_pos hn hbmono hbtop
  have hgp_pos : 0 < gp := knotGaps_pos hbmono hl
  have hee : tr - tl = A * (2:ℝ)^(-1/2:ℝ) * gp^(3/2:ℝ) := by
    rw [htl, htr, hA, hgp]; exact knotTime_inv_sqrt n b l
  have he : 0 < tr - tl := by
    rw [hee]; positivity
  set mid := (tl + tr) / 2 with hmid
  have htltr : tl ≤ tr := by linarith
  have htlmid : tl ≤ mid := by rw [hmid]; linarith
  have hmidtr : mid ≤ tr := by rw [hmid]; linarith
  have hmidIcc : mid ∈ Icc (0:ℝ) 1 := ⟨by linarith [htlIcc.1], by linarith [htrIcc.2]⟩
  have hint1 : IntervalIntegrable (gK n hn b) volume tl mid :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop htlIcc hmidIcc
  have hint2 : IntervalIntegrable (gK n hn b) volume mid tr :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop hmidIcc htrIcc
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hleft : ∫ t in tl..mid, gK n hn b t = A^(-2/3:ℝ) * ((mid - tl)^(2/3:ℝ)) := by
    rw [show (∫ t in tl..mid, gK n hn b t)
        = ∫ t in tl..mid, (2/3) * A^(-2/3:ℝ) * (t - tl)^(-1/3:ℝ) from
      intervalIntegral.integral_congr (fun t ht => ?_)]
    · rw [intervalIntegral.integral_const_mul, integral_sub_rpow _ _ _ htlmid (by norm_num)]
      rw [show ((-1/3:ℝ) + 1) = 2/3 by norm_num, div_eq_mul_inv]
      ring_nf
    · rw [uIcc_of_le htlmid] at ht
      have ht' : t ∈ Icc tl tr := ⟨ht.1, le_trans ht.2 hmidtr⟩
      rw [gK, distK_cell hn hbmono hbtop l hl t ht',
        min_eq_left (by linarith [ht.2] : t - tl ≤ tr - t)]
  have hright : ∫ t in mid..tr, gK n hn b t = A^(-2/3:ℝ) * ((tr - mid)^(2/3:ℝ)) := by
    rw [show (∫ t in mid..tr, gK n hn b t)
        = ∫ t in mid..tr, (2/3) * A^(-2/3:ℝ) * (tr - t)^(-1/3:ℝ) from
      intervalIntegral.integral_congr (fun t ht => ?_)]
    · rw [intervalIntegral.integral_const_mul]
      rw [show (∫ t in mid..tr, (tr - t)^(-1/3:ℝ)) = ∫ x in ((0:ℝ))..(tr - mid), x^(-1/3:ℝ) from by
        simpa only [sub_self] using
          intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x^(-1/3:ℝ))
            (a := mid) (b := tr) tr]
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/3))]
      rw [show ((-1/3:ℝ) + 1) = 2/3 by norm_num, Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0),
        sub_zero, div_eq_mul_inv]
      ring_nf
    · rw [uIcc_of_le hmidtr] at ht
      have ht' : t ∈ Icc tl tr := ⟨le_trans htlmid ht.1, ht.2⟩
      rw [gK, distK_cell hn hbmono hbtop l hl t ht',
        min_eq_right (by linarith [ht.1] : tr - t ≤ t - tl)]
  rw [hleft, hright]
  have hmid_eq : mid - tl = (tr - tl)/2 := by rw [hmid]; ring
  have htrmid_eq : tr - mid = (tr - tl)/2 := by rw [hmid]; ring
  rw [hmid_eq, htrmid_eq]
  have h1 : (((tr - tl)/2))^(2/3:ℝ) = A^(2/3:ℝ) * (2:ℝ)^(-1:ℝ) * gp := by
    rw [hee]
    rw [show A * (2:ℝ)^(-1/2:ℝ) * gp^(3/2:ℝ) / 2
        = A * (2:ℝ)^(-1/2:ℝ) * gp^(3/2:ℝ) * (2:ℝ)^(-1:ℝ) by ring]
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (le_of_lt hgp_pos)]
    rw [show (3/2:ℝ) * (2/3) = 1 by norm_num, Real.rpow_one]
    rw [show A^(2/3:ℝ) * 2^(-1/2*(2/3):ℝ) * gp * 2^(-1*(2/3):ℝ)
        = A^(2/3:ℝ) * gp * (2^(-1/2*(2/3):ℝ) * 2^(-1*(2/3):ℝ)) by ring]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
    ring
  rw [h1]
  have hA23 : A^(-2/3:ℝ) * A^(2/3:ℝ) = 1 := by
    rw [← Real.rpow_add hApos, show (-2/3:ℝ) + 2/3 = 0 by norm_num, Real.rpow_zero]
  rw [show A^(-2/3:ℝ) * (A^(2/3:ℝ) * (2:ℝ)^(-1:ℝ) * gp)
        + A^(-2/3:ℝ) * (A^(2/3:ℝ) * (2:ℝ)^(-1:ℝ) * gp)
      = 2 * (A^(-2/3:ℝ) * A^(2/3:ℝ)) * ((2:ℝ)^(-1:ℝ) * gp) by ring]
  rw [hA23]
  rw [show (2:ℝ)^(-1:ℝ) = 1/2 by norm_num]
  ring

lemma lastIntegral {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    ∫ t in (knotTime n b (n-1))..1, gK n hn b t = 1 - b (n-1) := by
  set tl := knotTime n b (n-1) with htl
  set A := knotA n b with hA
  have htlIcc : tl ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop (by omega)
  have h1Icc : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hApos : 0 < A := knotA_pos hn hbmono hbtop
  have htl1 : tl ≤ 1 := htlIcc.2
  have hint : IntervalIntegrable (gK n hn b) volume tl 1 :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop htlIcc h1Icc
  have hcongr : (∫ t in tl..1, gK n hn b t)
      = ∫ t in tl..1, (2/3) * A^(-2/3:ℝ) * (t - tl)^(-1/3:ℝ) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le htl1] at ht
    rw [gK, htl, distK_last hn hbmono hbtop t (by rw [← htl]; exact ht)]
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_sub_rpow _ _ _ htl1 (by norm_num)]
  rw [show ((-1/3:ℝ) + 1) = 2/3 by norm_num]
  rw [show (2/3:ℝ) * A^(-2/3:ℝ) * ((1 - tl)^(2/3:ℝ) / (2/3:ℝ))
      = A^(-2/3:ℝ) * (1 - tl)^(2/3:ℝ) by ring_nf]
  rw [show (1 - tl) = A * (1 - b (n-1))^(3/2:ℝ) by rw [htl, hA]; exact one_sub_knotTime_top hn hbmono hbtop]
  rw [Real.mul_rpow hApos.le (Real.rpow_nonneg (by linarith [hbtop] : (0:ℝ) ≤ 1 - b (n-1)) _)]
  rw [show A^(-2/3:ℝ) * (A^(2/3:ℝ) * ((1 - b (n-1))^(3/2:ℝ))^(2/3:ℝ))
      = (A^(-2/3:ℝ) * A^(2/3:ℝ)) * ((1 - b (n-1))^(3/2:ℝ))^(2/3:ℝ) by ring]
  rw [← Real.rpow_add hApos, show (-2/3:ℝ) + 2/3 = 0 by norm_num, Real.rpow_zero, one_mul]
  rw [← Real.rpow_mul (by linarith [hbtop] : (0:ℝ) ≤ 1 - b (n-1))]
  rw [show ((3/2:ℝ) * (2/3)) = 1 by norm_num, Real.rpow_one]

lemma FK_zero {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) : FK n hn b 0 = 0 := by
  rw [FK, intervalIntegral.integral_same]

lemma FK_knotTime {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j ≤ n-1) : FK n hn b (knotTime n b j) = b j := by
  have hint : ∀ k < j, IntervalIntegrable (gK n hn b) volume (knotTime n b k) (knotTime n b (k+1)) := by
    intro k hk
    exact gK_intervalIntegrable_sub hn hb0 hbmono hbtop
      (knotTime_mem_Icc hn hb0 hbmono hbtop (by omega))
      (knotTime_mem_Icc hn hb0 hbmono hbtop (by omega))
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := gK n hn b)
    (a := knotTime n b) (n := j) hint
  rw [knotTime_zero] at h
  have hcells : ∀ k ∈ Finset.range j, ∫ x in (knotTime n b k)..(knotTime n b (k+1)), gK n hn b x
      = b (k+1) - b k := by
    intro k hk
    have hk' : k < j := Finset.mem_range.mp hk
    rw [cellIntegral hn hb0 hbmono hbtop (l := k) (by omega), knotGaps_eq (by omega)]
  rw [Finset.sum_congr rfl hcells, Finset.sum_range_sub, hb0, sub_zero] at h
  rw [show FK n hn b (knotTime n b j)
      = (∫ x in (0:ℝ)..(knotTime n b j), gK n hn b x) from rfl]
  exact h.symm

lemma FK_one {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    FK n hn b 1 = 1 := by
  have htop : knotTime n b (n-1) ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop (by omega)
  have h1Icc : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h0Icc : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hint1 : IntervalIntegrable (gK n hn b) volume 0 (knotTime n b (n-1)) :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop h0Icc htop
  have hint2 : IntervalIntegrable (gK n hn b) volume (knotTime n b (n-1)) 1 :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop htop h1Icc
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  show (∫ x in (0:ℝ)..1, gK n hn b x) = 1
  rw [← hsplit]
  rw [show (∫ x in (0:ℝ)..(knotTime n b (n-1)), gK n hn b x)
      = FK n hn b (knotTime n b (n-1)) from rfl,
    FK_knotTime hn hb0 hbmono hbtop (le_refl _), lastIntegral hn hb0 hbmono hbtop]
  ring

lemma FK_AC {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    AbsolutelyContinuousOnInterval (FK n hn b) 0 1 := by
  have h := IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (f := gK n hn b) (intervalIntegrable_gK hn hbmono hbtop) (c := 0) (by norm_num)
  change AbsolutelyContinuousOnInterval (fun x => ∫ v in (0:ℝ)..x, gK n hn b v) 0 1
  exact h

lemma FK_mono {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    MonotoneOn (FK n hn b) (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have h0x : IntervalIntegrable (gK n hn b) volume 0 x :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop ⟨le_rfl, by norm_num⟩ hx
  have hxy' : IntervalIntegrable (gK n hn b) volume x y :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop hx hy
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hxy'
  have heq : FK n hn b y = FK n hn b x + ∫ t in x..y, gK n hn b t := by
    rw [FK, FK]
    exact hadd.symm
  have hnn : 0 ≤ ∫ t in x..y, gK n hn b t :=
    intervalIntegral.integral_nonneg hxy (fun t _ => gK_nonneg hn hbmono hbtop t)
  linarith

lemma knotTime_finite_range {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) :
    (Set.range (knotTime n b)).Finite := by
  refine (Finset.finite_toSet (Finset.image (knotTime n b) (Finset.range n))).subset ?_
  rintro x ⟨j, rfl⟩
  rcases lt_or_ge j n with hj | hj
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
  · rw [knotTime_stable n b j (by omega)]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨n-1, Finset.mem_range.mpr (by omega), rfl⟩)

lemma ae_of_forall_notMem_range {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) {P : ℝ → Prop}
    (h : ∀ t, t ∉ Set.range (knotTime n b) → P t) :
    ∀ᵐ t ∂(volume : Measure ℝ), P t := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ ((knotTime_finite_range hn b).measure_zero volume)
  intro t ht
  rw [Set.mem_setOf_eq] at ht
  by_contra hmem
  exact ht (h t hmem)

lemma distK_pos_of_notMem {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) {t : ℝ}
    (ht : t ∉ Set.range (knotTime n b)) : 0 < distK n hn b t := by
  rw [distK, Finset.lt_min'_iff]
  intro y hy
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  have hne : t ≠ knotTime n b j := fun h => ht ⟨j, h.symm⟩
  exact abs_pos.mpr (sub_ne_zero.mpr hne)

lemma continuousAt_gK_of_pos {n : ℕ} (hn : 0 < n) (b : ℕ → ℝ) {t : ℝ}
    (hpos : 0 < distK n hn b t) : ContinuousAt (gK n hn b) t := by
  have hcont : ContinuousAt (distK n hn b) t := (distK_continuous n hn b).continuousAt
  have h1 : ContinuousAt (fun x => distK n hn b x ^ (1/3:ℝ)) t :=
    (Real.continuousAt_rpow_const (distK n hn b t) (1/3:ℝ) (Or.inr (by norm_num))).comp hcont
  have hne : (distK n hn b t ^ (1/3:ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hpos _)
  have h2 : ContinuousAt (fun x => (distK n hn b x ^ (1/3:ℝ))⁻¹) t := h1.inv₀ hne
  rw [show gK n hn b = fun t => (2/3) * (knotA n b) ^ (-2/3:ℝ) * ((distK n hn b t ^ (1/3:ℝ))⁻¹)
      from funext (gK_eq_inv hn b)]
  exact continuousAt_const.mul h2

lemma FK_deriv_of_pos {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) (hpos : 0 < distK n hn b t) :
    deriv (FK n hn b) t = gK n hn b t := by
  have htIcc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hint : IntervalIntegrable (gK n hn b) volume 0 t :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop ⟨le_rfl, by norm_num⟩ htIcc
  have hcont := continuousAt_gK_of_pos hn b hpos
  have h := intervalIntegral.integral_hasDerivAt_right hint (MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter ((gK_measurable hn b).stronglyMeasurable)) hcont
  exact h.deriv

lemma FK_deriv_ae {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (0:ℝ) 1 → deriv (FK n hn b) t = gK n hn b t :=
  ae_of_forall_notMem_range hn b (fun t ht hmem => FK_deriv_of_pos hn hb0 hbmono hbtop hmem
    (distK_pos_of_notMem hn b ht))

lemma gK_sq_eq {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) (t : ℝ) :
    (gK n hn b t)^2
      = (4/9) * (knotA n b)^(-4/3:ℝ) * (distK n hn b t)^(-2/3:ℝ) := by
  rw [gK, mul_pow, mul_pow]
  rw [show ((2/3:ℝ))^2 = 4/9 by norm_num]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (knotA_pos hn hbmono hbtop))]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (distK_nonneg n hn b t)]
    norm_num

lemma gK_sq_le_sum {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) (t : ℝ) :
    (gK n hn b t)^2 ≤ (4/9) * (knotA n b)^(-4/3:ℝ)
      * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ) := by
  rw [gK_sq_eq hn hbmono hbtop t]
  have hmem : distK n hn b t ∈ (Finset.range n).image (fun j => |t - knotTime n b j|) := by
    rw [distK]; exact Finset.min'_mem _ _
  obtain ⟨j0, hj0, hval⟩ := Finset.mem_image.mp hmem
  have hterm : (distK n hn b t) ^ (-2/3:ℝ) ≤
      ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ) := by
    rw [← hval]
    exact Finset.single_le_sum (f := fun j => |t - knotTime n b j| ^ (-2/3:ℝ))
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) hj0
  exact mul_le_mul_of_nonneg_left hterm
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) _))

lemma intervalIntegrable_gK_sq {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    IntervalIntegrable (fun t => (gK n hn b t)^2) volume 0 1 := by
  have htop1 : knotTime n b (n-1) < 1 := knotTime_top_lt_one hn hbmono hbtop
  have hsumint : IntervalIntegrable
      (fun t => (4/9) * (knotA n b)^(-4/3:ℝ)
        * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ)) volume 0 1 := by
    have key : ∀ j ∈ Finset.range n,
        IntervalIntegrable (fun t => |t - knotTime n b j| ^ (-2/3:ℝ)) volume 0 1 := by
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hc0 : 0 ≤ knotTime n b j := knotTime_nonneg hn hbmono hbtop j
      have hc1 : knotTime n b j ≤ 1 := by
        have hm := knotTime_mono hn hbmono hbtop j (n-1) (by omega) (by omega)
        linarith
      exact intervalIntegrable_abs_sub_rpow_unit (by norm_num) hc0 hc1
    have this := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) (Finset.range n)
      (f := fun j t => |t - knotTime n b j| ^ (-2/3:ℝ)) key
    exact ((this.congr (fun t _ => by rw [Finset.sum_apply])).const_mul _)
  rw [intervalIntegrable_iff] at hsumint ⊢
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hsumint ⊢
  refine Integrable.mono' hsumint ((gK_measurable hn b).stronglyMeasurable.pow 2).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (by positivity)]
  exact gK_sq_le_sum hn hbmono hbtop t

lemma cusp_ae_right {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j < n) {t : ℝ} (ht : knotTime n b j ≤ t) :
    (fun s => (2/3)*(knotA n b)^(-2/3:ℝ)*(s - knotTime n b j)^(-1/3:ℝ))
      ≤ᵐ[volume.restrict (Icc (knotTime n b j) t)] (gK n hn b) := by
  change ∀ᵐ s ∂volume.restrict (Icc (knotTime n b j) t),
    (2/3)*(knotA n b)^(-2/3:ℝ)*(s - knotTime n b j)^(-1/3:ℝ) ≤ gK n hn b s
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine ae_of_forall_notMem_range hn b (fun s hs hmem => ?_)
  have hsτ : knotTime n b j ≤ s := hmem.1
  have hpos : 0 < distK n hn b s := distK_pos_of_notMem hn b hs
  have hle : distK n hn b s ≤ s - knotTime n b j := by
    have h := distK_le n hn b s j hj
    rwa [abs_of_nonneg (sub_nonneg.mpr hsτ)] at h
  have hrpow : (s - knotTime n b j)^(-1/3:ℝ) ≤ (distK n hn b s)^(-1/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  rw [gK]
  exact mul_le_mul_of_nonneg_left hrpow
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) _))

lemma cusp_ae_left {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j < n) {t : ℝ} (ht : t ≤ knotTime n b j) :
    (fun s => (2/3)*(knotA n b)^(-2/3:ℝ)*(knotTime n b j - s)^(-1/3:ℝ))
      ≤ᵐ[volume.restrict (Icc t (knotTime n b j))] (gK n hn b) := by
  change ∀ᵐ s ∂volume.restrict (Icc t (knotTime n b j)),
    (2/3)*(knotA n b)^(-2/3:ℝ)*(knotTime n b j - s)^(-1/3:ℝ) ≤ gK n hn b s
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine ae_of_forall_notMem_range hn b (fun s hs hmem => ?_)
  have hsτ : s ≤ knotTime n b j := hmem.2
  have hpos : 0 < distK n hn b s := distK_pos_of_notMem hn b hs
  have hle : distK n hn b s ≤ knotTime n b j - s := by
    have h := distK_le n hn b s j hj
    rwa [abs_of_nonpos (sub_nonpos.mpr hsτ), neg_sub] at h
  have hrpow : (knotTime n b j - s)^(-1/3:ℝ) ≤ (distK n hn b s)^(-1/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  rw [gK]
  exact mul_le_mul_of_nonneg_left hrpow
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (knotA_pos hn hbmono hbtop)) _))

lemma FK_cusp_right {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j < n) {t : ℝ} (ht : t ∈ Icc (knotTime n b j) 1) :
    (knotA n b)^(-2/3:ℝ) * (t - knotTime n b j)^(2/3:ℝ) ≤ FK n hn b t - b j := by
  have htj : knotTime n b j ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop hj
  have htIcc : t ∈ Icc (0:ℝ) 1 := ⟨le_trans htj.1 ht.1, ht.2⟩
  have hτt : knotTime n b j ≤ t := ht.1
  have hint1 : IntervalIntegrable (gK n hn b) volume (knotTime n b j) t :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop htj htIcc
  have hint2 : IntervalIntegrable (gK n hn b) volume 0 (knotTime n b j) :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop ⟨le_rfl, by norm_num⟩ htj
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint2 hint1
  have hFt : FK n hn b t
      = FK n hn b (knotTime n b j) + ∫ s in (knotTime n b j)..t, gK n hn b s := by
    rw [FK, FK]; exact hadd.symm
  have hf : IntervalIntegrable (fun s => (2/3)*(knotA n b)^(-2/3:ℝ)*(s - knotTime n b j)^(-1/3:ℝ))
      volume (knotTime n b j) t := by
    have hc := (intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -1/3)
      (a := (0:ℝ)) (b := t - knotTime n b j)).comp_sub_right (knotTime n b j)
    simpa only [zero_add, sub_add_cancel] using hc.const_mul _
  have hlow : (knotA n b)^(-2/3:ℝ) * (t - knotTime n b j)^(2/3:ℝ)
      ≤ ∫ s in (knotTime n b j)..t, gK n hn b s := by
    have hmono := intervalIntegral.integral_mono_ae_restrict hτt hf hint1
      (cusp_ae_right hn hbmono hbtop hj hτt)
    have hfval : ∫ s in (knotTime n b j)..t,
          (2/3)*(knotA n b)^(-2/3:ℝ)*(s - knotTime n b j)^(-1/3:ℝ)
        = (knotA n b)^(-2/3:ℝ) * (t - knotTime n b j)^(2/3:ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_sub_rpow _ _ _ hτt (by norm_num)]
      rw [show ((-1/3:ℝ)+1)=2/3 by norm_num]
      rw [show (2/3:ℝ)*(knotA n b)^(-2/3:ℝ)*((t-knotTime n b j)^(2/3:ℝ)/(2/3:ℝ))
          = (knotA n b)^(-2/3:ℝ)*(t-knotTime n b j)^(2/3:ℝ) by ring_nf]
    rw [← hfval]; exact hmono
  have hbj : FK n hn b (knotTime n b j) = b j :=
    FK_knotTime hn hb0 hbmono hbtop (by omega : j ≤ n-1)
  rw [hFt, hbj]
  linarith [hlow]

lemma FK_cusp_left {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j < n) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (knotTime n b j)) :
    (knotA n b)^(-2/3:ℝ) * (knotTime n b j - t)^(2/3:ℝ) ≤ b j - FK n hn b t := by
  have htj : knotTime n b j ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop hj
  have htIcc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1, le_trans ht.2 htj.2⟩
  have htt : t ≤ knotTime n b j := ht.2
  have hint1 : IntervalIntegrable (gK n hn b) volume t (knotTime n b j) :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop htIcc htj
  have hint2 : IntervalIntegrable (gK n hn b) volume 0 t :=
    gK_intervalIntegrable_sub hn hb0 hbmono hbtop ⟨le_rfl, by norm_num⟩ htIcc
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint2 hint1
  have hFt : FK n hn b (knotTime n b j)
      = FK n hn b t + ∫ s in t..(knotTime n b j), gK n hn b s := by
    rw [FK, FK]; exact hadd.symm
  have hf : IntervalIntegrable (fun s => (2/3)*(knotA n b)^(-2/3:ℝ)*(knotTime n b j - s)^(-1/3:ℝ))
      volume t (knotTime n b j) := by
    have hc := (intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -1/3)
      (a := knotTime n b j - t) (b := (0:ℝ))).comp_sub_left (knotTime n b j)
    rw [show knotTime n b j - (knotTime n b j - t) = t by ring,
        show knotTime n b j - 0 = knotTime n b j by ring] at hc
    exact hc.const_mul _
  have hlow : (knotA n b)^(-2/3:ℝ) * (knotTime n b j - t)^(2/3:ℝ)
      ≤ ∫ s in t..(knotTime n b j), gK n hn b s := by
    have hmono := intervalIntegral.integral_mono_ae_restrict htt hf hint1
      (cusp_ae_left hn hbmono hbtop hj htt)
    have hfval : ∫ s in t..(knotTime n b j),
          (2/3)*(knotA n b)^(-2/3:ℝ)*(knotTime n b j - s)^(-1/3:ℝ)
        = (knotA n b)^(-2/3:ℝ) * (knotTime n b j - t)^(2/3:ℝ) := by
      rw [intervalIntegral.integral_const_mul]
      rw [show (∫ s in t..(knotTime n b j), (knotTime n b j - s)^(-1/3:ℝ))
          = ∫ x in ((0:ℝ))..(knotTime n b j - t), x^(-1/3:ℝ) from by
        simpa only [sub_self] using
          intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x^(-1/3:ℝ))
            (a := t) (b := knotTime n b j) (knotTime n b j)]
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/3))]
      rw [show ((-1/3:ℝ)+1)=2/3 by norm_num, Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0),
        sub_zero, div_eq_mul_inv]
      ring_nf
    rw [← hfval]; exact hmono
  have hbj : FK n hn b (knotTime n b j) = b j :=
    FK_knotTime hn hb0 hbmono hbtop (by omega : j ≤ n-1)
  rw [hFt] at hbj
  linarith [hbj, hlow]

lemma FK_image {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : FK n hn b t ∈ Icc (0:ℝ) 1 := by
  have h1Icc : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have h0Icc : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h0t : FK n hn b 0 ≤ FK n hn b t :=
    FK_mono hn hb0 hbmono hbtop h0Icc ht (by linarith [ht.1])
  have ht1 : FK n hn b t ≤ FK n hn b 1 :=
    FK_mono hn hb0 hbmono hbtop ht h1Icc ht.2
  rw [FK_zero hn b] at h0t
  rw [FK_one hn hb0 hbmono hbtop] at ht1
  exact ⟨h0t, ht1⟩

lemma knotTime_le_one' {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ}
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {j : ℕ} (hj : j < n) : knotTime n b j ≤ 1 := by
  have hm := knotTime_mono hn hbmono hbtop j (n-1) (by omega) (by omega)
  linarith [knotTime_top_lt_one hn hbmono hbtop]

lemma FK_energy {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    ∫ t in (0:ℝ)..1, (deriv (FK n hn b) t)^2 ≤ (8/3) * n := by
  have hdomint : IntervalIntegrable
      (fun t => (4/9) * (knotA n b)^(-4/3:ℝ)
        * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ)) volume 0 1 := by
    have key : ∀ j ∈ Finset.range n,
        IntervalIntegrable (fun t => |t - knotTime n b j| ^ (-2/3:ℝ)) volume 0 1 := by
      intro j hj
      exact intervalIntegrable_abs_sub_rpow_unit (by norm_num)
        (knotTime_nonneg hn hbmono hbtop j) (knotTime_le_one' hn hbmono hbtop (Finset.mem_range.mp hj))
    have this := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) (Finset.range n)
      (f := fun j t => |t - knotTime n b j| ^ (-2/3:ℝ)) key
    exact ((this.congr (fun t _ => by rw [Finset.sum_apply])).const_mul _)
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (intervalIntegrable_gK_sq hn hbmono hbtop) hdomint
    (fun t _ => gK_sq_le_sum hn hbmono hbtop t)
  have hkey : ∫ t in (0:ℝ)..1, (4/9) * (knotA n b)^(-4/3:ℝ)
        * ∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ) ≤ (8/3) * n := by
    rw [intervalIntegral.integral_const_mul]
    have hsum : ∫ t in (0:ℝ)..1, (∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ)) ≤ 6*n := by
      rw [intervalIntegral.integral_finset_sum (s := Finset.range n)
        (f := fun j t => |t - knotTime n b j| ^ (-2/3:ℝ))
        (fun j hj => intervalIntegrable_abs_sub_rpow_unit (by norm_num)
          (knotTime_nonneg hn hbmono hbtop j)
          (knotTime_le_one' hn hbmono hbtop (Finset.mem_range.mp hj)))]
      calc ∑ j ∈ Finset.range n, ∫ t in (0:ℝ)..1, |t - knotTime n b j| ^ (-2/3:ℝ)
            ≤ ∑ j ∈ Finset.range n, 6 := Finset.sum_le_sum (fun j hj =>
              integral_abs_sub_rpow_neg_two_thirds_le (knotTime_nonneg hn hbmono hbtop j)
                (knotTime_le_one' hn hbmono hbtop (Finset.mem_range.mp hj)))
        _ = 6*n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have hInt_nonneg : 0 ≤ ∫ t in (0:ℝ)..1,
        (∑ j ∈ Finset.range n, |t - knotTime n b j| ^ (-2/3:ℝ)) :=
      intervalIntegral.integral_nonneg (by norm_num)
        (fun t _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _))
    have hAle : (knotA n b)^(-4/3:ℝ) ≤ 1 := knotA_rpow_neg_le_one hn hb0 hbmono hbtop (by norm_num)
    have h1 : (4/9) * (knotA n b)^(-4/3:ℝ) ≤ (4/9) * 1 :=
      mul_le_mul_of_nonneg_left hAle (by norm_num)
    have h2 := mul_le_mul h1 hsum hInt_nonneg (by norm_num : (0:ℝ) ≤ (4/9)*1)
    rw [show (4/9) * 1 * (6*(↑n:ℝ)) = (8/3) * n by ring] at h2
    exact h2
  have hcongr : (fun t => (deriv (FK n hn b) t)^2)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun t => (gK n hn b t)^2) := by
    change ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1), (deriv (FK n hn b) t)^2 = (gK n hn b t)^2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [FK_deriv_ae hn hb0 hbmono hbtop] with t ht hmem
    rw [ht hmem]
  have hEq : ∫ t in (0:ℝ)..1, (deriv (FK n hn b) t)^2 = ∫ t in (0:ℝ)..1, (gK n hn b t)^2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact MeasureTheory.integral_congr_ae hcongr
  rw [hEq]
  exact hmono.trans hkey

lemma intervalIntegrable_deriv_FK {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2) :
    IntervalIntegrable (fun t => (deriv (FK n hn b) t)^2) volume 0 1 := by
  refine (intervalIntegrable_gK_sq hn hbmono hbtop).congr_ae ?_
  rw [show uIoc (0:ℝ) 1 = Ioc (0:ℝ) 1 from uIoc_of_le (by norm_num)]
  change (fun t => (gK n hn b t)^2) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
    (fun t => (deriv (FK n hn b) t)^2)
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [FK_deriv_ae hn hb0 hbmono hbtop] with t ht hmem
  rw [ht hmem]

/-- Auxiliary construction: given knots `b 0 < b 1 < ... < b (n-1)` with `b 0 = 0`,
`b (n-1) ≤ 1/2`, and a target constant `0 < c ≤ 1/2`, there is a monotone absolutely
continuous `F : ℝ → ℝ` with `F 0 = 0`, `F 1 = 1`, image in `[0,1]`, singularities of order `2/3`
at the times `knotTime n b j` with values `b j`, and `∫ (F')² ≤ (8/3) * n`. -/
theorem knots_parametrisation {n : ℕ} (hn : 0 < n) {b : ℕ → ℝ} (hb0 : b 0 = 0)
    (hbmono : ∀ j, j + 1 < n → b j < b (j+1)) (hbtop : b (n-1) ≤ 1/2)
    {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1/2) :
    (∀ j, j < n → knotTime n b j ∈ Icc (0:ℝ) 1) ∧
    (∀ i j, i < j → j < n → knotTime n b i < knotTime n b j) ∧
    FK n hn b 0 = 0 ∧ FK n hn b 1 = 1 ∧
    (∀ t, t ∈ Icc (0:ℝ) 1 → FK n hn b t ∈ Icc (0:ℝ) 1) ∧
    MonotoneOn (FK n hn b) (Icc (0:ℝ) 1) ∧
    AbsolutelyContinuousOnInterval (FK n hn b) 0 1 ∧
    IntervalIntegrable (fun t => (deriv (FK n hn b) t)^2) volume 0 1 ∧
    (∀ j, j < n → ∀ t, t ∈ Icc (0:ℝ) 1 →
      c * |t - knotTime n b j| ^ (2/3:ℝ) ≤ |FK n hn b t - b j|) ∧
    (∀ j, j < n → FK n hn b (knotTime n b j) = b j) ∧
    (∫ t in (0:ℝ)..1, (deriv (FK n hn b) t)^2 ≤ (8/3) * n) := by
  have hAc : c ≤ (knotA n b)^(-2/3:ℝ) := by
    simpa only [neg_div] using knotA_rpow_ge_c hn hb0 hbmono hbtop hc0 hc
  refine ⟨fun j hj => knotTime_mem_Icc hn hb0 hbmono hbtop hj,
    fun i j hij hj => knotTime_lt hn hbmono hbtop i j hij hj,
    FK_zero hn b, FK_one hn hb0 hbmono hbtop,
    fun t ht => FK_image hn hb0 hbmono hbtop ht,
    FK_mono hn hb0 hbmono hbtop, FK_AC hn hbmono hbtop,
    intervalIntegrable_deriv_FK hn hb0 hbmono hbtop, ?_, ?_,
    FK_energy hn hb0 hbmono hbtop⟩
  · intro j hj t ht
    have htj : knotTime n b j ∈ Icc (0:ℝ) 1 := knotTime_mem_Icc hn hb0 hbmono hbtop hj
    have hbj : FK n hn b (knotTime n b j) = b j :=
      FK_knotTime hn hb0 hbmono hbtop (by omega : j ≤ n-1)
    rcases le_total (knotTime n b j) t with hle | hle
    · have hmono := FK_mono hn hb0 hbmono hbtop htj ht hle
      rw [hbj] at hmono
      have hR : (knotA n b)^(-2/3:ℝ)*(t-knotTime n b j)^(2/3:ℝ) ≤ FK n hn b t - b j :=
        FK_cusp_right hn hb0 hbmono hbtop hj ⟨hle, ht.2⟩
      have habs : |FK n hn b t - b j| = FK n hn b t - b j :=
        abs_of_nonneg (sub_nonneg.mpr hmono)
      rw [habs, abs_of_nonneg (sub_nonneg.mpr hle)]
      calc c * (t - knotTime n b j)^(2/3:ℝ)
          ≤ (knotA n b)^(-2/3:ℝ) * (t - knotTime n b j)^(2/3:ℝ) :=
            mul_le_mul_of_nonneg_right hAc (Real.rpow_nonneg (sub_nonneg.mpr hle) _)
        _ ≤ FK n hn b t - b j := hR
    · have hmono := FK_mono hn hb0 hbmono hbtop ht htj hle
      rw [hbj] at hmono
      have hL : (knotA n b)^(-2/3:ℝ)*(knotTime n b j - t)^(2/3:ℝ) ≤ b j - FK n hn b t :=
        FK_cusp_left hn hb0 hbmono hbtop hj ⟨ht.1, hle⟩
      have habs : |FK n hn b t - b j| = b j - FK n hn b t := by
        rw [abs_of_nonpos (sub_nonpos.mpr hmono)]; ring
      rw [habs, abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
      calc c * (knotTime n b j - t)^(2/3:ℝ)
          ≤ (knotA n b)^(-2/3:ℝ) * (knotTime n b j - t)^(2/3:ℝ) :=
            mul_le_mul_of_nonneg_right hAc (Real.rpow_nonneg (sub_nonneg.mpr hle) _)
        _ ≤ b j - FK n hn b t := hL
  · intro j hj
    exact FK_knotTime hn hb0 hbmono hbtop (by omega : j ≤ n-1)

theorem exists_holder_parametrisation (m : ℕ) (hm : 0 < m) (a : Fin m → ℝ)
    (ha : ∀ i : Fin m, |a i| ≤ 1 / 2) :
    ∃ b : Fin m → ℝ, ∃ F : ℝ → ℝ,
      F 0 = 0 ∧ F 1 = 1 ∧
        (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → F t ∈ Set.Icc (0 : ℝ) 1) ∧
        MonotoneOn F (Set.Icc (0 : ℝ) 1) ∧
        AbsolutelyContinuousOnInterval F 0 1 ∧
        IntervalIntegrable (fun t : ℝ => (deriv F t) ^ 2) MeasureTheory.volume 0 1 ∧
        (∀ (i : Fin m) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
          (2 * (m : ℝ))⁻¹ * (|t - b i|) ^ (2 / 3 : ℝ) ≤ |F t - a i|) ∧
        ∫ t in (0 : ℝ)..1, (deriv F t) ^ 2 ≤ 6 * (m : ℝ) := by
  classical
  set S : Finset ℝ := insert 0 ((Finset.univ.image a).filter (fun x => 0 ≤ x)) with hSdef
  have hSne : S.Nonempty := ⟨0, by rw [hSdef]; exact Finset.mem_insert_self 0 _⟩
  have hnpos : 0 < S.card := Finset.card_pos.mpr hSne
  let β : ℕ → ℝ := fun j => if h : j < S.card then (S.orderEmbOfFin rfl ⟨j, h⟩ : ℝ) else 0
  have hβmem : ∀ j (h : j < S.card), β j = (S.orderEmbOfFin rfl ⟨j, h⟩ : ℝ) :=
    fun j h => dif_pos h
  have hex : ∀ i : Fin m, 0 ≤ a i → ∃ j, j < S.card ∧ β j = a i := by
    intro i h
    have hmem : a i ∈ ↑S := by
      rw [hSdef]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, h⟩))
    have hx' : a i ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
      rwa [Finset.range_orderEmbOfFin]
    obtain ⟨i', hi'⟩ := hx'
    exact ⟨i'.val, i'.isLt, by rw [hβmem i'.val i'.isLt]; exact hi'⟩
  have hβ0 : β 0 = 0 := by
    rw [hβmem 0 hnpos, Finset.orderEmbOfFin_zero (s := S) (k := S.card) rfl hnpos]
    apply le_antisymm
    · exact Finset.min'_le (s := S) 0 (by rw [hSdef]; exact Finset.mem_insert_self 0 _)
    · rw [Finset.le_min'_iff]
      intro x hx
      rw [hSdef] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (Finset.mem_filter.mp hx).2
  have hβmono : ∀ j, j + 1 < S.card → β j < β (j+1) := by
    intro j hj
    rw [hβmem j (by omega), hβmem (j+1) hj]
    exact (S.orderEmbOfFin rfl).strictMono (by simp [Fin.lt_def])
  have hβtop : β (S.card - 1) ≤ 1/2 := by
    rw [hβmem (S.card - 1) (by omega),
      Finset.orderEmbOfFin_last (s := S) (k := S.card) rfl hnpos,
      Finset.max'_le_iff]
    intro x hx
    rw [hSdef] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨hxmem, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxmem
      have := (abs_le.mp (ha i)).2
      linarith
  have hc0 : 0 < (2 * (m:ℝ))⁻¹ := by positivity
  have hcle : (2 * (m:ℝ))⁻¹ ≤ 1/2 := by
    rw [show (1/2:ℝ) = 2⁻¹ by norm_num]
    refine (inv_le_inv₀ (by positivity : (0:ℝ) < 2*(m:ℝ)) (by norm_num : (0:ℝ) < 2)).mpr ?_
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  obtain ⟨-, -, hF0, hF1, hFim, hFmono, hFAC, hFint, hcusp, hFval, henergy⟩ :=
    knots_parametrisation hnpos hβ0 hβmono hβtop hc0 hcle
  refine ⟨fun i => if h : 0 ≤ a i then knotTime S.card β (Classical.choose (hex i h)) else 0,
    FK S.card hnpos β, hF0, hF1, hFim, hFmono, hFAC, hFint, ?_, ?_⟩
  · intro i t ht
    by_cases h : 0 ≤ a i
    · have hspec : β (Classical.choose (hex i h)) = a i := (Classical.choose_spec (hex i h)).2
      have hch : Classical.choose (hex i h) < S.card := (Classical.choose_spec (hex i h)).1
      have hc := hcusp (Classical.choose (hex i h)) hch t ht
      rw [hspec] at hc
      simpa only [dif_pos h] using hc
    · push_neg at h
      have hc := hcusp 0 hnpos t ht
      rw [hβ0, knotTime_zero] at hc
      have hFt : 0 ≤ FK S.card hnpos β t := (hFim t ht).1
      have hai : a i < 0 := h
      rw [show (fun i => if h : 0 ≤ a i then knotTime S.card β (Classical.choose (hex i h)) else 0) i = 0 from dif_neg (not_le.mpr h), sub_zero]
      have hc' : (2 * (m:ℝ))⁻¹ * |t| ^ (2/3:ℝ) ≤ FK S.card hnpos β t := by
        simpa only [sub_zero, abs_of_nonneg hFt] using hc
      have hgt : FK S.card hnpos β t ≤ |FK S.card hnpos β t - a i| := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ FK S.card hnpos β t - a i)]
        linarith
      linarith [hc', hgt]
  · have hcard : S.card ≤ m + 1 := by
      have h3 : (Finset.univ.image a).card ≤ m := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := a))
      have h1 := Finset.card_insert_le (0:ℝ) ((Finset.univ.image a).filter (fun x => 0 ≤ x))
      have h2 := Finset.card_filter_le ((Finset.univ.image a)) (fun x => 0 ≤ x)
      rw [hSdef]; omega
    have hcard' : (S.card : ℝ) ≤ (m:ℝ) + 1 := by exact_mod_cast hcard
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hbound : (8/3) * (S.card : ℝ) ≤ 6 * (m:ℝ) := by nlinarith [hcard', hm1]
    exact henergy.trans hbound

end
end Commons.Analysis.Calculus