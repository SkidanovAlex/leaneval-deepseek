import Mathlib
import Submission.Work.FIArea4.logSine_defs

namespace Work.FIArea4

open scoped Topology

noncomputable section

lemma hasDerivAt_log_two_mul (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log (2 * z)) (1 / y) y := by
  have h : HasDerivAt (fun z : ℝ => Real.log (2 * z)) ((2 * y)⁻¹ * 2) y := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log (x := 2 * y) (mul_ne_zero two_ne_zero hy)).comp y
        (hasDerivAt_const_mul (x := y) (2 : ℝ))
  have hv : (2 * y)⁻¹ * 2 = 1 / y := by field_simp
  rwa [hv] at h

lemma hasDerivAt_half_log (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ => (1 / 2) * Real.log (2 * z)) (1 / (2 * y)) y := by
  have h := (hasDerivAt_log_two_mul y hy).const_mul (1 / 2)
  have hv : (1 / 2) * (1 / y) = 1 / (2 * y) := by field_simp
  rwa [hv] at h

lemma hasDerivAt_one_div_two_mul (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ => 1 / (2 * z)) (-(1 / (2 * y ^ 2))) y := by
  have hnum : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have hden : HasDerivAt (fun z : ℝ => 2 * z) 2 y := hasDerivAt_const_mul (x := y) (2 : ℝ)
  have h := hnum.div hden (by simpa using mul_ne_zero two_ne_zero hy)
  have hv : (0 * (2 * y) - 1 * 2) / (2 * y) ^ 2 = -(1 / (2 * y ^ 2)) := by
    field_simp
    try ring
  rwa [hv] at h

lemma hasDerivAt_transition (N : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1))
      (deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)) y := by
  have hτ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1)) (2 * (N : ℝ) ^ 2 * y - 1) :=
    (by fun_prop : DifferentiableAt ℝ Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1)).hasDerivAt
  have hφ : HasDerivAt (fun z : ℝ => 2 * (N : ℝ) ^ 2 * z - 1) (2 * (N : ℝ) ^ 2) y :=
    (hasDerivAt_const_mul (x := y) (2 * (N : ℝ) ^ 2)).sub_const 1
  simpa [Function.comp_def] using hτ.comp y hφ

lemma hasDerivAt_Psi (N : ℕ) (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (Psi N)
      ((N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * Real.log (2 * y)
        + (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y) y := by
  have hτ := hasDerivAt_transition N y
  have hlog := hasDerivAt_log_two_mul y hy
  have h1 : HasDerivAt (fun z : ℝ => (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1))
      ((1 / 2) * (deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)))
      y := hτ.const_mul (1 / 2)
  have h2 := h1.mul hlog
  have hv : ((1 / 2) * (deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)))
        * Real.log (2 * y)
        + ((1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1)) * (1 / y)
      = (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * Real.log (2 * y)
        + (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y := by
    field_simp
    try ring
  unfold Psi
  rwa [hv] at h2

lemma hasDerivAt_transition_deriv (N : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1))
      (deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)) y := by
  have hτ : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1))
      (2 * (N : ℝ) ^ 2 * y - 1) :=
    (by fun_prop : DifferentiableAt ℝ (deriv Real.smoothTransition)
      (2 * (N : ℝ) ^ 2 * y - 1)).hasDerivAt
  have hφ : HasDerivAt (fun z : ℝ => 2 * (N : ℝ) ^ 2 * z - 1) (2 * (N : ℝ) ^ 2) y :=
    (hasDerivAt_const_mul (x := y) (2 * (N : ℝ) ^ 2)).sub_const 1
  simpa [Function.comp_def] using hτ.comp y hφ

/-- Second derivative of `Ψ_N` on `y ≠ 0`, as a `HasDerivAt` statement for the first derivative. -/
lemma hasDerivAt_deriv_Psi (N : ℕ) (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z : ℝ =>
        (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1) * Real.log (2 * z)
        + (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1) / z)
      (2 * (N : ℝ) ^ 4 * deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1)
          * Real.log (2 * y)
        + 2 * (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y
        - (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y ^ 2) y := by
  have hA := (hasDerivAt_transition_deriv N y).const_mul ((N : ℝ) ^ 2)
  have hlog := hasDerivAt_log_two_mul y hy
  have hAB := hA.mul hlog
  have hnum := (hasDerivAt_transition N y).const_mul (1 / 2)
  have hden : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
  have hC := hnum.div hden (by simpa using hy)
  have hsum := hAB.add hC
  have hv : ((N : ℝ) ^ 2
          * (deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)))
        * Real.log (2 * y)
        + ((N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1)) * (1 / y)
        + (((1 / 2) * (deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * (2 * (N : ℝ) ^ 2)))
            * y - ((1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1)) * 1) / y ^ 2
      = 2 * (N : ℝ) ^ 4 * deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1)
          * Real.log (2 * y)
        + 2 * (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y
        - (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y ^ 2 := by
    field_simp
    try ring
  rwa [hv] at hsum

lemma deriv_Psi (N : ℕ) {y : ℝ} (hy : 0 < y) :
    deriv (Psi N) y
      = (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) * Real.log (2 * y)
        + (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y :=
  (hasDerivAt_Psi N y (ne_of_gt hy)).deriv

lemma deriv_deriv_Psi (N : ℕ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (Psi N)) y
      = 2 * (N : ℝ) ^ 4 * deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1)
          * Real.log (2 * y)
        + 2 * (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y
        - (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) / y ^ 2 := by
  have hge : deriv (Psi N) =ᶠ[𝓝 y] (fun z : ℝ =>
      (N : ℝ) ^ 2 * deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1) * Real.log (2 * z)
      + (1 / 2) * Real.smoothTransition (2 * (N : ℝ) ^ 2 * z - 1) / z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact deriv_Psi N hz
  rw [Filter.EventuallyEq.deriv_eq hge]
  exact (hasDerivAt_deriv_Psi N y (ne_of_gt hy)).deriv

/-! ### The regions `y ≤ 1/(2N²)` and `y ≥ 1/N²` -/

lemma Psi_eventuallyEq_log (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : 1 / (N : ℝ) ^ 2 < y) :
    Psi N =ᶠ[𝓝 y] fun z => (1 / 2) * Real.log (2 * z) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hset : Set.Ioi (1 / (N : ℝ) ^ 2) ∈ 𝓝 y := isOpen_Ioi.mem_nhds hy
  filter_upwards [hset] with z hz
  have hz' : (1 : ℝ) ≤ 2 * (N : ℝ) ^ 2 * z - 1 := by
    have h1 : (1 : ℝ) < (N : ℝ) ^ 2 * z := by
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) := by field_simp
        _ < (N : ℝ) ^ 2 * z := mul_lt_mul_of_pos_left hz hB
    linarith
  rw [Psi, phi_one_of_one_le hz', mul_one]

lemma Psi_eventuallyEq_zero (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : y < 1 / (2 * (N : ℝ) ^ 2)) :
    Psi N =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hset : Set.Iio (1 / (2 * (N : ℝ) ^ 2)) ∈ 𝓝 y := isOpen_Iio.mem_nhds hy
  filter_upwards [hset] with z hz
  have hz' : 2 * (N : ℝ) ^ 2 * z - 1 ≤ 0 := by
    have h1 : 2 * (N : ℝ) ^ 2 * z < 1 := by
      calc 2 * (N : ℝ) ^ 2 * z < 2 * (N : ℝ) ^ 2 * (1 / (2 * (N : ℝ) ^ 2)) :=
            mul_lt_mul_of_pos_left hz h2B
        _ = 1 := by field_simp
    linarith
  exact Psi_eq_zero hz'

/-- Off the transition window, above it: `Ψ_N` behaves like `(1/2) log (2y)`. -/
lemma deriv_Psi_of_gt (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : 1 / (N : ℝ) ^ 2 < y) :
    deriv (Psi N) y = 1 / (2 * y) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos hB) hy.le
  rw [Filter.EventuallyEq.deriv_eq (Psi_eventuallyEq_log N hN hy)]
  exact (hasDerivAt_half_log y (ne_of_gt hypos)).deriv

lemma deriv_deriv_Psi_of_gt (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : 1 / (N : ℝ) ^ 2 < y) :
    deriv (deriv (Psi N)) y = -(1 / (2 * y ^ 2)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos hB) hy.le
  have hge : deriv (Psi N) =ᶠ[𝓝 y] fun z => 1 / (2 * z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact deriv_Psi_of_gt N hN hz
  rw [Filter.EventuallyEq.deriv_eq hge]
  exact (hasDerivAt_one_div_two_mul y (ne_of_gt hypos)).deriv

/-- Off the transition window, below it: `Ψ_N` vanishes identically near `y`. -/
lemma deriv_Psi_of_lt (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : y < 1 / (2 * (N : ℝ) ^ 2)) :
    deriv (Psi N) y = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (Psi_eventuallyEq_zero N hN hy)]
  exact deriv_const y 0

lemma deriv_deriv_Psi_of_lt (N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : y < 1 / (2 * (N : ℝ) ^ 2)) :
    deriv (deriv (Psi N)) y = 0 := by
  have h1 := Psi_eventuallyEq_zero N hN hy
  have h2 : deriv (Psi N) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    have h3 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := funext fun z => deriv_const z 0
    simpa [h3] using Filter.EventuallyEq.deriv h1
  rw [Filter.EventuallyEq.deriv_eq h2]
  exact deriv_const y 0

/-! ### Bounds inside the window -/

lemma one_div_le_of_window (N : ℕ) (hN : 1 ≤ N) {y : ℝ}
    (h1 : 1 / (2 * (N : ℝ) ^ 2) ≤ y) : 1 / y ≤ 2 * (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos h2B) h1
  rw [div_le_iff₀ hypos]
  have h := (div_le_iff₀ h2B).mp h1
  nlinarith [h]

lemma one_div_sq_le_of_window (N : ℕ) (hN : 1 ≤ N) {y : ℝ}
    (h1 : 1 / (2 * (N : ℝ) ^ 2) ≤ y) : 1 / y ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
  have hle := one_div_le_of_window N hN h1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos h2B) h1
  have hyinv : 0 ≤ 1 / y := le_of_lt (div_pos one_pos hypos)
  have hsq : (1 / y) ^ 2 ≤ (2 * (N : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hyinv hle 2
  calc 1 / y ^ 2 = (1 / y) ^ 2 := by rw [div_pow, one_pow]
    _ ≤ (2 * (N : ℝ) ^ 2) ^ 2 := hsq
    _ = 4 * (N : ℝ) ^ 4 := by ring

lemma abs_log_two_mul_le_of_window (N : ℕ) (hN : 2 ≤ N) {y : ℝ}
    (h1 : 1 / (2 * (N : ℝ) ^ 2) ≤ y) (h2 : y ≤ 2 / (N : ℝ) ^ 2) :
    |Real.log (2 * y)| ≤ 2 * Real.log N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos h2B) h1
  have h2ypos : 0 < 2 * y := by linarith
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hup : 2 * y ≤ 1 := by
    have h2y : 2 * y ≤ 4 / (N : ℝ) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * y ≤ 2 * (2 / (N : ℝ) ^ 2) := hm
        _ = 4 / (N : ℝ) ^ 2 := by ring
    have h4 : 4 / (N : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one hB]; exact hN2
    linarith
  have hdown : 1 / (N : ℝ) ^ 2 ≤ 2 * y := by
    rw [div_le_iff₀ hB]
    have h := (div_le_iff₀ h2B).mp h1
    nlinarith [h]
  have hlogup : Real.log (2 * y) ≤ 0 := by
    have h := Real.log_le_log h2ypos hup
    rwa [Real.log_one] at h
  have hlogdown : -(2 * Real.log N) ≤ Real.log (2 * y) := by
    have h := Real.log_le_log (div_pos one_pos hB) hdown
    have hlogN2 : Real.log (1 / (N : ℝ) ^ 2) = -(2 * Real.log N) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    linarith [h, hlogN2]
  rw [abs_of_nonpos hlogup]
  linarith

lemma abs_deriv_Psi_le_of_window (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K) {y : ℝ}
    (h1 : 1 / (2 * (N : ℝ) ^ 2) ≤ y) (h2 : y ≤ 2 / (N : ℝ) ^ 2) :
    |deriv (Psi N) y| ≤ 4 * K * (N : ℝ) ^ 2 * (Real.log N + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos h2B) h1
  rw [deriv_Psi N hypos]
  set dτ := deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) with hdτ
  set t := Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) with ht
  have hd : |dτ| ≤ K := by rw [hdτ]; exact hK1 _
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.smoothTransition.nonneg _
  have ht1 : t ≤ 1 := by rw [ht]; exact Real.smoothTransition.le_one _
  have hlog : |Real.log (2 * y)| ≤ 2 * Real.log N := abs_log_two_mul_le_of_window N hN h1 h2
  have h1y : 1 / y ≤ 2 * (N : ℝ) ^ 2 := one_div_le_of_window N hN1 h1
  have hK0 : 0 ≤ K := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hterm1 : |(N : ℝ) ^ 2 * dτ * Real.log (2 * y)| ≤ (N : ℝ) ^ 2 * K * (2 * Real.log N) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hB)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hd (le_of_lt hB)) hlog (abs_nonneg _)
      (mul_nonneg (le_of_lt hB) hK0)
  have hterm2 : |(1 / 2) * t / y| ≤ (N : ℝ) ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg ht0,
      abs_of_pos hypos]
    have hA : (1 / 2) * t ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left ht1 (by norm_num)
    have hres := mul_le_mul hA h1y (le_of_lt (div_pos one_pos hypos))
        (by norm_num : (0 : ℝ) ≤ (1 / 2) * 1)
    calc (1 / 2) * t / y = (1 / 2) * t * (1 / y) := by ring
      _ ≤ (1 / 2) * 1 * (2 * (N : ℝ) ^ 2) := hres
      _ = (N : ℝ) ^ 2 := by ring
  calc |(N : ℝ) ^ 2 * dτ * Real.log (2 * y) + (1 / 2) * t / y|
      ≤ |(N : ℝ) ^ 2 * dτ * Real.log (2 * y)| + |(1 / 2) * t / y| := abs_add_le _ _
    _ ≤ (N : ℝ) ^ 2 * K * (2 * Real.log N) + (N : ℝ) ^ 2 := add_le_add hterm1 hterm2
    _ ≤ 4 * K * (N : ℝ) ^ 2 * (Real.log N + 1) := by
      have hKN : 0 ≤ K * (N : ℝ) ^ 2 := mul_nonneg hK0 (le_of_lt hB)
      have h1 : 0 ≤ K * (N : ℝ) ^ 2 * Real.log N := mul_nonneg hKN hlogN
      have hKN' : (N : ℝ) ^ 2 ≤ K * (N : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hK (le_of_lt hB)
        simpa using h
      linarith

lemma abs_deriv_deriv_Psi_le_of_window (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) {y : ℝ}
    (h1 : 1 / (2 * (N : ℝ) ^ 2) ≤ y) (h2 : y ≤ 2 / (N : ℝ) ^ 2) :
    |deriv (deriv (Psi N)) y| ≤ 8 * K * (N : ℝ) ^ 4 * (Real.log N + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h2B : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le (div_pos one_pos h2B) h1
  rw [deriv_deriv_Psi N hypos]
  set d2 := deriv (deriv Real.smoothTransition) (2 * (N : ℝ) ^ 2 * y - 1) with hd2
  set dτ := deriv Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) with hdτ
  set t := Real.smoothTransition (2 * (N : ℝ) ^ 2 * y - 1) with ht
  have hd2b : |d2| ≤ K := by rw [hd2]; exact hK2 _
  have hdb : |dτ| ≤ K := by rw [hdτ]; exact hK1 _
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.smoothTransition.nonneg _
  have ht1 : t ≤ 1 := by rw [ht]; exact Real.smoothTransition.le_one _
  have hlog : |Real.log (2 * y)| ≤ 2 * Real.log N := abs_log_two_mul_le_of_window N hN h1 h2
  have h1y : 1 / y ≤ 2 * (N : ℝ) ^ 2 := one_div_le_of_window N hN1 h1
  have h1y2 : 1 / y ^ 2 ≤ 4 * (N : ℝ) ^ 4 := one_div_sq_le_of_window N hN1 h1
  have hK0 : 0 ≤ K := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hterm1 : |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y)|
      ≤ 2 * (N : ℝ) ^ 4 * K * (2 * Real.log N) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 4)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hd2b (by positivity)) hlog (abs_nonneg _)
      (by positivity)
  have hterm2 : |2 * (N : ℝ) ^ 2 * dτ / y| ≤ 2 * (N : ℝ) ^ 2 * K * (2 * (N : ℝ) ^ 2) := by
    have hA : 2 * (N : ℝ) ^ 2 * |dτ| ≤ 2 * (N : ℝ) ^ 2 * K :=
      mul_le_mul_of_nonneg_left hdb (by positivity)
    have hres := mul_le_mul hA h1y (le_of_lt (div_pos one_pos hypos)) (by positivity)
    calc |2 * (N : ℝ) ^ 2 * dτ / y| = 2 * (N : ℝ) ^ 2 * |dτ| * (1 / y) := by
          rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2),
            abs_of_pos hypos]
          ring
      _ ≤ (2 * (N : ℝ) ^ 2 * K) * (2 * (N : ℝ) ^ 2) := hres
      _ = 2 * (N : ℝ) ^ 2 * K * (2 * (N : ℝ) ^ 2) := by ring
  have hterm3 : |(1 / 2) * t / y ^ 2| ≤ 2 * (N : ℝ) ^ 4 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg ht0,
      abs_of_pos (by positivity : (0 : ℝ) < y ^ 2)]
    have hA : (1 / 2) * t ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left ht1 (by norm_num)
    have hres := mul_le_mul hA h1y2 (by positivity : (0 : ℝ) ≤ 1 / y ^ 2)
        (by norm_num : (0 : ℝ) ≤ (1 / 2) * 1)
    calc (1 / 2) * t / y ^ 2 = (1 / 2) * t * (1 / y ^ 2) := by ring
      _ ≤ (1 / 2) * 1 * (4 * (N : ℝ) ^ 4) := hres
      _ = 2 * (N : ℝ) ^ 4 := by ring
  have hsplit1 : |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y) + 2 * (N : ℝ) ^ 2 * dτ / y
      - (1 / 2) * t / y ^ 2|
      ≤ |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y) + 2 * (N : ℝ) ^ 2 * dτ / y|
        + |(1 / 2) * t / y ^ 2| := by
    have h := abs_add_le (2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y) + 2 * (N : ℝ) ^ 2 * dτ / y)
      (-((1 / 2) * t / y ^ 2))
    simpa [sub_eq_add_neg, abs_neg] using h
  have hsplit2 : |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y) + 2 * (N : ℝ) ^ 2 * dτ / y|
      ≤ |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y)| + |2 * (N : ℝ) ^ 2 * dτ / y| :=
    abs_add_le _ _
  calc |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y) + 2 * (N : ℝ) ^ 2 * dτ / y
        - (1 / 2) * t / y ^ 2|
      ≤ |2 * (N : ℝ) ^ 4 * d2 * Real.log (2 * y)| + |2 * (N : ℝ) ^ 2 * dτ / y|
        + |(1 / 2) * t / y ^ 2| := by linarith [hsplit1, hsplit2]
    _ ≤ 2 * (N : ℝ) ^ 4 * K * (2 * Real.log N) + 2 * (N : ℝ) ^ 2 * K * (2 * (N : ℝ) ^ 2)
        + 2 * (N : ℝ) ^ 4 := by linarith [hterm1, hterm2, hterm3]
    _ ≤ 8 * K * (N : ℝ) ^ 4 * (Real.log N + 1) := by
      have hN4 : 0 < (N : ℝ) ^ 4 := by positivity
      have hKN4 : 0 ≤ K * (N : ℝ) ^ 4 := mul_nonneg hK0 (le_of_lt hN4)
      have h1 : 0 ≤ K * (N : ℝ) ^ 4 * Real.log N := mul_nonneg hKN4 hlogN
      have hKN4' : (N : ℝ) ^ 4 ≤ K * (N : ℝ) ^ 4 := by
        have h := mul_le_mul_of_nonneg_right hK (le_of_lt hN4)
        simpa using h
      linarith



/-- Analytic control of `Ψ_N(y) = (1/2)·τ(2 N² y − 1)·log(2y)` (`Work.FIArea4.Psi`), where
`τ = Real.smoothTransition` and `K` bounds `|τ'|`, `|τ''|` (see `Work.FIArea4.logSine_tau_bound`):
exact values off the transition window `[1/(2N²), 2/N²]`, and bounds inside it.

Hints: for `y ≥ 2/N²` the argument `2N²y - 1 ≥ 3 > 1` on a neighbourhood, so `τ ≡ 1` there and
`Psi N = (1/2) log(2y)` locally — differentiate.  For `y < 1/(2N²)` the argument is `< 0` on a
neighbourhood, so `Psi N ≡ 0` locally.  Inside the window use the product rule
`deriv (Psi N) y = N²·τ'(2N²y-1)·log(2y) + (1/2)·τ(2N²y-1)/y` and
`deriv (deriv (Psi N)) y = 2N⁴·τ''(2N²y-1)·log(2y) + 2N²·τ'(2N²y-1)/y - (1/2)·τ(2N²y-1)/y²`
(valid for `y > 0`), plus `|log (2y)| ≤ 2 log N`, `1/y ≤ 2N²`, `1/y² ≤ 4N⁴`, `K ≥ 1`. -/
theorem logSine_psi_deriv (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) :
    (∀ y : ℝ, 2 / (N:ℝ)^2 ≤ y → deriv (Psi N) y = 1/(2*y)) ∧
    (∀ y : ℝ, 2 / (N:ℝ)^2 ≤ y → deriv (deriv (Psi N)) y = -(1/(2*y^2))) ∧
    (∀ y : ℝ, y < 1/(2*(N:ℝ)^2) → deriv (Psi N) y = 0) ∧
    (∀ y : ℝ, y < 1/(2*(N:ℝ)^2) → deriv (deriv (Psi N)) y = 0) ∧
    (∀ y : ℝ, 1/(2*(N:ℝ)^2) ≤ y → y ≤ 2/(N:ℝ)^2 →
        |deriv (Psi N) y| ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) ∧
        |deriv (deriv (Psi N)) y| ≤ 8 * K * (N:ℝ)^4 * (Real.log N + 1)) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hB : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hlt : 1 / (N : ℝ) ^ 2 < 2 / (N : ℝ) ^ 2 := by
    have h2eq : 2 / (N : ℝ) ^ 2 = 2 * (1 / (N : ℝ) ^ 2) := by ring
    have hpos : 0 < 1 / (N : ℝ) ^ 2 := div_pos one_pos hB
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact deriv_Psi_of_gt N hN1 (lt_of_lt_of_le hlt hy)
  · intro y hy
    exact deriv_deriv_Psi_of_gt N hN1 (lt_of_lt_of_le hlt hy)
  · intro y hy
    exact deriv_Psi_of_lt N hN1 hy
  · intro y hy
    exact deriv_deriv_Psi_of_lt N hN1 hy
  · intro y h1 h2
    exact ⟨abs_deriv_Psi_le_of_window N hN K hK hK1 h1 h2,
      abs_deriv_deriv_Psi_le_of_window N hN K hK hK1 hK2 h1 h2⟩

end
end Work.FIArea4
