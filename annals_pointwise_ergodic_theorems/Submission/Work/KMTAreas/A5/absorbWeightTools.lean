/-
# Tools for the absorption lemma `absorbWeight`

Two groups of elementary lemmas used by `Work.KMTAreas.A5.absorbWeightStrict`:

* comparisons between the integer scales `logN N = ⌊log₂ max(N,2)⌋`, `logLogN N` and the real
  logarithms `Real.logb 2 N`;
* the two real-variable estimates
  `(A + B)^s ≤ 2^s (A^s + B^s)` (`s ≥ 0`) and `m^{-a} ≤ 2^a M^{-a}` when `M ≤ 2 m`
  (`a > 0`), plus the coercion bridge `ennrealRpowLift` lifting a real inequality of
  nonnegative reals to `ℝ≥0∞`.
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Setup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar
open Work.Analysis.IWMultiplier

/-! ## Scale comparisons -/

lemma sc_logN_ge_one {N : ℕ} (_hN : 1 ≤ N) : (1 : ℝ) ≤ ((logN N : ℤ) : ℝ) := by
  rw [show logN N = (Nat.log 2 (max N 2) : ℤ) from rfl]
  push_cast
  have h : 1 ≤ Nat.log 2 (max N 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ max N 2)
  exact_mod_cast h

lemma sc_logN_le_logb {N : ℕ} (hN : 2 ≤ N) :
    ((logN N : ℤ) : ℝ) ≤ Real.logb 2 (N : ℝ) := by
  have hm : logN N = (Nat.log 2 N : ℤ) := by
    simp only [logN, max_eq_left (show (2 : ℕ) ≤ N by omega)]
  rw [hm]
  push_cast
  have h2m : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hx : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N) := by positivity
  have hy : (0 : ℝ) < (N : ℝ) := by positivity
  have h := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) hx hy).mpr h2m
  rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one] at h
  linarith

lemma sc_logb_le_one_add_logN {N : ℕ} (hN : 1 ≤ N) :
    Real.logb 2 (N : ℝ) ≤ 1 + ((logN N : ℤ) : ℝ) := by
  rcases eq_or_lt_of_le hN with h | h
  · subst h
    rw [show logN 1 = (Nat.log 2 (max 1 2) : ℤ) from rfl]
    norm_num
  · have h2m : ((logN N : ℤ) : ℝ) = ((Nat.log 2 N : ℕ) : ℝ) := by
      rw [show logN N = (Nat.log 2 (max N 2) : ℤ) from rfl,
        max_eq_left (by omega : (2 : ℕ) ≤ N)]
      push_cast; ring
    rw [h2m]
    have hlt : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      exact_mod_cast le_of_lt h
    have hx : (0 : ℝ) < (N : ℝ) := by positivity
    have hy : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1) := by positivity
    have h := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) hx hy).mpr hlt
    rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one] at h
    push_cast at h
    linarith

lemma sc_natlog_le_logb (m : ℕ) : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm; simp
  · have h2m : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hm
    have hx : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 m) := by positivity
    have hy : (0 : ℝ) < (m : ℝ) := by positivity
    have h := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) hx hy).mpr h2m
    rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one] at h
    linarith

lemma sc_logLogN_le {N : ℕ} (hN : 2 ≤ N) :
    (logLogN N : ℝ) ≤ 1 + Real.logb 2 (Real.logb 2 (N : ℝ)) := by
  have hmN : logN N = (Nat.log 2 N : ℤ) := by
    simp only [logN, max_eq_left (show (2 : ℕ) ≤ N by omega)]
  have hm1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have h1 : ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    have h := sc_logN_le_logb hN
    rw [hmN] at h; push_cast at h; exact h
  have hstep : Nat.log 2 (Nat.log 2 N + 2) ≤ 1 + Nat.log 2 (Nat.log 2 N) := by
    by_cases h : Nat.log 2 N ≤ 1
    · have he : Nat.log 2 N = 1 := le_antisymm h hm1
      rw [he]; norm_num
    · have hle : Nat.log 2 N + 2 ≤ 2 * Nat.log 2 N := by omega
      calc Nat.log 2 (Nat.log 2 N + 2) ≤ Nat.log 2 (2 * Nat.log 2 N) := Nat.log_mono_right hle
        _ = Nat.log 2 (Nat.log 2 N * 2) := by rw [Nat.mul_comm]
        _ = Nat.log 2 (Nat.log 2 N) + 1 := Nat.log_mul_base (by norm_num) (by omega)
        _ ≤ 1 + Nat.log 2 (Nat.log 2 N) := by omega
  have hlogLog : logLogN N = Nat.log 2 (Nat.log 2 N + 2) := by
    simp only [logLogN, max_eq_left (show (2 : ℕ) ≤ N by omega)]
  have hstepR : ((Nat.log 2 (Nat.log 2 N + 2) : ℕ) : ℝ)
      ≤ 1 + ((Nat.log 2 (Nat.log 2 N) : ℕ) : ℝ) := by exact_mod_cast hstep
  rw [hlogLog]
  have hB : ((Nat.log 2 (Nat.log 2 N) : ℕ) : ℝ) ≤ Real.logb 2 ((Nat.log 2 N : ℕ) : ℝ) :=
    sc_natlog_le_logb _
  have hC : Real.logb 2 ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    have hx : (0 : ℝ) < ((Nat.log 2 N : ℕ) : ℝ) := by exact_mod_cast hm1
    have hy : (0 : ℝ) < Real.logb 2 (N : ℝ) := by linarith
    exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hx hy).mpr h1
  linarith

/-- The height scale is bounded by `C₀ (1 + LogLog N)` in terms of `Log N = logb 2 N`. -/
lemma sc_heightScale_le {C₀ N : ℕ} (hN : 1 ≤ N) :
    ((heightScale C₀ N : ℕ) : ℝ)
      ≤ (C₀ : ℝ) * (1 + Real.logb 2 (max 1 (Real.logb 2 (N : ℝ)))) := by
  have hL : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
    simp only [heightScale]; push_cast; ring
  rw [hL]
  rcases eq_or_lt_of_le hN with h | h
  · subst h
    have h1 : logLogN 1 = 1 := by
      rw [show logLogN 1 = Nat.log 2 (Nat.log 2 (max 1 2) + 2) from rfl]
      norm_num
    rw [h1]
    norm_num
  · have h2 : max 1 (Real.logb 2 (N : ℝ)) = Real.logb 2 (N : ℝ) := by
      refine max_eq_right ?_
      have hlt : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
      have := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) (by norm_num : (0 : ℝ) < 2)
        (by positivity : (0 : ℝ) < (N : ℝ))).mpr hlt
      rwa [Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num)] at this
    rw [h2]
    have h := sc_logLogN_le (by omega : 2 ≤ N)
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (C₀ : ℝ))
    linarith

/-- `LogLog N` is controlled by the height scale: `logb 2 (Log N) ≤ 1 + heightScale C₀ N / C₀`. -/
lemma sc_logb_logN_le_heightScale {C₀ N : ℕ} (hC₀ : 1 ≤ C₀) (hN : 1 ≤ N) :
    Real.logb 2 (((logN N : ℤ) : ℝ)) ≤ 1 + ((heightScale C₀ N : ℕ) : ℝ) / (C₀ : ℝ) := by
  have hm_eq : ((logN N : ℤ) : ℝ) = ((Nat.log 2 (max N 2) : ℕ) : ℝ) := by
    rw [show logN N = (Nat.log 2 (max N 2) : ℤ) from rfl]; push_cast; ring
  have h1 : Real.logb 2 (((Nat.log 2 (max N 2) : ℕ) : ℝ)) ≤ 1 + ((logLogN N : ℕ) : ℝ) := by
    have hlt : (Nat.log 2 (max N 2) : ℕ) < 2 ^ (logLogN N + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 (max N 2) + 2)
      have hl : logLogN N = Nat.log 2 (Nat.log 2 (max N 2) + 2) := rfl
      rw [← hl, Nat.succ_eq_add_one] at h
      omega
    have hcast : (((Nat.log 2 (max N 2) : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ (logLogN N + 1)) := by
      have hthis : (((2 ^ (logLogN N + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (logLogN N + 1) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
      rw [← hthis]
      exact_mod_cast le_of_lt hlt
    have hx : 0 < (((Nat.log 2 (max N 2) : ℕ) : ℝ)) := by
      have := sc_logN_ge_one hN
      rw [hm_eq] at this
      linarith
    have hy : 0 < (2 : ℝ) ^ (logLogN N + 1) := by positivity
    have h := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) hx hy).mpr hcast
    rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one] at h
    push_cast at h
    linarith
  have hL : ((heightScale C₀ N : ℕ) : ℝ) / (C₀ : ℝ) = ((logLogN N : ℕ) : ℝ) := by
    have hC0pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀
    have hh : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
      simp only [heightScale]; push_cast; ring
    rw [hh]; field_simp
  rw [hm_eq]
  linarith

/-! ## Two real-variable estimates -/

/-- `(A+B)^s ≤ 2^s (A^s + B^s)` for `A, B ≥ 0`, `s ≥ 0`. -/
lemma add_rpow_le {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    (A + B) ^ s ≤ (2 : ℝ) ^ s * (A ^ s + B ^ s) := by
  have h1 : A + B ≤ 2 * max A B := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (2 * max A B) ^ s = (2 : ℝ) ^ s * (max A B) ^ s :=
    Real.mul_rpow (by norm_num) (le_max_of_le_left hA)
  have h3 : (max A B) ^ s ≤ A ^ s + B ^ s := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]
      have : (0 : ℝ) ≤ A ^ s := Real.rpow_nonneg hA s
      linarith
    · rw [max_eq_left h]
      have : (0 : ℝ) ≤ B ^ s := Real.rpow_nonneg hB s
      linarith
  calc (A + B) ^ s ≤ (2 * max A B) ^ s := Real.rpow_le_rpow (by linarith) h1 hs
    _ = (2 : ℝ) ^ s * (max A B) ^ s := h2
    _ ≤ (2 : ℝ) ^ s * (A ^ s + B ^ s) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `m^{-a} ≤ 2^a M^{-a}` when `0 < m`, `0 < M`, `a > 0` and `M ≤ 2m`. -/
lemma rpow_neg_le_mul_two_pow {m M a : ℝ} (hm : 0 < m) (hM : 0 < M) (ha : 0 < a)
    (h : M ≤ 2 * m) : m ^ (-a) ≤ (2 : ℝ) ^ a * M ^ (-a) := by
  have hM2 : M / 2 ≤ m := by linarith
  have h0 : (0 : ℝ) ≤ M / 2 := by linarith
  have hpow : (M / 2) ^ a ≤ m ^ a := Real.rpow_le_rpow h0 hM2 ha.le
  have hp1 : 0 < (M / 2) ^ a := Real.rpow_pos_of_pos (by linarith) a
  have hp2 : 0 < m ^ a := Real.rpow_pos_of_pos hm a
  have hinv : (m ^ a)⁻¹ ≤ ((M / 2) ^ a)⁻¹ := (inv_le_inv₀ hp2 hp1).mpr hpow
  rw [← Real.rpow_neg hm.le, ← Real.rpow_neg h0] at hinv
  have h2 : (M / 2) ^ (-a) = (2 : ℝ) ^ a * M ^ (-a) := by
    rw [show (M / 2 : ℝ) = M * (1 / 2) by ring]
    rw [Real.mul_rpow hM.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show ((1 / 2 : ℝ)) ^ (-a) = (2 : ℝ) ^ a by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring]
    ring
  linarith [hinv, h2.le]

/-! ## Structural rewriting lemmas for `2 ^ ·` with real exponents

These are stated with *variable* exponents so that they match structurally
(`2 ^ u` for any `u`), which is what makes exponent arithmetic usable. -/

lemma two_rpow_mul {u v : ℝ} : ((2 : ℝ) ^ u) ^ v = (2 : ℝ) ^ (u * v) :=
  (Real.rpow_mul (by norm_num) u v).symm

lemma two_rpow_add {u v : ℝ} : (2 : ℝ) ^ (u + v) = (2 : ℝ) ^ u * (2 : ℝ) ^ v :=
  Real.rpow_add (by norm_num) u v

lemma two_rpow_logb {m : ℝ} (hm : 0 < m) : (2 : ℝ) ^ (Real.logb 2 m) = m :=
  Real.rpow_logb (by norm_num) (by norm_num) hm

lemma two_rpow_mono {u v : ℝ} (h : u ≤ v) : (2 : ℝ) ^ u ≤ (2 : ℝ) ^ v :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

lemma two_rpow_add_comm {u v : ℝ} : (2 : ℝ) ^ (u + v) = (2 : ℝ) ^ v * (2 : ℝ) ^ u := by
  rw [add_comm, two_rpow_add]

lemma rpow_pow_mul {x u v : ℝ} (hx : 0 ≤ x) : (x ^ u) ^ v = x ^ (u * v) :=
  (Real.rpow_mul hx u v).symm

/-- The coercion bridge: a real inequality of nonnegative reals lifts to `ℝ≥0∞`. -/
theorem ennrealRpowLift {x y z K : NNReal} {s P : ℝ} (hs : 0 ≤ s) (hP : 0 ≤ P)
    (h : ((x : ℝ)) ^ s * ((y : ℝ)) ^ P ≤ ((K : ℝ)) * ((z : ℝ))) :
    (x : ENNReal) ^ s * (y : ENNReal) ^ P ≤ (K : ENNReal) * (z : ENNReal) := by
  have hL : (x : ENNReal) ^ s * (y : ENNReal) ^ P
      = ((x ^ s * y ^ P : NNReal) : ENNReal) := by
    rw [ENNReal.rpow_ofNNReal hs, ENNReal.rpow_ofNNReal hP, ENNReal.coe_mul]
  have hR : (K : ENNReal) * (z : ENNReal) = ((K * z : NNReal) : ENNReal) := by
    rw [ENNReal.coe_mul]
  rw [hL, hR, ENNReal.coe_le_coe]
  show ((x ^ s * y ^ P : NNReal) : ℝ) ≤ ((K * z : NNReal) : ℝ)
  rw [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_mul]
  exact h

end

end Work.KMTAreas.A5
