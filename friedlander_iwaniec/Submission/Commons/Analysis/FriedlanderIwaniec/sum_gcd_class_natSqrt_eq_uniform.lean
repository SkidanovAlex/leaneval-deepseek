import Mathlib
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_coprime_sqrt_sub_pow_four

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Commons.Analysis.FriedlanderIwaniec

/-! ## Auxiliary power identities for the fourth root -/

/-- `(x^(1/4))^4 = x` for `x ≥ 0`. -/
private lemma rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) : (x ^ (1/4:ℝ)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(x^4)^(1/4) = x` for `x ≥ 0`. -/
private lemma pow_four_rpow_quarter {x : ℝ} (hx : 0 ≤ x) : (x ^ 4) ^ (1/4:ℝ) = x := by
  rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx]
  norm_num

/-- `(x^(1/4))^2 = √x` for `x ≥ 0`. -/
private lemma rpow_quarter_pow_two {x : ℝ} (hx : 0 ≤ x) : (x ^ (1/4:ℝ)) ^ 2 = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  norm_num

/-- `(x^(1/4))^3 = x^(3/4)` for `x ≥ 0`. -/
private lemma rpow_quarter_pow_three {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1/4:ℝ)) ^ 3 = x ^ (3/4:ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The integer part of the fourth root of `x` is the iterated integer square root. -/
private lemma floor_rpow_quarter_eq_sqrt_sqrt (x : ℕ) :
    ⌊(x:ℝ) ^ (1/4:ℝ)⌋₊ = Nat.sqrt (Nat.sqrt x) := by
  have hN4 : (Nat.sqrt (Nat.sqrt x))^4 ≤ x := by
    have h1 : (Nat.sqrt (Nat.sqrt x))^2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x)^2 ≤ x := Nat.sqrt_le' _
    calc (Nat.sqrt (Nat.sqrt x))^4 = ((Nat.sqrt (Nat.sqrt x))^2)^2 := by ring
      _ ≤ (Nat.sqrt x)^2 := Nat.pow_le_pow_left h1 2
      _ ≤ x := h2
  have hxlt : x < (Nat.sqrt (Nat.sqrt x)+1)^4 := by
    have h1 : x < (Nat.sqrt x + 1)^2 := Nat.lt_succ_sqrt' x
    have h2 : Nat.sqrt x < (Nat.sqrt (Nat.sqrt x)+1)^2 := Nat.lt_succ_sqrt' (Nat.sqrt x)
    have h3 : Nat.sqrt x + 1 ≤ (Nat.sqrt (Nat.sqrt x)+1)^2 := h2
    calc x < (Nat.sqrt x + 1)^2 := h1
      _ ≤ ((Nat.sqrt (Nat.sqrt x)+1)^2)^2 := Nat.pow_le_pow_left h3 2
      _ = (Nat.sqrt (Nat.sqrt x)+1)^4 := by ring
  have h1 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x:ℝ)^(1/4:ℝ) := by
    have h : (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)^4)^(1/4:ℝ) ≤ (x:ℝ)^(1/4:ℝ) :=
      (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num)).mpr
        (by exact_mod_cast hN4)
    rwa [pow_four_rpow_quarter (by positivity)] at h
  have h2 : (x:ℝ)^(1/4:ℝ) < ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) + 1 := by
    have hxcast : (x:ℝ) < (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)+1)^4 := by
      have h := (Nat.cast_lt (α := ℝ)).mpr hxlt
      push_cast at h
      linarith [h]
    have h : (x:ℝ)^(1/4:ℝ) < ((((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)+1)^4)^(1/4:ℝ) :=
      (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num)).mpr hxcast
    rwa [pow_four_rpow_quarter (by positivity)] at h
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨h1, by simpa using h2⟩

/-! ## Rounding the square roots -/

/-- The integer square root approximation error `2⌊√n⌋ + 1 - 2√n` has absolute value at most `1`. -/
private lemma abs_two_natSqrt_add_one_sub_two_realSqrt_le_one (n : ℕ) :
    |((2 * Nat.sqrt n + 1 : ℕ) : ℝ) - 2 * Real.sqrt (n : ℝ)| ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) hn0]
    calc (Nat.sqrt n : ℝ) ^ 2 = ((Nat.sqrt n) ^ 2 : ℕ) := by push_cast; ring
      _ ≤ (n : ℝ) := by exact_mod_cast (Nat.sqrt_le' n)
  have hlt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
    rw [Real.sqrt_lt hn0 (by positivity)]
    calc (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast (by
            have := Nat.sqrt_lt'.mp (Nat.lt_succ_self (Nat.sqrt n)); simpa using this)
      _ = ((Nat.sqrt n : ℝ) + 1) ^ 2 := by push_cast; ring
  have hcast : ((2 * Nat.sqrt n + 1 : ℕ) : ℝ) = 2 * (Nat.sqrt n : ℝ) + 1 := by
    push_cast; ring
  rw [hcast, abs_le]
  constructor <;> linarith

/-- For `c⁴ ≤ x`, the difference between the counting function
`2⌊√(x - c⁴)⌋ + 1` and `2√(x - c⁴)` is at most `1`. -/
private lemma abs_natSqrt_count_sub_two_sqrt_le_one {x c : ℕ} (hc : c ^ 4 ≤ x) :
    |(((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) - 2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)|
      ≤ 1 := by
  have hcast : ((x - c^4 : ℕ) : ℝ) = (x:ℝ) - (c:ℝ)^4 := by
    rw [Nat.cast_sub hc]; push_cast; ring
  rw [← hcast]
  exact abs_two_natSqrt_add_one_sub_two_realSqrt_le_one (x - c ^ 4)

/-! ## The rounding error over a gcd class -/

/-- Replacing each `2⌊√(x - c⁴)⌋ + 1` by `2√(x - c⁴)` over the gcd class
`gcd c m = ν`, `1 ≤ c ≤ ⌊x^(1/4)⌋`, costs at most the number of terms. -/
private lemma abs_sum_gcd_class_natSqrt_sub_two_sqrt_le {m ν x : ℕ} :
    |(∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ))
      - 2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))|
      ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
  have hN4 : (Nat.sqrt (Nat.sqrt x))^4 ≤ x := by
    have h1 : (Nat.sqrt (Nat.sqrt x))^2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x)^2 ≤ x := Nat.sqrt_le' _
    calc (Nat.sqrt (Nat.sqrt x))^4 = ((Nat.sqrt (Nat.sqrt x))^2)^2 := by ring
      _ ≤ (Nat.sqrt x)^2 := Nat.pow_le_pow_left h1 2
      _ ≤ x := h2
  have hterm : ∀ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
      |(((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) - 2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)|
        ≤ 1 := by
    intro c hc
    have hcN : c ≤ Nat.sqrt (Nat.sqrt x) := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).2
    exact abs_natSqrt_count_sub_two_sqrt_le_one (le_trans (Nat.pow_le_pow_left hcN 4) hN4)
  have hsplit : (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ))
      - 2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
      = ∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        ((((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) - 2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  calc |∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        ((((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) - 2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))|
      ≤ ∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
        |(((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ)) : ℝ) - 2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν), (1:ℝ) := by
        apply Finset.sum_le_sum; intro c hc; exact hterm c hc
    _ = (((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
        have hcard : ((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter
              (fun c => Nat.gcd c m = ν)).card ≤ Nat.sqrt (Nat.sqrt x) := by
          calc ((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν)).card
              ≤ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).card :=
                Finset.card_filter_le _ _
            _ = Nat.sqrt (Nat.sqrt x) := by simp
        exact_mod_cast hcard

private lemma sum_Icc_filter_gcd_eq_sum_Icc_filter_coprime {m ν : ℕ} (hνpos : 0 < ν)
    (hmν : m = ν * (m / ν)) {N K : ℕ} (hNK : ∀ d : ℕ, d ≤ K ↔ ν * d ≤ N) (g : ℕ → ℝ) :
    ∑ c ∈ (Finset.Icc 1 N).filter (fun c => Nat.gcd c m = ν), g c
      = ∑ d ∈ (Finset.Icc 1 K).filter (fun d => Nat.Coprime d (m / ν)), g (ν * d) := by
  set q : ℕ := m / ν with hq
  have hm' : m = ν * q := by rw [hmν, hq]
  have hgcd : ∀ d : ℕ, Nat.gcd (ν * d) m = ν ↔ Nat.Coprime d q := by
    intro d
    rw [hm', Nat.gcd_mul_left, Nat.coprime_iff_gcd_eq_one]
    constructor
    · intro h
      exact Nat.mul_left_cancel hνpos (by rw [h, Nat.mul_one])
    · intro h
      rw [h, Nat.mul_one]
  refine Finset.sum_bij (fun c _ => c / ν) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hc1, hcN⟩, hcgcd⟩ := hc
    have hsplit : ν * (c / ν) = c := Nat.mul_div_cancel' (hcgcd ▸ Nat.gcd_dvd_left c m)
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos (c / ν) with h | h
      · rw [h, Nat.mul_zero] at hsplit
        omega
      · exact h
    · exact (hNK (c / ν)).mpr (by rw [hsplit]; exact hcN)
    · have hh : Nat.gcd (ν * (c / ν)) m = ν := by rw [hsplit]; exact hcgcd
      exact (hgcd (c / ν)).mp hh
  · intro a1 ha1 a2 ha2 heq
    rw [Finset.mem_filter] at ha1 ha2
    have h1 : ν * (a1 / ν) = a1 := Nat.mul_div_cancel' (ha1.2 ▸ Nat.gcd_dvd_left a1 m)
    have h2 : ν * (a2 / ν) = a2 := Nat.mul_div_cancel' (ha2.2 ▸ Nat.gcd_dvd_left a2 m)
    rw [← h1, ← h2, heq]
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hbK⟩, hbcop⟩ := hb
    refine ⟨ν * b, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.mul_pos hνpos (by omega), (hNK b).mp hbK⟩, (hgcd b).mpr hbcop⟩
    · exact Nat.mul_div_cancel_left b hνpos
  · intro c hc
    rw [Finset.mem_filter] at hc
    have hsplit : ν * (c / ν) = c := Nat.mul_div_cancel' (hc.2 ▸ Nat.gcd_dvd_left c m)
    rw [hsplit]

/-- **Removing the `d = 0` term** from a sum over `{0, …, K}` that is filtered by
coprimality with `q`: the only difference to the sum over `{1, …, K}` is the
contribution of `0`, which is coprime to `q` exactly when `q = 1`. -/
private lemma sum_range_filter_coprime_eq {q K : ℕ} (f : ℕ → ℝ) :
    ∑ d ∈ (Finset.range (K + 1)).filter (fun d => Nat.Coprime d q), f d
      = ∑ d ∈ (Finset.Icc 1 K).filter (fun d => Nat.Coprime d q), f d
        + (if Nat.Coprime 0 q then f 0 else 0) := by
  have hset : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  conv_lhs => rw [hset]
  rw [Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
    ring
  · ring

lemma sum_sqrt_sub_pow_four_dilate_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 1 ≤ s → ∀ y : ℝ, 1 ≤ y →
      |(∑ k ∈ Finset.range (⌊y / s⌋₊ + 1), Real.sqrt (y ^ 4 - ((s * k : ℕ) : ℝ) ^ 4)) -
        (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / s| ≤ C * y ^ 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro s hs y hy
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) := by linarith
  have hJ0 : 0 ≤ ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    integral_nonneg (by norm_num) (fun u _ => Real.sqrt_nonneg _)
  by_cases hsy : (s : ℝ) ≤ y
  · -- case y ≥ s : reduce to the s = 1 lemma by scaling
    have hY : (1 : ℝ) ≤ y / (s : ℝ) := by
      rw [le_div_iff₀ hspos]; simpa using hsy
    have hB := sum_sqrt_sub_pow_four_sub_kappa_le (y := y / (s : ℝ)) hY
    have hterm : ∀ c : ℕ,
        (s : ℝ) ^ 2 * Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4) =
          Real.sqrt (y ^ 4 - ((s * c : ℕ) : ℝ) ^ 4) := by
      intro c
      have hcast : ((s * c : ℕ) : ℝ) = (s : ℝ) * (c : ℝ) := by push_cast; ring
      rw [hcast]
      have hs2 : Real.sqrt ((s : ℝ) ^ 4) = (s : ℝ) ^ 2 := by
        rw [show (s : ℝ) ^ 4 = ((s : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      have hkey : (s : ℝ) ^ 4 * ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)
          = y ^ 4 - ((s : ℝ) * (c : ℝ)) ^ 4 := by
        field_simp
      calc (s : ℝ) ^ 2 * Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)
          = Real.sqrt ((s : ℝ) ^ 4) * Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4) := by
              rw [hs2]
        _ = Real.sqrt ((s : ℝ) ^ 4 * ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)) :=
              (Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (s : ℝ) ^ 4) _).symm
        _ = Real.sqrt (y ^ 4 - ((s : ℝ) * (c : ℝ)) ^ 4) := by rw [hkey]
    have hSA : (∑ k ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
          Real.sqrt (y ^ 4 - ((s * k : ℕ) : ℝ) ^ 4))
        = (s : ℝ) ^ 2 * (∑ c ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
          Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c _ => (hterm c).symm)
    have hAI : (s : ℝ) ^ 2 * ((∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ)) ^ 3)
        = (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / (s : ℝ) := by
      field_simp
    have hEq : (∑ k ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
          Real.sqrt (y ^ 4 - ((s * k : ℕ) : ℝ) ^ 4)) -
          (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / (s : ℝ)
        = (s : ℝ) ^ 2 * ((∑ c ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
            Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)) -
            (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ)) ^ 3) := by
      rw [hSA, ← hAI]; ring
    rw [hEq]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) ^ 2), one_mul]
    calc (s : ℝ) ^ 2 * |(∑ c ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
            Real.sqrt ((y / (s : ℝ)) ^ 4 - (c : ℝ) ^ 4)) -
            (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ)) ^ 3|
        ≤ (s : ℝ) ^ 2 * (y / (s : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = y ^ 2 := by field_simp
  · -- case y < s : the sum has only the k = 0 term
    have hys : y < (s : ℝ) := lt_of_not_ge hsy
    have hfloor : ⌊y / (s : ℝ)⌋₊ = 0 := by
      rw [Nat.floor_eq_zero, div_lt_one hspos]
      exact hys
    have hSval : (∑ k ∈ Finset.range (⌊y / (s : ℝ)⌋₊ + 1),
          Real.sqrt (y ^ 4 - ((s * k : ℕ) : ℝ) ^ 4)) = y ^ 2 := by
      rw [hfloor, Nat.zero_add, Finset.sum_range_one]
      rw [show ((s * 0 : ℕ) : ℝ) = 0 by simp]
      rw [show y ^ 4 - (0 : ℝ) ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hJle1 : (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) ≤ 1 := by
      have hcont : Continuous (fun u : ℝ => Real.sqrt (1 - u ^ 4)) := by fun_prop
      have hint : IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u ^ 4)) volume (0:ℝ) 1 :=
        hcont.intervalIntegrable 0 1
      have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (0:ℝ) 1 :=
        intervalIntegrable_const
      have h := integral_mono_on (show (0:ℝ) ≤ 1 by norm_num) hint hconst
        (fun u hu => by
          rw [Real.sqrt_le_one]
          nlinarith [sq_nonneg (u ^ 2)])
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h
      exact h
    have hJy0 : 0 ≤ (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / (s : ℝ) := by
      apply div_nonneg _ hspos.le
      exact mul_nonneg hJ0 (by positivity)
    have hJoy : (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / (s : ℝ) ≤ y ^ 2 := by
      have hydiv : y / (s : ℝ) ≤ 1 := by rw [div_le_one hspos]; linarith
      have hb : (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ)) ≤ 1 := by
        calc (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ))
            ≤ 1 * 1 := mul_le_mul hJle1 hydiv (by positivity) (by linarith)
          _ = 1 := by ring
      have heq : (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / (s : ℝ)
          = y ^ 2 * ((∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ))) := by
        field_simp
      rw [heq]
      calc y ^ 2 * ((∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (y / (s : ℝ)))
          ≤ y ^ 2 * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = y ^ 2 := by ring
    rw [hSval, one_mul, abs_le]
    constructor <;> linarith [hJy0, hJoy, sq_nonneg y]

lemma sum_coprime_sqrt_sub_pow_four_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ m s : ℕ, 0 < m → 0 < s → s ∣ m → ∀ y : ℝ, 1 ≤ y →
      |(∑ c ∈ (Finset.range (⌊y / s⌋₊ + 1)).filter (fun c => Nat.Coprime c (m / s)),
          Real.sqrt (y ^ 4 - ((s * c : ℕ) : ℝ) ^ 4))
        - (Nat.totient (m / s) : ℝ) / (m / s) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / s| ≤
        C * ((Nat.divisors (m / s)).card : ℝ) * y ^ 2 := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := sum_sqrt_sub_pow_four_dilate_le_uniform
  refine ⟨2 + C₂, by linarith, ?_⟩
  intro m s hm hs hsdvd y hy
  have hs1 : 1 ≤ s := hs
  set q : ℕ := m / s with hqdef
  have hm_eq : m = s * q := by rw [hqdef]; exact (Nat.mul_div_cancel' hsdvd).symm
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, Nat.mul_zero] at hm_eq; omega
    · exact h
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega)
  have hden : (m : ℝ) / (s : ℝ) = (q : ℝ) := by
    rw [hqdef]
    exact (Nat.cast_div hsdvd (by positivity : (s:ℝ) ≠ 0)).symm
  rw [hden]
  set ratio : ℝ := (Nat.totient q : ℝ) / (q : ℝ) with hrdef
  set dq : ℝ := ((Nat.divisors q).card : ℝ) with hddef
  set f : ℕ → ℝ := fun c => Real.sqrt (y ^ 4 - ((s * c : ℕ) : ℝ) ^ 4) with hfdef
  have hf0 : f 0 = y ^ 2 := by
    simp only [hfdef, Nat.mul_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero]
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg y)]
  have hfnonneg : ∀ k, 0 ≤ f k := fun k => Real.sqrt_nonneg _
  have hfmono : ∀ k, k < ⌊y / s⌋₊ → f (k + 1) ≤ f k := by
    intro k _
    simp only [hfdef]
    apply Real.sqrt_le_sqrt
    have hle : ((s * k : ℕ) : ℝ) ≤ ((s * (k + 1) : ℕ) : ℝ) := by
      have : s * k ≤ s * (k + 1) := Nat.mul_le_mul_left s (by omega)
      exact_mod_cast this
    have hpow : ((s * k : ℕ) : ℝ) ^ 4 ≤ ((s * (k + 1) : ℕ) : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hle 4
    linarith
  have hsum_eq : ∑ c ∈ (Finset.range (⌊y / s⌋₊ + 1)).filter (fun c => Nat.Coprime c q), f c
      = ∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
          (if Nat.Coprime c q then (1:ℝ) else 0) * f c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : Nat.Coprime c q <;> simp [h]
  have hdecomp : ∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
        (if Nat.Coprime c q then (1:ℝ) else 0) * f c
      = (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
          ((if Nat.Coprime c q then (1:ℝ) else 0) - ratio) * f c)
        + ratio * (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1), f c) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsum_eq, hdecomp]
  have hgoal : (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
          ((if Nat.Coprime c q then (1:ℝ) else 0) - ratio) * f c)
        + ratio * (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1), f c)
        - ratio * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / s
      = (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
          ((if Nat.Coprime c q then (1:ℝ) else 0) - ratio) * f c)
        + ratio * ((∑ c ∈ Finset.range (⌊y / s⌋₊ + 1), f c)
          - (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / s) := by ring
  rw [hgoal]
  set A : ℝ := ∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
      ((if Nat.Coprime c q then (1:ℝ) else 0) - ratio) * f c with hAdef
  set B : ℝ := (∑ c ∈ Finset.range (⌊y / s⌋₊ + 1), f c)
      - (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / s with hBdef
  have hD1 : |A| ≤ (dq + 1) * y ^ 2 := by
    have hAb := abs_sum_range_mul_le_of_partial_sum_bound
      (a := fun c => (if Nat.Coprime c q then (1:ℝ) else 0) - ratio)
      (w := f) (D := dq + 1) (N := ⌊y / s⌋₊)
      (fun k _ => by have := abs_sum_range_coprime_sub_ratio_le q hq1 k; simpa [dq] using this)
      (fun k hk => hfmono k hk)
      (fun k _ => hfnonneg k)
    simp only [hf0] at hAb
    have hAeq : A = ∑ c ∈ Finset.range (⌊y / s⌋₊ + 1),
        f c * ((if Nat.Coprime c q then (1:ℝ) else 0) - ratio) := by
      rw [hAdef]
      apply Finset.sum_congr rfl; intro c _; ring
    rw [hAeq]; exact hAb
  have hD2 : |B| ≤ C₂ * y ^ 2 := by
    rw [hBdef]
    simpa [f] using hC₂ s hs1 y hy
  have hratio0 : 0 ≤ ratio := by
    rw [hrdef]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratio1 : ratio ≤ 1 := by
    rw [hrdef, div_le_one hqpos]; exact_mod_cast Nat.totient_le q
  have hdq1 : 1 ≤ dq := by
    rw [hddef]
    exact_mod_cast Finset.card_pos.mpr
      ⟨1, Nat.one_mem_divisors.mpr (by omega : q ≠ 0)⟩
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  have hfin : (dq + 1) * y ^ 2 + ratio * (C₂ * y ^ 2) ≤ (2 + C₂) * dq * y ^ 2 := by
    have hA' : (dq + 1) * y ^ 2 ≤ 2 * dq * y ^ 2 := by
      have : dq + 1 ≤ 2 * dq := by linarith
      calc (dq + 1) * y ^ 2 ≤ (2 * dq) * y ^ 2 := mul_le_mul_of_nonneg_right this hy2
        _ = 2 * dq * y ^ 2 := by ring
    have hB' : ratio * (C₂ * y ^ 2) ≤ C₂ * (dq * y ^ 2) := by
      have hry : ratio * y ^ 2 ≤ dq * y ^ 2 :=
        mul_le_mul_of_nonneg_right (le_trans hratio1 hdq1) hy2
      calc ratio * (C₂ * y ^ 2) = C₂ * (ratio * y ^ 2) := by ring
        _ ≤ C₂ * (dq * y ^ 2) := mul_le_mul_of_nonneg_left hry hC₂nn
    calc (dq + 1) * y ^ 2 + ratio * (C₂ * y ^ 2)
        ≤ 2 * dq * y ^ 2 + C₂ * (dq * y ^ 2) := add_le_add hA' hB'
      _ = (2 + C₂) * dq * y ^ 2 := by ring
  calc |A + ratio * B| ≤ |A| + |ratio * B| := abs_add_le _ _
    _ = |A| + ratio * |B| := by rw [abs_mul, abs_of_nonneg hratio0]
    _ ≤ (dq + 1) * y ^ 2 + ratio * (C₂ * y ^ 2) :=
        add_le_add hD1 (mul_le_mul_of_nonneg_left hD2 hratio0)
    _ ≤ (2 + C₂) * dq * y ^ 2 := hfin

theorem sum_coprime_sqrt_sub_pow_four_half_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ m ν : ℕ, 0 < m → 0 < ν → ν ∣ m → ∀ y : ℝ, 1 ≤ y →
      |(∑ c ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun c => Nat.gcd c m = ν),
          Real.sqrt (y ^ 4 - (c : ℝ) ^ 4))
        - (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / m|
        ≤ C * ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := sum_coprime_sqrt_sub_pow_four_uniform
  refine ⟨C + 1, by linarith, ?_⟩
  intro m ν hm hνpos hν y hy
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hqpos : 0 < m / ν := Nat.div_pos (Nat.le_of_dvd hm hν) hνpos
  have hmν : m = ν * (m / ν) := (Nat.mul_div_cancel' hν).symm
  have hNK : ∀ d : ℕ, d ≤ ⌊y / ν⌋₊ ↔ ν * d ≤ ⌊y⌋₊ := by
    intro d
    rw [Nat.floor_div_natCast y ν, Nat.le_div_iff_mul_le hνpos, Nat.mul_comm ν d]
  set g : ℕ → ℝ := (fun t => Real.sqrt (y ^ 4 - (t : ℝ) ^ 4)) with hg
  have hg0 : g 0 = y ^ 2 := by
    simp only [hg]
    rw [show ((0 : ℕ) : ℝ) = 0 by norm_num, show (0 : ℝ) ^ 4 = 0 by norm_num, sub_zero,
      show y ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq hy2]
  -- (i) reindex the target sum
  have hT : (∑ c ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun c => Nat.gcd c m = ν),
        Real.sqrt (y ^ 4 - (c : ℝ) ^ 4))
      = ∑ d ∈ (Finset.Icc 1 ⌊y / ν⌋₊).filter (fun d => Nat.Coprime d (m / ν)), g (ν * d) := by
    calc (∑ c ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt (y ^ 4 - (c : ℝ) ^ 4))
        = ∑ c ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun c => Nat.gcd c m = ν), g c :=
          Finset.sum_congr rfl (fun c _ => by simp [hg])
      _ = ∑ d ∈ (Finset.Icc 1 ⌊y / ν⌋₊).filter (fun d => Nat.Coprime d (m / ν)), g (ν * d) :=
          sum_Icc_filter_gcd_eq_sum_Icc_filter_coprime hνpos hmν hNK g
  -- (ii) the auxiliary sums
  set S : ℝ := ∑ d ∈ (Finset.Icc 1 ⌊y / ν⌋₊).filter (fun d => Nat.Coprime d (m / ν)),
      g (ν * d) with hSdef
  set L : ℝ := ∑ d ∈ (Finset.range (⌊y / ν⌋₊ + 1)).filter (fun d => Nat.Coprime d (m / ν)),
      g (ν * d) with hLdef
  set Mlem : ℝ := (Nat.totient (m / ν) : ℝ) / (m / ν)
      * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / ν with hMldef
  set M : ℝ := (Nat.totient (m / ν) : ℝ)
      * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3 / m with hMdef
  -- (iii) the range sum is the coprime lemma's sum
  have hLbound : |L - Mlem| ≤ C * ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 := by
    rw [hLdef, hMldef]
    simpa [hg] using hC m ν hm hνpos hν y hy
  -- (iv) comparison of the range and Icc sums
  have hcorr : (if Nat.Coprime 0 (m / ν) then (fun d : ℕ => g (ν * d)) 0 else 0)
      = (if m / ν = 1 then y ^ 2 else 0) := by
    have hz : (fun d : ℕ => g (ν * d)) 0 = y ^ 2 := by
      simp only [Nat.mul_zero]; exact hg0
    rw [hz]
    by_cases h : m / ν = 1
    · rw [if_pos ((Nat.coprime_zero_left _).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((Nat.coprime_zero_left _).mp hc)), if_neg h]
  have hL_eq : L = S + (if m / ν = 1 then y ^ 2 else 0) := by
    rw [hLdef, hSdef, sum_range_filter_coprime_eq (q := m / ν) (K := ⌊y / ν⌋₊)
      (fun d => g (ν * d)), hcorr]
  have hS_eq : S = L - (if m / ν = 1 then y ^ 2 else 0) := by linarith
  have hcorr_le : |(if m / ν = 1 then y ^ 2 else 0)| ≤ y ^ 2 := by
    by_cases h : m / ν = 1
    · rw [if_pos h, abs_of_nonneg hy2]
    · rw [if_neg h, abs_zero]; exact hy2
  -- (v) the main terms agree
  have hmain : Mlem = M := by
    rw [hMldef, hMdef]
    have hmne : (m : ℝ) ≠ 0 := by positivity
    have hνne : (ν : ℝ) ≠ 0 := by positivity
    field_simp
  -- (vi) combine
  have hgoal_eq : |(∑ c ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun c => Nat.gcd c m = ν),
        Real.sqrt (y ^ 4 - (c : ℝ) ^ 4)) - M|
      = |(L - Mlem) - (if m / ν = 1 then y ^ 2 else 0)| := by
    rw [hT, hS_eq, ← hmain]
    congr 1
    ring
  have hτ1 : (1 : ℝ) ≤ ((Nat.divisors (m / ν)).card : ℝ) := by
    have : 1 ≤ (Nat.divisors (m / ν)).card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (ne_of_gt hqpos)⟩
    exact_mod_cast this
  rw [hgoal_eq]
  calc |(L - Mlem) - (if m / ν = 1 then y ^ 2 else 0)|
      ≤ |(L - Mlem) - 0| + |0 - (if m / ν = 1 then y ^ 2 else 0)| := abs_sub_le _ _ _
    _ = |L - Mlem| + |(if m / ν = 1 then y ^ 2 else 0)| := by
        rw [sub_zero, zero_sub, abs_neg]
    _ ≤ C * ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 + y ^ 2 :=
        add_le_add hLbound hcorr_le
    _ ≤ (C + 1) * ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 := by
        have hle : y ^ 2 ≤ ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 := by
          calc y ^ 2 = 1 * y ^ 2 := by ring
            _ ≤ ((Nat.divisors (m / ν)).card : ℝ) * y ^ 2 :=
                mul_le_mul_of_nonneg_right hτ1 hy2
        nlinarith [hle]



/-- Uniform-in-`m,ν,x` version of `sum_gcd_class_sqrt_sub_pow_four_x`. -/
lemma sum_gcd_class_sqrt_sub_pow_four_x_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ m ν x : ℕ, 0 < m → 0 < ν → ν ∣ m → 1 ≤ x →
      |(∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
          Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
        - (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
            * (x : ℝ) ^ (3 / 4 : ℝ) / m|
        ≤ C * ((Nat.divisors (m / ν)).card : ℝ) * Real.sqrt x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := sum_coprime_sqrt_sub_pow_four_half_uniform
  refine ⟨C₀, hC₀pos, ?_⟩
  intro m ν x hm hνpos hν hx
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg x
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hy1 : (1:ℝ) ≤ (x:ℝ)^(1/4:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have h := hC₀ m ν hm hνpos hν ((x:ℝ)^(1/4:ℝ)) hy1
  rwa [floor_rpow_quarter_eq_sqrt_sqrt x, rpow_quarter_pow_four hx0,
      rpow_quarter_pow_three hx0, rpow_quarter_pow_two hx0] at h

theorem sum_gcd_class_natSqrt_eq_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ m ν x : ℕ, 0 < m → 0 < ν → ν ∣ m → 1 ≤ x →
      |(∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
          ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ))
        - 2 * (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
            * (x : ℝ) ^ (3 / 4 : ℝ) / m|
        ≤ C * ((Nat.divisors (m / ν)).card : ℝ) * Real.sqrt x
          + C * ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sum_gcd_class_sqrt_sub_pow_four_x_uniform
  refine ⟨2 * C₁ + 2, by linarith, ?_⟩
  intro m ν x hm hνpos hν hx
  have hround := abs_sum_gcd_class_natSqrt_sub_two_sqrt_le (m := m) (ν := ν) (x := x)
  have hdoubled :
      |2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
          - 2 * (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
              * (x : ℝ) ^ (3 / 4 : ℝ) / m|
        ≤ 2 * (C₁ * ((Nat.divisors (m / ν)).card : ℝ) * Real.sqrt x) := by
    have he : 2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
          - 2 * (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
              * (x : ℝ) ^ (3 / 4 : ℝ) / m
        = 2 * ((∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
          - (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
              * (x : ℝ) ^ (3 / 4 : ℝ) / m) := by ring
    rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hC₁ m ν x hm hνpos hν hx) (by norm_num)
  have hτ0 : (0:ℝ) ≤ ((Nat.divisors (m / ν)).card : ℝ) := Nat.cast_nonneg _
  have hxs0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hN0 : (0:ℝ) ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := Nat.cast_nonneg _
  calc |(∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
          ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ))
        - 2 * (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
            * (x : ℝ) ^ (3 / 4 : ℝ) / m|
      ≤ |(∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ))
          - 2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))|
        + |2 * (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter (fun c => Nat.gcd c m = ν),
            Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4))
          - 2 * (Nat.totient (m / ν) : ℝ) * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4))
              * (x : ℝ) ^ (3 / 4 : ℝ) / m| := abs_sub_le _ _ _
    _ ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)
        + 2 * (C₁ * ((Nat.divisors (m / ν)).card : ℝ) * Real.sqrt x) := add_le_add hround hdoubled
    _ ≤ (2 * C₁ + 2) * ((Nat.divisors (m / ν)).card : ℝ) * Real.sqrt x
        + (2 * C₁ + 2) * ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
        nlinarith [hC₁pos, hτ0, hxs0, hN0,
          mul_nonneg hτ0 hxs0, mul_nonneg (le_of_lt hC₁pos) hN0]

end Commons.Analysis.FriedlanderIwaniec
