import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset Real Complex Filter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate

namespace Commons
namespace NumberTheory
namespace DirichletPolynomial

/-- ∑_{k=1}^K 1/k ≤ 1 + log K, as reals -/
lemma sum_inv_Icc_le_log (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ((k : ℝ))⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  simpa using h

lemma log_pred_le_log (K : ℕ) (hK : 1 ≤ K) : Real.log (↑(K - 1) : ℝ) ≤ Real.log (K : ℝ) := by
  by_cases h1 : K = 1
  · simp [h1]
  · have hK2 : 2 ≤ K := by omega
    have hposn : 0 < K - 1 := by omega
    have hpos : 0 < (↑(K - 1) : ℝ) := by exact_mod_cast hposn
    exact Real.log_le_log hpos (by exact_mod_cast (Nat.sub_le K 1))

/-- ∑_{m=1}^{K-1} 1/m ≤ 1 + log K (as reals), with Ico 1 K = {1,..,K-1} -/
lemma sum_inv_Ico_le_log (K : ℕ) :
    (∑ m ∈ Finset.Ico 1 K, ((m : ℝ))⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  by_cases hK : K = 0
  · simp [hK]
  · have hK1 : 1 ≤ K := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hK)
    calc
      (∑ m ∈ Finset.Ico 1 K, ((m : ℝ))⁻¹) = ∑ m ∈ Finset.Icc 1 (K - 1), ((m : ℝ))⁻¹ := by
        apply Finset.sum_congr rfl
        intro m hm
        rfl
      _ ≤ 1 + Real.log (↑(K - 1) : ℝ) := sum_inv_Icc_le_log (K - 1)
      _ ≤ 1 + Real.log (K : ℝ) := by
        simpa [add_comm] using add_le_add_right (log_pred_le_log K hK1) 1

/-- reflect: Σ_{m ∈ Ico 1 n} 1/(n-m) = Σ_{m ∈ Ico 1 n} 1/m -/
lemma sum_inv_sub_self (n : ℕ) :
    (∑ m ∈ Finset.Ico 1 n, (((n : ℝ) - (m : ℝ))⁻¹)) =
      ∑ m ∈ Finset.Ico 1 n, ((m : ℝ))⁻¹ := by
  have hreflect := sum_Ico_reflect (fun j : ℕ => ((j : ℝ))⁻¹) 1 (m := n) (n := n) (by omega : n ≤ n + 1)
  calc
    (∑ m ∈ Finset.Ico 1 n, (((n : ℝ) - (m : ℝ))⁻¹))
        = ∑ m ∈ Finset.Ico 1 n, (((n - m : ℕ) : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro m hm
          congr 1
          rw [Nat.cast_sub]
          exact_mod_cast (le_of_lt (Finset.mem_Ico.mp hm).2)
    _ = ∑ m ∈ Finset.Ico 1 n, ((m : ℝ))⁻¹ := by
          simpa using hreflect

lemma log_ratio_sub (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) :
    Real.log (a / b) ≥ (a - b) / a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hpos : 0 < a / b := div_pos ha hb
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hrew : 1 - (a / b)⁻¹ = (a - b) / a := by
    field_simp [ha.ne', hb.ne']
  rwa [hrew] at h

lemma abs_log_ratio_ge (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |Real.log (a / b)| ≥ |a - b| / max a b := by
  rcases le_total a b with hab | hba
  · have h1 := log_ratio_sub b a ha hab
    have hsub_nonneg : 0 ≤ (b - a) / b := div_nonneg (sub_nonneg.mpr hab) (le_of_lt hb)
    have hlog_nonneg : 0 ≤ Real.log (b / a) := by linarith
    have hlog_neg : Real.log (a / b) = -Real.log (b / a) := by
      calc
        Real.log (a / b) = Real.log a - Real.log b :=
          Real.log_div (x := a) (y := b) (ne_of_gt ha) (ne_of_gt hb)
        _ = -(Real.log b - Real.log a) := by ring
        _ = -Real.log (b / a) := by
          rw [Real.log_div (x := b) (y := a) (ne_of_gt hb) (ne_of_gt ha)]
    calc
      |Real.log (a / b)| = |Real.log (b / a)| := by rw [hlog_neg, abs_neg]
      _ = Real.log (b / a) := abs_of_nonneg hlog_nonneg
      _ ≥ |a - b| / max a b := by
        rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab)]
        simpa [neg_sub] using h1
  · have h1 := log_ratio_sub a b hb hba
    have hsub_nonneg : 0 ≤ (a - b) / a := div_nonneg (sub_nonneg.mpr hba) (le_of_lt ha)
    have hlog_nonneg : 0 ≤ Real.log (a / b) := by linarith
    calc
      |Real.log (a / b)| = Real.log (a / b) := abs_of_nonneg hlog_nonneg
      _ ≥ |a - b| / max a b := by
        rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba)]
        exact h1

/-- reindex: Σ_{m∈Ico (n+1) (N+1)} 1/(m-n) = Σ_{j∈Ico 1 (N+1-n)} 1/j -/
lemma sum_inv_sub_right (n N : ℕ) :
    (∑ m ∈ Finset.Ico (n + 1) (N + 1), (((m : ℝ) - (n : ℝ))⁻¹)) =
      ∑ j ∈ Finset.Ico 1 (N + 1 - n), ((j : ℝ))⁻¹ := by
  refine Finset.sum_bij (fun m _ => m - n) ?hi ?i_inj ?i_surj ?h
  · intro m hm
    have hm1 := (Finset.mem_Ico.mp hm).1
    have hm2 := (Finset.mem_Ico.mp hm).2
    simp
    omega
  · intro a1 ha1 a2 ha2 hab
    have ha1n : n + 1 ≤ a1 := (Finset.mem_Ico.mp ha1).1
    omega
  · intro j hj
    refine ⟨n + j, ?mem, ?val⟩
    · have hj1 := (Finset.mem_Ico.mp hj).1
      have hj2 := (Finset.mem_Ico.mp hj).2
      simp
      omega
    · omega
  · intro m hm
    have hmn : n ≤ m := by
      have hm1 := (Finset.mem_Ico.mp hm).1
      omega
    rw [Nat.cast_sub hmn]

/-- distance-to-n sum is O(log): for 1 ≤ n ≤ N, Σ_{m ≤ N, m≠n} 1/|m-n| ≤ 2(1+log N) -/
lemma dist_harm (n N : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, |(n : ℝ) - (m : ℝ)|⁻¹) ≤
      2 * (1 + Real.log (N : ℝ)) := by
  have hset : (Finset.Ico 1 (N + 1)).erase n =
      ((Finset.Ico 1 (N + 1)).filter (fun m => m < n)) ∪
        (Finset.Ico 1 (N + 1)).filter (fun m => n < m) := by
    ext m
    simp
    omega
  have hdisj : Disjoint ((Finset.Ico 1 (N + 1)).filter (fun m => m < n))
      ((Finset.Ico 1 (N + 1)).filter (fun m => n < m)) := by
    rw [Finset.disjoint_filter]
    intro m hm1 hm2
    omega
  have hf1 : (Finset.Ico 1 (N + 1)).filter (fun m => m < n) = Finset.Ico 1 n := by
    ext m
    simp
    omega
  have hf2 : (Finset.Ico 1 (N + 1)).filter (fun m => n < m) = Finset.Ico (n + 1) (N + 1) := by
    ext m
    simp
    omega
  calc
    (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, |(n : ℝ) - (m : ℝ)|⁻¹)
        = ∑ m ∈ ((Finset.Ico 1 (N + 1)).filter (fun m => m < n)) ∪
            (Finset.Ico 1 (N + 1)).filter (fun m => n < m), |(n : ℝ) - (m : ℝ)|⁻¹ := by
          rw [hset]
    _ = ∑ m ∈ (Finset.Ico 1 (N + 1)).filter (fun m => m < n), |(n : ℝ) - (m : ℝ)|⁻¹ +
        ∑ m ∈ (Finset.Ico 1 (N + 1)).filter (fun m => n < m), |(n : ℝ) - (m : ℝ)|⁻¹ := by
          rw [Finset.sum_union hdisj]
    _ = ∑ m ∈ Finset.Ico 1 n, |(n : ℝ) - (m : ℝ)|⁻¹ +
        ∑ m ∈ Finset.Ico (n + 1) (N + 1), |(n : ℝ) - (m : ℝ)|⁻¹ := by
          rw [hf1, hf2]
    _ ≤ (1 + Real.log (n : ℝ)) + (1 + Real.log (↑(N + 1 - n) : ℝ)) := by
          have h1 : (∑ m ∈ Finset.Ico 1 n, |(n : ℝ) - (m : ℝ)|⁻¹) ≤ 1 + Real.log (n : ℝ) := by
            have hrew : (∑ m ∈ Finset.Ico 1 n, |(n : ℝ) - (m : ℝ)|⁻¹) =
                ∑ m ∈ Finset.Ico 1 n, (((n : ℝ) - (m : ℝ))⁻¹) := by
              apply Finset.sum_congr rfl
              intro m hm
              congr 1
              have hmn : m ≤ n := by
                have hm2 := (Finset.mem_Ico.mp hm).2
                omega
              rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ (n : ℝ)))]
            rw [hrew]
            calc
              (∑ m ∈ Finset.Ico 1 n, (((n : ℝ) - (m : ℝ))⁻¹)) = ∑ m ∈ Finset.Ico 1 n, ((m : ℝ))⁻¹ := sum_inv_sub_self n
              _ ≤ 1 + Real.log (n : ℝ) := sum_inv_Ico_le_log n
          have h2 : (∑ m ∈ Finset.Ico (n + 1) (N + 1), |(n : ℝ) - (m : ℝ)|⁻¹) ≤ 1 + Real.log (↑(N + 1 - n) : ℝ) := by
            have hrew : (∑ m ∈ Finset.Ico (n + 1) (N + 1), |(n : ℝ) - (m : ℝ)|⁻¹) =
                ∑ m ∈ Finset.Ico (n + 1) (N + 1), (((m : ℝ) - (n : ℝ))⁻¹) := by
              apply Finset.sum_congr rfl
              intro m hm
              congr 1
              have hnm : n ≤ m := by
                have hm1 := (Finset.mem_Ico.mp hm).1
                omega
              rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ (m : ℝ)))]
              ring
            rw [hrew]
            calc
              (∑ m ∈ Finset.Ico (n + 1) (N + 1), (((m : ℝ) - (n : ℝ))⁻¹)) = ∑ j ∈ Finset.Ico 1 (N + 1 - n), ((j : ℝ))⁻¹ := sum_inv_sub_right n N
              _ ≤ 1 + Real.log (↑(N + 1 - n) : ℝ) := sum_inv_Ico_le_log (N + 1 - n)
          exact add_le_add h1 h2
    _ ≤ 2 * (1 + Real.log (N : ℝ)) := by
          have hln : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
            have hpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
            exact Real.log_le_log hpos (by exact_mod_cast hnN)
          have hlm : Real.log (↑(N + 1 - n) : ℝ) ≤ Real.log (N : ℝ) := by
            have hpos : 0 < (↑(N + 1 - n) : ℝ) := by
              have : 1 ≤ N + 1 - n := by omega
              exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) this)
            have hle : (↑(N + 1 - n) : ℝ) ≤ (N : ℝ) := by
              have : N + 1 - n ≤ N := by omega
              exact_mod_cast this
            exact Real.log_le_log hpos hle
          nlinarith
lemma log_kernel_le (n m N : ℕ) (hn1 : 1 ≤ n) (hm1 : 1 ≤ m) (hnN : n ≤ N) (hmN : m ≤ N) :
    2 / |Real.log ((n : ℝ) / (m : ℝ))| ≤ 2 * (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹ := by
  by_cases hmn : m = n
  · subst m
    simp
  · have hposn0 : (0 : ℕ) < n := by omega
    have hposn : 0 < (n : ℝ) := by exact_mod_cast hposn0
    have hposm0 : (0 : ℕ) < m := by omega
    have hposm : 0 < (m : ℝ) := by exact_mod_cast hposm0
    have hNpos0 : (0 : ℕ) < N := by omega
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos0
    have hge := abs_log_ratio_ge (n : ℝ) (m : ℝ) hposn hposm
    let x : ℝ := |(n : ℝ) - (m : ℝ)|
    have hmaxle : max (n : ℝ) (m : ℝ) ≤ (N : ℝ) := by
      exact max_le (by exact_mod_cast hnN) (by exact_mod_cast hmN)
    have hmaxpos : 0 < max (n : ℝ) (m : ℝ) := lt_of_lt_of_le hposn (le_max_left _ _)
    have hxne : x ≠ 0 := by
      dsimp [x]
      exact abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hmn)))
    have hxpos : 0 < x := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxne)
    have hxNpos : 0 < x / (N : ℝ) := div_pos hxpos hNpos
    have h1N : (N : ℝ)⁻¹ ≤ (max (n : ℝ) (m : ℝ))⁻¹ := by
      exact (inv_le_inv₀ hNpos hmaxpos).mpr hmaxle
    have hge' : x / max (n : ℝ) (m : ℝ) ≤ |Real.log ((n : ℝ) / (m : ℝ))| := by
      simpa [x] using hge
    have hsplit : x / (N : ℝ) ≤ |Real.log ((n : ℝ) / (m : ℝ))| := by
      calc
        x / (N : ℝ) ≤ x / max (n : ℝ) (m : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left h1N (le_of_lt hxpos)
        _ ≤ |Real.log ((n : ℝ) / (m : ℝ))| := hge'
    have hlogpos : 0 < |Real.log ((n : ℝ) / (m : ℝ))| := lt_of_lt_of_le hxNpos hsplit
    calc
      2 / |Real.log ((n : ℝ) / (m : ℝ))| = 2 * |Real.log ((n : ℝ) / (m : ℝ))|⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ 2 * (x / (N : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hlogpos hxNpos).mpr hsplit) (by norm_num)
      _ = 2 * (N : ℝ) * x⁻¹ := by
        field_simp [hNpos.ne']
      _ = 2 * (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹ := by rfl


lemma row_est (n N : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 / |Real.log ((n : ℝ) / (m : ℝ))|) ≤
      8 * (N : ℝ) * Real.log (2 + N) := by
  have hN1 : 1 ≤ N := le_trans hn1 hnN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN1)
  have h1 : (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 / |Real.log ((n : ℝ) / (m : ℝ))|)
      ≤ ∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 * (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹ := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' : m ∈ Finset.Ico 1 (N + 1) := (Finset.mem_erase.mp hm).2
        have hm1n : 1 ≤ m := (Finset.mem_Ico.mp hm').1
        have hmN : m ≤ N := by
          have hm2 := (Finset.mem_Ico.mp hm').2
          omega
        exact log_kernel_le n m N hn1 hm1n hnN hmN
  have h2 : (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 * (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹)
      = (2 * (N : ℝ)) * ∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, |(n : ℝ) - (m : ℝ)|⁻¹ := by
        rw [Finset.mul_sum]
  have hlelog : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (2 + N) := by
    have hpos2N : 0 < (2 + N : ℝ) := by positivity
    have h1log : (1 : ℝ) ≤ Real.log (2 + N) := by
      rw [Real.le_log_iff_exp_le hpos2N]
      have h3 : (3 : ℝ) ≤ (2 + N : ℝ) := by
        have h3n : (3 : ℕ) ≤ 2 + N := by omega
        exact_mod_cast h3n
      exact le_trans (le_of_lt Real.exp_one_lt_three) h3
    have hNlog : Real.log (N : ℝ) ≤ Real.log (2 + N) := by
      exact Real.log_le_log hNpos (by nlinarith)
    nlinarith
  calc
    (∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 / |Real.log ((n : ℝ) / (m : ℝ))|)
        ≤ ∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, 2 * (N : ℝ) * |(n : ℝ) - (m : ℝ)|⁻¹ := h1
    _ = (2 * (N : ℝ)) * ∑ m ∈ (Finset.Ico 1 (N + 1)).erase n, |(n : ℝ) - (m : ℝ)|⁻¹ := h2
    _ ≤ (2 * (N : ℝ)) * (2 * (1 + Real.log (N : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (dist_harm n N hn1 hnN) (by positivity)
    _ = 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) := by ring
    _ ≤ 8 * (N : ℝ) * Real.log (2 + N) := by
        nlinarith [hlelog]
/-- (n : ℂ) ^ (I*t) = exp ((log n * t) * I) for n ≥ 1 -/
lemma cn_pow_exp (n : ℕ) (t : ℝ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (I * t) = Complex.exp ((Real.log (n : ℝ) * t) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.succ_le_iff.mp hn))
  rw [Complex.cpow_def_of_ne_zero hn0]
  congr 1
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.natCast_log]
  rw [hlog]
  ring

lemma cont_cpow_I_mul {n : ℕ} (hn : 1 ≤ n) : Continuous (fun t : ℝ => (n : ℂ) ^ (I * t)) := by
  have hfunext : (fun t : ℝ => (n : ℂ) ^ (I * t)) =
      fun t : ℝ => Complex.exp ((Real.log (n : ℝ) * t) * I) := by
    funext t
    exact cn_pow_exp n t hn
  rw [hfunext]
  fun_prop

lemma cn_pow_conj_exp (n m : ℕ) (t : ℝ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (n : ℂ) ^ (I * t) * conj ((m : ℂ) ^ (I * t)) =
      Complex.exp (((Real.log (n : ℝ) - Real.log (m : ℝ)) * t) * I) := by
  rw [cn_pow_exp n t hn, cn_pow_exp m t hm]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have hconj : conj (((Real.log (m : ℝ) : ℂ) * (t : ℂ)) * I) =
      -(((Real.log (m : ℝ) : ℂ) * (t : ℂ)) * I) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  rw [hconj]
  ring

lemma norm_sq_conj_c (z : ℂ) : (‖z‖ : ℂ) ^ 2 = z * conj z := by
  have hpow : (‖z‖ : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (map_pow (algebraMap ℝ ℂ) ‖z‖ 2)
  rw [hpow]
  calc
    ((‖z‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq z : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) (Complex.normSq_eq_norm_sq z).symm
    _ = conj z * z := Complex.normSq_eq_conj_mul_self
    _ = z * conj z := by rw [mul_comm]

lemma expand_prod (s : Finset ℕ) (b : ℕ → ℂ) (z : ℕ → ℂ) :
    (∑ n ∈ s, b n * z n) * conj (∑ m ∈ s, b m * z m) =
      ∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) * (z n * conj (z m)) := by
  rw [map_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul]
  ring

lemma cont_pair (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (I * t) * conj ((m : ℂ) ^ (I * t))) := by
  exact Continuous.mul (cont_cpow_I_mul hn)
    (Complex.continuous_conj.comp (cont_cpow_I_mul hm))

/-- complex-valued double integral expansion -/
lemma core_identity (N : ℕ) (T : ℝ) (b : ℕ → ℂ) :
    (∫ t in -T..T, (‖∑ n ∈ Finset.Ico 1 (N + 1), b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2)
      = ∑ n ∈ Finset.Ico 1 (N + 1), ∑ m ∈ Finset.Ico 1 (N + 1),
          b n * conj (b m) *
            (∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))) := by
  let s : Finset ℕ := Finset.Ico 1 (N + 1)
  have hpt : ∀ t : ℝ, (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2 =
      ∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) *
        (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))) := by
    intro t
    calc
      (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2
          = (∑ n ∈ s, b n * (n : ℂ) ^ (I * t)) * conj (∑ m ∈ s, b m * (m : ℂ) ^ (I * t)) := by
            rw [norm_sq_conj_c]
      _ = ∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) *
            (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))) := by
            simpa using expand_prod s b (fun n : ℕ => (n : ℂ) ^ (I * t))
  have hint_pair : ∀ n ∈ s, ∀ m ∈ s,
      IntervalIntegrable (fun t : ℝ => ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))
        MeasureTheory.volume (-T) T := by
    intro n hn m hm
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ico.mp hn).1
      omega
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ico.mp hm).1
      omega
    exact Continuous.intervalIntegrable (cont_pair n m hn1 hm1) (-T) T
  have hcont_sum : ∀ n ∈ s,
      Continuous (fun t : ℝ => ∑ m ∈ s, (b n * conj (b m)) *
        (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ico.mp hn).1
      omega
    refine continuous_finsetSum s ?_
    intro m hm
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ico.mp hm).1
      omega
    exact Continuous.mul continuous_const (cont_pair n m hn1 hm1)
  have hcont_inn : ∀ n ∈ s, ∀ m ∈ s,
      Continuous (fun t : ℝ => (b n * conj (b m)) *
        (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
    intro n hn m hm
    exact Continuous.mul continuous_const (cont_pair n m (by have := (Finset.mem_Ico.mp hn).1; omega)
      (by have := (Finset.mem_Ico.mp hm).1; omega))
  calc
    (∫ t in -T..T, (‖∑ n ∈ Finset.Ico 1 (N + 1), b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2)
        = ∫ t in -T..T, (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2 := rfl
    _ = ∫ t in -T..T, (∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) *
            (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact hpt t
    _ = ∑ n ∈ s, ∫ t in -T..T, (∑ m ∈ s, b n * conj (b m) *
            (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
          rw [intervalIntegral.integral_finsetSum]
          intro n hn
          exact Continuous.intervalIntegrable (hcont_sum n hn) (-T) T
    _ = ∑ n ∈ s, ∑ m ∈ s, ∫ t in -T..T, (b n * conj (b m) *
            (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [intervalIntegral.integral_finsetSum]
          intro m hm
          exact Continuous.intervalIntegrable (hcont_inn n hn m hm) (-T) T
    _ = ∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) *
          (∫ t in -T..T, (((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro m hm
          simp

/-- integral of exp(I α t) equals integral of exp(c * t) with c = αI -/
lemma exp_int_eq (T : ℝ) (α : ℝ) :
    (∫ t in -T..T, Complex.exp (((α * t) : ℝ) * I)) =
      (∫ t in -T..T, Complex.exp (((α : ℂ) * I) * (t : ℂ))) := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp
  congr 1
  rw [Complex.ofReal_mul]
  ring

lemma exp_norm_mul_I (T : ℝ) (α : ℝ) :
    ‖Complex.exp (((α : ℂ) * I) * (T : ℂ))‖ = 1 := by
  have harg : Complex.exp (((α : ℂ) * I) * (T : ℂ)) = Complex.exp (((α * T : ℝ) : ℂ) * I) := by
    congr 1
    calc
      ((α : ℂ) * I) * (T : ℂ) = ((α : ℂ) * (T : ℂ)) * I := by ring
      _ = ((α * T : ℝ) : ℂ) * I := by rw [← Complex.ofReal_mul]
  rw [harg]
  exact norm_exp_ofReal_mul_I (α * T)

/-- norm bound for the oscillatory integral -/
lemma exp_int_abs (T : ℝ) {α : ℝ} (hα : α ≠ 0) :
    ‖(∫ t in -T..T, Complex.exp (((α * t) : ℝ) * I))‖ ≤ 2 / |α| := by
  have hc : ((α : ℂ) * I) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hα
    · simp
  rw [exp_int_eq T α]
  rw [integral_exp_mul_complex hc]
  have hnormT : ‖Complex.exp (((α : ℂ) * I) * (T : ℂ))‖ = 1 := exp_norm_mul_I T α
  have hnormT' : ‖Complex.exp (((α : ℂ) * I) * ((-T : ℝ) : ℂ))‖ = 1 := exp_norm_mul_I (-T) α
  have hnormc : ‖((α : ℂ) * I)‖ = |α| := by
    rw [norm_mul, Complex.norm_I, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖(Complex.exp (((α : ℂ) * I) * (T : ℂ)) - Complex.exp (((α : ℂ) * I) * ((-T : ℝ) : ℂ)))
        / ((α : ℂ) * I)‖
        = ‖Complex.exp (((α : ℂ) * I) * (T : ℂ)) - Complex.exp (((α : ℂ) * I) * ((-T : ℝ) : ℂ))‖ / ‖((α : ℂ) * I)‖ := by
          rw [norm_div]
    _ = ‖Complex.exp (((α : ℂ) * I) * (T : ℂ)) - Complex.exp (((α : ℂ) * I) * ((-T : ℝ) : ℂ))‖ / |α| := by
          rw [hnormc]
    _ ≤ (‖Complex.exp (((α : ℂ) * I) * (T : ℂ))‖ + ‖Complex.exp (((α : ℂ) * I) * ((-T : ℝ) : ℂ))‖)
          / |α| := by
          gcongr
          exact norm_sub_le _ _
    _ = 2 / |α| := by
          rw [hnormT, hnormT']
          norm_num

lemma pair_int_eq (T : ℝ) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))) =
      ∫ t in -T..T, Complex.exp (((Real.log (n : ℝ) - Real.log (m : ℝ)) * t) * I) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact cn_pow_conj_exp n m t hn hm

lemma z_norm_one {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ (I * t)‖ = 1 := by
  rw [cn_pow_exp n t hn]
  rw [← Complex.ofReal_mul]
  exact norm_exp_ofReal_mul_I (Real.log (n : ℝ) * t)

/-- ‖∫ z_n conj z_m‖ ≤ 2T for n,m ≥ 1, T ≥ 0 -/
lemma jint_norm_le_T (T : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hT : 0 ≤ T) :
    ‖(∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))‖ ≤ 2 * T := by
  have hnorm : ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ), t ∈ Set.uIoc (-T) T →
      ‖((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))‖ ≤ 1 := by
    filter_upwards with t ht
    calc
      ‖((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))‖
          ≤ ‖(n : ℂ) ^ (I * t)‖ * ‖conj ((m : ℂ) ^ (I * t))‖ := norm_mul_le _ _
      _ = ‖(n : ℂ) ^ (I * t)‖ * ‖(m : ℂ) ^ (I * t)‖ := by rw [norm_conj]
      _ = 1 := by
        rw [z_norm_one hn t, z_norm_one hm t]
        norm_num
      _ ≤ 1 := le_rfl
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae hnorm
  -- hb : ‖∫ x in -T..T, f x‖ ≤ 1 * |T - (-T)|
  have hTsub : T - (-T) = 2 * T := by ring
  calc
    ‖(∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))‖ ≤ 1 * |T - -T| := hb
    _ = |2 * T| := by rw [hTsub, one_mul]
    _ = 2 * T := abs_of_nonneg (mul_nonneg (by norm_num) hT)

/-- ‖∫ z_n conj z_m‖ ≤ 2/|log(n/m)| for m ≠ n -/
lemma jint_norm_le (T : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    ‖(∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t)))‖ ≤
      2 / |Real.log ((n : ℝ) / (m : ℝ))| := by
  rw [pair_int_eq T n m hn hm]
  have hposn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hposm : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hα : Real.log (n : ℝ) - Real.log (m : ℝ) ≠ 0 := by
    intro h
    have hlogeq : Real.log (n : ℝ) = Real.log (m : ℝ) := sub_eq_zero.mp h
    have hn' : (n : ℝ) = (m : ℝ) := by
      rw [← Real.exp_log hposn, ← Real.exp_log hposm, hlogeq]
    have hne : n = m := by exact_mod_cast hn'
    exact hmn hne.symm
  have hb := exp_int_abs T hα
  -- hb : ‖∫ exp (((log n - log m) * t) * I)‖ ≤ 2/|log n - log m|
  have hratio : |Real.log (n : ℝ) - Real.log (m : ℝ)| = |Real.log ((n : ℝ) / (m : ℝ))| := by
    congr 1
    rw [Real.log_div (ne_of_gt hposn) (ne_of_gt hposm)]
  simpa [hratio] using hb


lemma abs_log_ratio_symm (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |Real.log ((n : ℝ) / (m : ℝ))| = |Real.log ((m : ℝ) / (n : ℝ))| := by
  have hposn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hposm : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  calc
    |Real.log ((n : ℝ) / (m : ℝ))| = |-(Real.log ((m : ℝ) / (n : ℝ)))| := by
      congr 1
      rw [Real.log_div (x := n) (y := m) (ne_of_gt hposn) (ne_of_gt hposm),
        Real.log_div (x := m) (y := n) (ne_of_gt hposm) (ne_of_gt hposn)]
      ring
    _ = |Real.log ((m : ℝ) / (n : ℝ))| := by rw [abs_neg]


/-- col bound: Σ_{n ≤ N, n≠m} 2/|log(n/m)| ≤ 8 N log(2+N) -/
lemma col_est (m N : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ n ∈ (Finset.Ico 1 (N + 1)).erase m, 2 / |Real.log ((n : ℝ) / (m : ℝ))|) ≤
      8 * (N : ℝ) * Real.log (2 + N) := by
  have hrow := row_est m N hm1 hmN
  have hrew : (∑ n ∈ (Finset.Ico 1 (N + 1)).erase m, 2 / |Real.log ((n : ℝ) / (m : ℝ))|) =
      (∑ n ∈ (Finset.Ico 1 (N + 1)).erase m, 2 / |Real.log ((m : ℝ) / (n : ℝ))|) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ∈ Finset.Ico 1 (N + 1) := (Finset.mem_erase.mp hn).2
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn').1
    rw [abs_log_ratio_symm n m hn1 hm1]
  rwa [hrew]

/-- pointwise: x y ≤ x^2 + y^2 -/
lemma mul_le_sq_add_sq (x y : ℝ) : x * y ≤ x ^ 2 + y ^ 2 := by
  have h : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have h2 : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith
  have h3 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  nlinarith

/-- the off-diagonal double sum is O(N log N) Σ |b|^2 -/
lemma cross_bound (N : ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico 1 (N + 1), ∑ m ∈ (Finset.Ico 1 (N + 1)).erase n,
        ‖b n‖ * ‖b m‖ * (2 / |Real.log ((n : ℝ) / (m : ℝ))|))
      ≤ 2 * (8 * (N : ℝ) * Real.log (2 + N)) * ∑ n ∈ Finset.Ico 1 (N + 1), ‖b n‖ ^ 2 := by
  let s : Finset ℕ := Finset.Ico 1 (N + 1)
  let x : ℕ → ℝ := fun n => ‖b n‖
  let w : ℕ → ℕ → ℝ := fun n m => 2 / |Real.log ((n : ℝ) / (m : ℝ))|
  let P : ℝ := 8 * (N : ℝ) * Real.log (2 + N)
  have hmem1 : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    have := (Finset.mem_Ico.mp hn).1
    omega
  have hmemN : ∀ n ∈ s, n ≤ N := by
    intro n hn
    have := (Finset.mem_Ico.mp hn).2
    omega
  have hw0 : ∀ n m, 0 ≤ w n m := by
    intro n m
    dsimp [w]
    exact div_nonneg (by norm_num) (abs_nonneg _)
  have hrow : ∀ n ∈ s, (∑ m ∈ s.erase n, w n m) ≤ P := by
    intro n hn
    dsimp [w, P]
    exact row_est n N (hmem1 n hn) (hmemN n hn)
  have hcol : ∀ m ∈ s, (∑ n ∈ s, w n m) ≤ P := by
    intro m hm
    have hfull : (∑ n ∈ s, w n m) = ∑ n ∈ s.erase m, w n m := by
      calc
        (∑ n ∈ s, w n m) = (∑ n ∈ s.erase m, w n m) + w m m := by
          exact (Finset.sum_erase_add s (fun n => w n m) hm).symm
        _ = ∑ n ∈ s.erase m, w n m := by simp [w]
    rw [hfull]
    dsimp [w, P]
    exact col_est m N (hmem1 m hm) (hmemN m hm)
  calc
    (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * w n m)
        ≤ ∑ n ∈ s, ∑ m ∈ s.erase n, (x n ^ 2 + x m ^ 2) * w n m := by
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro m hm
          exact mul_le_mul_of_nonneg_right (mul_le_sq_add_sq (x n) (x m)) (hw0 n m)
    _ = (∑ n ∈ s, ∑ m ∈ s.erase n, x n ^ 2 * w n m) +
        (∑ n ∈ s, ∑ m ∈ s.erase n, x m ^ 2 * w n m) := by
          -- Σ (a + b) w = Σ a w + Σ b w
          simp [add_mul, Finset.sum_add_distrib]
    _ ≤ P * (∑ n ∈ s, x n ^ 2) + P * (∑ n ∈ s, x n ^ 2) := by
          -- first: factor out x n² and use row bound; second: extend to rectangle, swap, use col bound
          have hfirst : (∑ n ∈ s, ∑ m ∈ s.erase n, x n ^ 2 * w n m) ≤ P * (∑ n ∈ s, x n ^ 2) := by
            calc
              (∑ n ∈ s, ∑ m ∈ s.erase n, x n ^ 2 * w n m)
                  = ∑ n ∈ s, x n ^ 2 * (∑ m ∈ s.erase n, w n m) := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    rw [Finset.mul_sum]
              _ ≤ ∑ n ∈ s, x n ^ 2 * P := by
                    apply Finset.sum_le_sum
                    intro n hn
                    exact mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
              _ = P * (∑ n ∈ s, x n ^ 2) := by
                    rw [Finset.mul_sum]
                    simp [mul_comm, mul_left_comm, mul_assoc]
          have hsecond : (∑ n ∈ s, ∑ m ∈ s.erase n, x m ^ 2 * w n m) ≤ P * (∑ n ∈ s, x n ^ 2) := by
            calc
              (∑ n ∈ s, ∑ m ∈ s.erase n, x m ^ 2 * w n m)
                  ≤ ∑ n ∈ s, ∑ m ∈ s, x m ^ 2 * w n m := by
                    apply Finset.sum_le_sum
                    intro n hn
                    have hsplit : (∑ m ∈ s, x m ^ 2 * w n m) =
                        (∑ m ∈ s.erase n, x m ^ 2 * w n m) + x n ^ 2 * w n n := by
                      exact (Finset.sum_erase_add s (fun m => x m ^ 2 * w n m) hn).symm
                    have hf : 0 ≤ x n ^ 2 * w n n := mul_nonneg (sq_nonneg _) (hw0 n n)
                    rw [hsplit]
                    linarith
              _ = ∑ m ∈ s, x m ^ 2 * (∑ n ∈ s, w n m) := by
                    -- swap rectangle sums and factor x_m²
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro m hm
                    rw [Finset.mul_sum]
              _ ≤ P * (∑ n ∈ s, x n ^ 2) := by
                    calc
                      (∑ m ∈ s, x m ^ 2 * (∑ n ∈ s, w n m)) ≤ ∑ m ∈ s, x m ^ 2 * P := by
                        apply Finset.sum_le_sum
                        intro m hm
                        exact mul_le_mul_of_nonneg_left (hcol m hm) (sq_nonneg _)
                      _ = P * (∑ m ∈ s, x m ^ 2) := by
                        rw [Finset.mul_sum]
                        simp [mul_comm, mul_left_comm, mul_assoc]
                      _ = P * (∑ n ∈ s, x n ^ 2) := by rfl
          linarith
    _ = 2 * P * (∑ n ∈ s, x n ^ 2) := by ring

/-- main mean-value estimate for Dirichlet polynomials over n = 1..N -/
lemma core_bound (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (b : ℕ → ℂ) :
    (∫ t in -T..T, ‖∑ n ∈ Finset.Ico 1 (N + 1), b n * (n : ℂ) ^ (I * t)‖ ^ 2)
      ≤ (2 * T + 16 * (N : ℝ) * Real.log (2 + N)) *
          ∑ n ∈ Finset.Ico 1 (N + 1), ‖b n‖ ^ 2 := by
  let s : Finset ℕ := Finset.Ico 1 (N + 1)
  let x : ℕ → ℝ := fun n => ‖b n‖
  let w : ℕ → ℕ → ℝ := fun n m => 2 / |Real.log ((n : ℝ) / (m : ℝ))|
  let J : ℕ → ℕ → ℂ := fun n m => ∫ t in -T..T, ((n : ℂ) ^ (I * t)) * conj ((m : ℂ) ^ (I * t))
  let R : ℝ := ∫ t in -T..T, ‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ ^ 2
  let II : ℂ := ∫ t in -T..T, (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2
  have hnonneg : 0 ≤ R := by
    dsimp [R]
    exact intervalIntegral.integral_nonneg (by linarith) (fun u hu => sq_nonneg _)
  have hII : II = (R : ℂ) := by
    dsimp [R, II]
    have hfun : (fun t : ℝ => (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ : ℂ) ^ 2) =
        fun t : ℝ => (((‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖ ^ 2 : ℝ) : ℂ)) := by
      funext t
      exact (map_pow (algebraMap ℝ ℂ) (‖∑ n ∈ s, b n * (n : ℂ) ^ (I * t)‖) 2).symm
    rw [hfun]
    rw [intervalIntegral.integral_ofReal]
  have hR_eq : R = ‖II‖ := by
    have hcast : ‖(R : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [hII]
    exact hcast.symm
  have hmem1 : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    have := (Finset.mem_Ico.mp hn).1
    omega
  have hmemN : ∀ n ∈ s, n ≤ N := by
    intro n hn
    have := (Finset.mem_Ico.mp hn).2
    omega
  have hJ : ‖II‖ ≤ ∑ n ∈ s, ∑ m ∈ s, x n * x m * ‖J n m‖ := by
    have hid' : II = ∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) * J n m := by
      dsimp [II, J]
      simpa using (core_identity N T b)
    rw [hid']
    calc
      ‖∑ n ∈ s, ∑ m ∈ s, b n * conj (b m) * J n m‖
          ≤ ∑ n ∈ s, ‖∑ m ∈ s, b n * conj (b m) * J n m‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖b n * conj (b m) * J n m‖ := by
            apply Finset.sum_le_sum
            intro n hn
            exact norm_sum_le _ _
      _ = ∑ n ∈ s, ∑ m ∈ s, x n * x m * ‖J n m‖ := by
            dsimp [x]
            apply Finset.sum_congr rfl
            intro n hn
            apply Finset.sum_congr rfl
            intro m hm
            rw [norm_mul, norm_mul, norm_conj]
  have hsplit : (∑ n ∈ s, ∑ m ∈ s, x n * x m * ‖J n m‖) =
      (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * ‖J n m‖) +
        (∑ n ∈ s, x n * x n * ‖J n n‖) := by
    calc
      (∑ n ∈ s, ∑ m ∈ s, x n * x m * ‖J n m‖)
          = ∑ n ∈ s, ((∑ m ∈ s.erase n, x n * x m * ‖J n m‖) + x n * x n * ‖J n n‖) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [← Finset.sum_erase_add s (fun m => x n * x m * ‖J n m‖) hn]
      _ = (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * ‖J n m‖) +
          (∑ n ∈ s, x n * x n * ‖J n n‖) := by
            rw [Finset.sum_add_distrib]
  have hdiagb : (∑ n ∈ s, x n * x n * ‖J n n‖) ≤ (2 * T) * (∑ n ∈ s, x n ^ 2) := by
    calc
      (∑ n ∈ s, x n * x n * ‖J n n‖) ≤ ∑ n ∈ s, x n ^ 2 * (2 * T) := by
        apply Finset.sum_le_sum
        intro n hn
        have hJn : ‖J n n‖ ≤ 2 * T := by
          dsimp [J]
          exact jint_norm_le_T T (hmem1 n hn) (hmem1 n hn) hT
        have hx : 0 ≤ x n ^ 2 := sq_nonneg _
        have hx2 : x n * x n = x n ^ 2 := by ring
        nlinarith
      _ = (2 * T) * (∑ n ∈ s, x n ^ 2) := by
        rw [← Finset.sum_mul]
        exact mul_comm (∑ n ∈ s, x n ^ 2) (2 * T)
  have hcrossb : (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * w n m) ≤
      2 * (8 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) := by
    dsimp [s, x, w]
    exact cross_bound N b
  have hcrossJ : (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * ‖J n m‖) ≤
      ∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * w n m := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    have hmn : m ≠ n := (Finset.mem_erase.mp hm).1
    have hJ : ‖J n m‖ ≤ w n m := by
      dsimp [J, w]
      exact jint_norm_le T (hmem1 n hn) (hmem1 m (Finset.mem_erase.mp hm).2) hmn
    have hx : 0 ≤ x n * x m := by
      dsimp [x]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hJ hx
  have hmain : ‖II‖ ≤ 2 * (8 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) +
      (2 * T) * (∑ n ∈ s, x n ^ 2) := by
    calc
      ‖II‖ ≤ ∑ n ∈ s, ∑ m ∈ s, x n * x m * ‖J n m‖ := hJ
      _ = (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * ‖J n m‖) +
          (∑ n ∈ s, x n * x n * ‖J n n‖) := hsplit
      _ ≤ (∑ n ∈ s, ∑ m ∈ s.erase n, x n * x m * w n m) +
          (2 * T) * (∑ n ∈ s, x n ^ 2) := by
            exact add_le_add hcrossJ hdiagb
      _ ≤ 2 * (8 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) +
          (2 * T) * (∑ n ∈ s, x n ^ 2) := by
            exact add_le_add hcrossb (le_rfl)
  have hR : R ≤ (2 * T + 16 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) := by
    rw [hR_eq]
    have hc : 2 * (8 * (N : ℝ) * Real.log (2 + N)) = 16 * (N : ℝ) * Real.log (2 + N) := by ring
    calc
      ‖II‖ ≤ 2 * (8 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) +
          (2 * T) * (∑ n ∈ s, x n ^ 2) := hmain
      _ = (2 * T + 16 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ s, x n ^ 2) := by
            rw [hc]
            rw [add_comm]
            rw [← add_mul]
  simpa [s, x] using hR

lemma sum_range_split (N : ℕ) {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (∑ n ∈ Finset.range (N + 1), f n) = f 0 + ∑ n ∈ Finset.Ico 1 (N + 1), f n := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have htop : (∑ n ∈ Finset.Ico 1 ((N + 1) + 1), f n) = (∑ n ∈ Finset.Ico 1 (N + 1), f n) + f (N + 1) := by
        rw [Finset.sum_Ico_succ_top]
        norm_num
      calc
        (∑ n ∈ Finset.range ((N + 1) + 1), f n)
            = (∑ n ∈ Finset.range (N + 1), f n) + f (N + 1) := by rw [Finset.sum_range_succ]
        _ = (f 0 + ∑ n ∈ Finset.Ico 1 (N + 1), f n) + f (N + 1) := by rw [ih]
        _ = f 0 + ((∑ n ∈ Finset.Ico 1 (N + 1), f n) + f (N + 1)) := by ac_rfl
        _ = f 0 + ∑ n ∈ Finset.Ico 1 ((N + 1) + 1), f n := by rw [← htop]

/-- a.e. equality: the n = 0 term of n^it vanishes for t ≠ 0 -/
lemma integral_range_eq_Ico (T : ℝ) (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in -T..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (I * t)‖ ^ 2)
      = (∫ t in -T..T, ‖∑ n ∈ Finset.Ico 1 (N + 1), a n * (n : ℂ) ^ (I * t)‖ ^ 2) := by
  apply intervalIntegral.integral_congr_ae
  have ae_ne0 : ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ), t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : ({t : ℝ | ¬t ≠ 0} : Set ℝ) = {0} := by
      ext x
      simp
    rw [hset]
    simp
  filter_upwards [ae_ne0] with t htne htmem
  have hS : (∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (I * t)) =
      ∑ n ∈ Finset.Ico 1 (N + 1), a n * (n : ℂ) ^ (I * t) := by
    have hz0 : (0 : ℂ) ^ (I * t) = 0 := by
      exact Complex.zero_cpow (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast htne))
    calc
      (∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (I * t))
          = a 0 * (↑(0 : ℕ) : ℂ) ^ (I * t) + ∑ n ∈ Finset.Ico 1 (N + 1), a n * (n : ℂ) ^ (I * t) := by
            rw [sum_range_split N (fun n => a n * (n : ℂ) ^ (I * t))]
      _ = ∑ n ∈ Finset.Ico 1 (N + 1), a n * (n : ℂ) ^ (I * t) := by
            simp [hz0]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hS

/-- Mean value theorem for Dirichlet polynomials: for complex `aₙ` supported on
`1 ≤ n ≤ N`, `∫_{-T}^{T} |∑ aₙ n^{it}|² dt` is `O((T + N log(2+N))·∑|aₙ|²)`. -/
theorem dirichlet_mean_value :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (N : ℕ) (T : ℝ) (a : ℕ → ℂ), 1 ≤ T →
        (∫ t in -T..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (I * t)‖ ^ 2)
          ≤ C₂ * (T + (N : ℝ) * Real.log (2 + N)) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  refine ⟨32, by norm_num, ?_⟩
  intro N T a hT
  have hT0 : 0 ≤ T := by linarith
  have hS0 : (∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) =
      ‖a 0‖ ^ 2 + (∑ n ∈ Finset.Ico 1 (N + 1), ‖a n‖ ^ 2) := by
    rw [sum_range_split N (fun n => ‖a n‖ ^ 2)]
  have hlog : 0 ≤ Real.log (2 + N) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (by omega : (1 : ℕ) ≤ 2 + N)
  have hcoef : 0 ≤ 2 * T + 16 * (N : ℝ) * Real.log (2 + N) := by
    nlinarith [hT0, hlog]
  have hcoef2 : 2 * T + 16 * (N : ℝ) * Real.log (2 + N) ≤ 32 * (T + (N : ℝ) * Real.log (2 + N)) := by
    nlinarith [hT0, hlog]
  calc
    (∫ t in -T..T, ‖∑ n ∈ Finset.range (N + 1), a n * (n : ℂ) ^ (I * t)‖ ^ 2)
        = (∫ t in -T..T, ‖∑ n ∈ Finset.Ico 1 (N + 1), a n * (n : ℂ) ^ (I * t)‖ ^ 2) :=
          integral_range_eq_Ico T N a
    _ ≤ (2 * T + 16 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ Finset.Ico 1 (N + 1), ‖a n‖ ^ 2) :=
          core_bound N T hT0 a
    _ ≤ (2 * T + 16 * (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by
          rw [hS0]
          nlinarith [hcoef, sq_nonneg (‖a 0‖)]
    _ ≤ 32 * (T + (N : ℝ) * Real.log (2 + N)) * (∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by
          have hS : 0 ≤ (∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by
            exact Finset.sum_nonneg (fun n hn => sq_nonneg _)
          nlinarith [hcoef2, hS]
