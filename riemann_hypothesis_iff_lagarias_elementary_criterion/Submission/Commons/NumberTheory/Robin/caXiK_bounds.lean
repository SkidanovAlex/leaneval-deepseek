import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Commons.NumberTheory.Robin

open Set

/-- The function `t ↦ log (1 + 1/t) / log t` is strictly antitone on `(1, ∞)`. -/
private lemma log_one_add_inv_div_log_strictAntiOn :
    StrictAntiOn (fun t : ℝ => Real.log (1 + 1/t) / Real.log t) (Ioi 1) := by
  intro a ha b hb hab
  have ha0 : (0:ℝ) < a := lt_trans zero_lt_one ha
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hla : 0 < Real.log a := Real.log_pos ha
  have hNa : 0 < Real.log (1 + 1/a) := by
    apply Real.log_pos
    have : (0:ℝ) < 1/a := by positivity
    linarith
  have hlogab : Real.log a < Real.log b := Real.log_lt_log ha0 hab
  have hnab : Real.log (1 + 1/b) < Real.log (1 + 1/a) := by
    apply Real.log_lt_log
    · have : (0:ℝ) < 1/b := by positivity
      linarith
    · have : 1/b < 1/a := one_div_lt_one_div_of_lt ha0 hab
      linarith
  calc Real.log (1 + 1/b) / Real.log b
      < Real.log (1 + 1/a) / Real.log b := div_lt_div_of_pos_right hnab hlb
    _ < Real.log (1 + 1/a) / Real.log a := div_lt_div_of_pos_left hNa hla hlogab

/-- `x^k ≤ ∑_{i=0}^{k-1} x^{i+1}` for `x > 1`. -/
private lemma pow_le_sum (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 2 ≤ k) :
    x^k ≤ Finset.sum (Finset.range k) (fun i => x^(i+1)) := by
  have hmem : k-1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (s := Finset.range k) (f := fun i => x^(i+1)) (a := k-1)
      (fun i _ => by positivity) hmem
  have hidx : k - 1 + 1 = k := by omega
  simpa [hidx] using h

/-- `∑_{i=0}^{k-1} x^{i+1} ≤ k·x^k` for `x > 1`. -/
private lemma sum_le (x : ℝ) (hx : 1 < x) (k : ℕ) :
    Finset.sum (Finset.range k) (fun i => x^(i+1)) ≤ (k:ℝ) * x^k := by
  have hx1 : (1:ℝ) ≤ x := le_of_lt hx
  calc Finset.sum (Finset.range k) (fun i => x^(i+1))
      ≤ Finset.sum (Finset.range k) (fun _ => x^k) := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i+1 ≤ k := by have := Finset.mem_range.mp hi; omega
        exact pow_le_pow_right₀ hx1 hik
    _ = (k:ℝ) * x^k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `∑_{i=0}^{k-1} x^{i+1} > 0` for `x > 1`, `k ≥ 2`. -/
private lemma sum_pos (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 2 ≤ k) :
    0 < Finset.sum (Finset.range k) (fun i => x^(i+1)) := by
  apply Finset.sum_pos
  · intro i _; positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

/-- `log w ≤ w · log k` for `1 < w` and `2 ≤ k`. -/
private lemma log_le_mul_log (w : ℝ) (hw : 1 < w) (k : ℕ) (hk : 2 ≤ k) :
    Real.log w ≤ w * Real.log k := by
  have hw0 : 0 < w := lt_trans zero_lt_one hw
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0:ℝ) < k := by linarith
  have hs : (-1:ℝ) ≤ (k:ℝ) - 1 := by linarith
  have hw1 : (1:ℝ) ≤ w := le_of_lt hw
  have hbern := one_add_mul_self_le_rpow_one_add (s := (k:ℝ)-1) hs (p := w) hw1
  have hk_eq : 1 + ((k:ℝ)-1) = (k:ℝ) := by ring
  rw [hk_eq] at hbern
  have hwle : w ≤ 1 + w * ((k:ℝ)-1) := by nlinarith [hw0, hk2]
  have hkw : w ≤ (k:ℝ) ^ w := le_trans hwle hbern
  calc Real.log w ≤ Real.log ((k:ℝ) ^ w) := Real.log_le_log hw0 hkw
    _ = w * Real.log k := Real.log_rpow hk1 w

/-- **Lower sandwich.** For `x > 1`, `k ≥ 2`:
`g(x^k) ≤ log(1 + 1/∑_{i<k} x^{i+1}) / log x`, where `g(t) = log(1+1/t)/log t`. -/
private lemma lower_sandwich (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 2 ≤ k) :
    Real.log (1 + 1/x^k) / Real.log (x^k) ≤
      Real.log (1 + 1/Finset.sum (Finset.range k) (fun i => x^(i+1))) / Real.log x := by
  have hxl : 0 < Real.log x := Real.log_pos hx
  have hy1 : 1 < x^k := one_lt_pow₀ hx (by omega)
  set S := Finset.sum (Finset.range k) (fun i => x^(i+1)) with hS
  have hSpos : 0 < S := by rw [hS]; exact sum_pos x hx k hk
  have hSle : S ≤ (k:ℝ)*x^k := by rw [hS]; exact sum_le x hx k
  have hkey : (1 + 1/x^k)^(1/(k:ℝ)) ≤ 1 + 1/S := by
    have hkpos : (0:ℝ) < k := by positivity
    have hlt : (1:ℝ)/(k:ℝ) < 1 := by rw [div_lt_one hkpos]; exact_mod_cast (show 1 < k by omega)
    have hs0 : (0:ℝ) < 1/x^k := by positivity
    have hsne : (1/x^k : ℝ) ≠ 0 := ne_of_gt hs0
    have hbern := rpow_one_add_lt_one_add_mul_self (s := 1/x^k) (by linarith) hsne
        (p := 1/(k:ℝ)) (by positivity) hlt
    have heq : (1 + 1/x^k)^(1/(k:ℝ)) < 1 + 1/((k:ℝ)*x^k) := by
      convert hbern using 1
      field_simp
    have hmono : 1/((k:ℝ)*x^k) ≤ 1/S := one_div_le_one_div_of_le (by positivity) hSle
    linarith [heq.le, hmono]
  have hlog : (1/(k:ℝ)) * Real.log (1 + 1/x^k) ≤ Real.log (1 + 1/S) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + 1/x^k) _) hkey
    rwa [Real.log_rpow (by positivity : (0:ℝ) < 1 + 1/x^k)] at this
  have hlog' : Real.log (1 + 1/x^k) / (k:ℝ) ≤ Real.log (1 + 1/S) := by
    rw [div_eq_mul_inv]
    simpa [one_mul, mul_comm] using hlog
  have hA : Real.log (1 + 1/x^k) ≤ Real.log (1 + 1/S) * (k:ℝ) :=
    (div_le_iff₀ (by positivity : (0:ℝ) < k)).mp hlog'
  rw [Real.log_pow]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ)*Real.log x) hxl]
  nlinarith [hA, hxl]

/-- **Upper sandwich (numeric core).** For `k ≥ 2` and `y > k`:
`k·g(y) ≤ g(y/k)`, where `g(t) = log(1+1/t)/log t`. -/
private lemma kg_le (y : ℝ) (k : ℕ) (hk : 2 ≤ k) (hy : (k:ℝ) < y) :
    (k:ℝ) * (Real.log (1 + 1/y) / Real.log y) ≤
      Real.log (1 + 1/(y/(k:ℝ))) / Real.log (y/(k:ℝ)) := by
  set w := y/(k:ℝ) with hw
  have hkpos : (0:ℝ) < k := by positivity
  have hk2 : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hy0 : 0 < y := lt_trans hkpos hy
  have hy1 : 1 < y := lt_trans hk2 hy
  have hyl : 0 < Real.log y := Real.log_pos hy1
  have hw1 : 1 < w := by rw [hw, lt_div_iff₀ hkpos]; linarith
  have hwl : 0 < Real.log w := Real.log_pos hw1
  have hlogw : Real.log w = Real.log y - Real.log k := by
    rw [hw, Real.log_div (ne_of_gt hy0) (ne_of_gt hkpos)]
  have hpos : 0 < Real.log y - Real.log k := by rw [← hlogw]; exact hwl
  have hA : Real.log (1 + 1/y) ≤ 1/y := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/y by positivity)
    linarith
  have hB : (k:ℝ)/(y + k) ≤ Real.log (1 + 1/w) := by
    have hT : (0:ℝ) < 1 + 1/w := by positivity
    have hb := Real.one_sub_inv_le_log_of_pos hT
    have heq : (1:ℝ) - (1 + 1/w)⁻¹ = (k:ℝ)/(y + k) := by
      rw [hw]; field_simp; ring
    linarith [hb]
  have hC : (y + (k:ℝ)) * (Real.log y - Real.log k) ≤ y * Real.log y := by
    have hkey : Real.log y - Real.log k ≤ w * Real.log k := by
      have := log_le_mul_log w hw1 k hk
      rwa [hlogw] at this
    have hkey2 : (k:ℝ) * (Real.log y - Real.log k) ≤ y * Real.log k := by
      have h1 := mul_le_mul_of_nonneg_left hkey (le_of_lt hkpos)
      have h2 : (k:ℝ) * (w * Real.log k) = y * Real.log k := by rw [hw]; field_simp
      rwa [h2] at h1
    nlinarith [hkey2]
  have hstep1 : (k:ℝ) * (Real.log (1 + 1/y) / Real.log y) ≤ (k:ℝ)/(y * Real.log y) := by
    have h1 : Real.log (1 + 1/y) / Real.log y ≤ (1/y)/Real.log y :=
      div_le_div_of_nonneg_right hA (le_of_lt hyl)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hkpos)
    have h3 : (k:ℝ) * ((1/y)/Real.log y) = (k:ℝ)/(y * Real.log y) := by field_simp
    rwa [h3] at h2
  have hstep2 : (k:ℝ)/(y * Real.log y) ≤ (k:ℝ)/((y + k) * (Real.log y - Real.log k)) := by
    have hden1 : 0 < y * Real.log y := mul_pos hy0 hyl
    have hden2 : 0 < (y + k) * (Real.log y - Real.log k) := mul_pos (by linarith) hpos
    rw [div_le_div_iff₀ hden1 hden2]
    have := mul_le_mul_of_nonneg_left hC (le_of_lt hkpos)
    linarith [this]
  have hstep3 : (k:ℝ)/((y + k) * (Real.log y - Real.log k)) ≤
      Real.log (1 + 1/w) / Real.log w := by
    have hd : (k:ℝ)/((y + k) * (Real.log y - Real.log k)) =
        ((k:ℝ)/(y+k))/(Real.log y - Real.log k) := by field_simp
    rw [hd, hlogw]
    exact div_le_div_of_nonneg_right hB (le_of_lt hpos)
  calc (k:ℝ) * (Real.log (1 + 1/y) / Real.log y)
      ≤ (k:ℝ)/(y * Real.log y) := hstep1
    _ ≤ (k:ℝ)/((y + k) * (Real.log y - Real.log k)) := hstep2
    _ ≤ Real.log (1 + 1/w) / Real.log w := hstep3

/-- **Upper sandwich.** For `x > 1`, `k ≥ 2`, `x^k > k`:
`log(1 + 1/∑_{i<k} x^{i+1}) / log x ≤ g(x^k/k)`. -/
private lemma upper_sandwich (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 2 ≤ k) (hyk : (k:ℝ) < x^k) :
    Real.log (1 + 1/Finset.sum (Finset.range k) (fun i => x^(i+1))) / Real.log x ≤
      Real.log (1 + 1/(x^k/(k:ℝ))) / Real.log (x^k/(k:ℝ)) := by
  have hy0 : 0 < x^k := by positivity
  have hxl : 0 < Real.log x := Real.log_pos hx
  set S := Finset.sum (Finset.range k) (fun i => x^(i+1)) with hS
  have hSle : x^k ≤ S := by rw [hS]; exact pow_le_sum x hx k hk
  have hSpos : 0 < S := by rw [hS]; exact sum_pos x hx k hk
  have hlogS : Real.log (1 + 1/S) ≤ Real.log (1 + 1/x^k) := by
    apply Real.log_le_log
    · positivity
    · have := one_div_le_one_div_of_le hy0 hSle
      linarith
  have hmid : Real.log (1 + 1/x^k)/Real.log x =
      (k:ℝ) * (Real.log (1 + 1/x^k)/Real.log (x^k)) := by
    rw [Real.log_pow]
    field_simp
  calc Real.log (1 + 1/S)/Real.log x
      ≤ Real.log (1 + 1/x^k)/Real.log x := div_le_div_of_nonneg_right hlogS (le_of_lt hxl)
    _ = (k:ℝ) * (Real.log (1 + 1/x^k)/Real.log (x^k)) := hmid
    _ ≤ Real.log (1 + 1/(x^k/(k:ℝ)))/Real.log (x^k/(k:ℝ)) := kg_le (x^k) k hk hyk

theorem caXiK_bounds (ξ ξk : ℝ) (k : ℕ) (hξ : 1 < ξ) (hξk : 1 < ξk) (hk : 2 ≤ k)
    (hF : Real.log (1 + 1 / Finset.sum (Finset.range k) (fun i => ξk ^ (i + 1))) / Real.log ξk
        = Real.log (1 + 1 / ξ) / Real.log ξ) :
    ξ ^ (1 / (k : ℝ)) ≤ ξk ∧ ξk ≤ ((k : ℝ) * ξ) ^ (1 / (k : ℝ)) := by
  have hξ0 : 0 < ξ := lt_trans zero_lt_one hξ
  have hx0 : 0 < ξk := lt_trans zero_lt_one hξk
  set S := Finset.sum (Finset.range k) (fun i => ξk ^ (i + 1)) with hS
  have hy1 : 1 < ξk^k := one_lt_pow₀ hξk (by omega)
  have hy0 : 0 < ξk^k := lt_trans zero_lt_one hy1
  -- lower bound:  ξ ≤ ξk^k
  have hξle : ξ ≤ ξk^k := by
    have hlow : Real.log (1 + 1/ξk^k)/Real.log (ξk^k) ≤ Real.log (1 + 1/S)/Real.log ξk := by
      rw [hS]; exact lower_sandwich ξk hξk k hk
    have hgl : Real.log (1 + 1/ξk^k)/Real.log (ξk^k) ≤ Real.log (1 + 1/ξ)/Real.log ξ :=
      hlow.trans_eq hF
    exact (log_one_add_inv_div_log_strictAntiOn.le_iff_ge hy1 hξ).mp hgl
  -- upper bound:  ξk^k ≤ k·ξ
  have hy_le : ξk^k ≤ (k:ℝ)*ξ := by
    by_cases hyk : ξk^k ≤ (k:ℝ)
    · have hklt : (k:ℝ) < (k:ℝ)*ξ := by
        nlinarith [show (0:ℝ) < (k:ℝ) by positivity]
      linarith
    · push Not at hyk
      have hup : Real.log (1 + 1/S)/Real.log ξk ≤
          Real.log (1 + 1/(ξk^k/(k:ℝ)))/Real.log (ξk^k/(k:ℝ)) := by
        rw [hS]; exact upper_sandwich ξk hξk k hk hyk
      have hgl : Real.log (1 + 1/ξ)/Real.log ξ ≤
          Real.log (1 + 1/(ξk^k/(k:ℝ)))/Real.log (ξk^k/(k:ℝ)) := by
        rw [← hF]; exact hup
      have hykw : ξk^k/(k:ℝ) ∈ Ioi (1:ℝ) := by
        rw [Set.mem_Ioi, lt_div_iff₀ (by positivity : (0:ℝ) < k)]; linarith
      have hle : ξk^k/(k:ℝ) ≤ ξ := (log_one_add_inv_div_log_strictAntiOn.le_iff_ge hξ hykw).mp hgl
      have := (div_le_iff₀ (show (0:ℝ) < k by positivity)).mp hle
      linarith [this]
  have hroot : (ξk^k)^(1/(k:ℝ)) = ξk := by
    rw [← Real.rpow_natCast ξk k, ← Real.rpow_mul (le_of_lt hx0)]
    have : (k:ℝ)*(1/(k:ℝ)) = 1 := by rw [mul_one_div, div_self (by positivity)]
    rw [this, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc ξ^(1/(k:ℝ)) ≤ (ξk^k)^(1/(k:ℝ)) := Real.rpow_le_rpow (le_of_lt hξ0) hξle (by positivity)
      _ = ξk := hroot
  · calc ξk = (ξk^k)^(1/(k:ℝ)) := hroot.symm
      _ ≤ ((k:ℝ)*ξ)^(1/(k:ℝ)) := Real.rpow_le_rpow (le_of_lt hy0) hy_le (by positivity)

end Commons.NumberTheory.Robin