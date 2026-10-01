import Mathlib

namespace Work.ZeroDensity.Ingham

private lemma log_two_add_le (w : ℝ) (hw : 0 ≤ w) : Real.log (2 + w) ≤ 2 + w / 2 := by
  have h1 : (0:ℝ) < 1 + w/2 := by linarith
  have key : Real.log (2 + w) = Real.log 2 + Real.log (1 + w/2) := by
    have h : (2:ℝ) + w = 2 * (1 + w/2) := by ring
    rw [h, Real.log_mul (by norm_num) (by linarith)]
  rw [key]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have h3 : Real.log (1 + w/2) ≤ w/2 := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  linarith

private lemma log_two_mul_le (n : ℕ) (hn : 3 ≤ n) :
    Real.log (2 * (n:ℝ)) ≤ 4 * Real.log (((n-1:ℕ)):ℝ) := by
  have hnpos : 0 < n := by omega
  have hnr : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  rw [Nat.cast_pred hnpos]
  have hb2 : (2:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hle : 2 * (n:ℝ) ≤ 4 * ((n:ℝ) - 1) := by linarith
  have h1 : Real.log (2 * (n:ℝ)) ≤ Real.log (4 * ((n:ℝ)-1)) :=
    Real.log_le_log (by linarith) hle
  have h4 : Real.log (4 * ((n:ℝ)-1)) = Real.log 4 + Real.log ((n:ℝ)-1) :=
    Real.log_mul (by norm_num) (by linarith)
  have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [h4, hlog4] at h1
  have hlc : Real.log 2 ≤ Real.log ((n:ℝ)-1) := Real.log_le_log (by norm_num) hb2
  have hnn : 0 ≤ Real.log ((n:ℝ)-1) := Real.log_nonneg (by linarith)
  linarith

theorem logLog_diff_le (N n : ℕ) (hN : 2 ≤ N) (hn : 3 ≤ n) (hnN : n ≤ N - 1) :
    Real.log (Real.log (((N - 1 : ℕ) : ℝ))) - Real.log (Real.log (((n - 1 : ℕ) : ℝ)))
      ≤ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) := by
  have hNpos : 0 < N := by omega
  have hnpos : 0 < n := by omega
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hNr3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
  have hnr3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnlt : (n:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : n < N)
  set a : ℝ := ((N - 1 : ℕ) : ℝ) with ha
  set b : ℝ := ((n - 1 : ℕ) : ℝ) with hb
  have hb2 : (2:ℝ) ≤ b := by rw [hb]; exact_mod_cast (by omega : (2:ℕ) ≤ n - 1)
  have ha1 : (1:ℝ) < a := by rw [ha]; exact_mod_cast (by omega : (1:ℕ) < N - 1)
  have hb1 : (1:ℝ) < b := by linarith
  have hapos : (0:ℝ) < a := by linarith
  have hbpos : (0:ℝ) < b := by linarith
  set A : ℝ := Real.log a with hAlog
  set B : ℝ := Real.log b with hBlog
  have hApos : 0 < A := by rw [hAlog]; exact Real.log_pos ha1
  have hBpos : 0 < B := by rw [hBlog]; exact Real.log_pos hb1
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hlog2B : Real.log 2 ≤ B := by
    rw [hBlog]; exact Real.log_le_log (by norm_num) hb2
  have hlog2npos : 0 < Real.log (2*(n:ℝ)) := Real.log_pos (by linarith)
  have hXnn : 0 ≤ Real.log N - Real.log n := by
    have : Real.log n ≤ Real.log N := Real.log_le_log hnr (le_of_lt hnlt)
    linarith
  have hAB : A - B = Real.log (a/b) := by
    rw [hAlog, hBlog, Real.log_div (ne_of_gt hapos) (ne_of_gt hbpos)]
  have hratio : a / b ≤ 2 * (N:ℝ) / (n:ℝ) := by
    rw [div_le_iff₀ hbpos, div_mul_eq_mul_div, le_div_iff₀ hnr]
    rw [ha, hb, Nat.cast_pred hNpos, Nat.cast_pred hnpos]
    nlinarith [hNr3, hnr3]
  have hABbound : A - B ≤ Real.log 2 + (Real.log N - Real.log n) := by
    rw [hAB]
    have h1 : Real.log (a/b) ≤ Real.log (2 * (N:ℝ) / (n:ℝ)) :=
      Real.log_le_log (div_pos hapos hbpos) hratio
    have h2 : Real.log (2 * (N:ℝ) / (n:ℝ)) = Real.log 2 + (Real.log N - Real.log n) := by
      rw [Real.log_div (by positivity) (ne_of_gt hnr), Real.log_mul (by norm_num) (ne_of_gt hNr)]
      ring
    rw [h2] at h1; exact h1
  have hABle : A / B ≤ 2 + (Real.log N - Real.log n) / B := by
    have hsplit : A / B = 1 + (A - B)/B := by field_simp; ring
    rw [hsplit]
    have h1 : (A - B)/B ≤ (Real.log 2 + (Real.log N - Real.log n))/B :=
      div_le_div_of_nonneg_right hABbound (le_of_lt hBpos)
    have h2 : (Real.log 2 + (Real.log N - Real.log n))/B ≤ 1 + (Real.log N - Real.log n)/B := by
      rw [add_div]
      have hh : Real.log 2 / B ≤ 1 := by rw [div_le_one hBpos]; exact hlog2B
      linarith
    linarith
  have hw : 0 ≤ (Real.log N - Real.log n)/B := div_nonneg hXnn (le_of_lt hBpos)
  have hlogAB : Real.log (A/B) ≤ Real.log (2 + (Real.log N - Real.log n)/B) :=
    Real.log_le_log (div_pos hApos hBpos) hABle
  have hD : Real.log (2 + (Real.log N - Real.log n)/B) ≤ 2 + ((Real.log N - Real.log n)/B)/2 :=
    log_two_add_le _ hw
  have hRle : Real.log (2*(n:ℝ)) ≤ 4*B := by
    have h := log_two_mul_le n hn
    rw [← hb, ← hBlog] at h; exact h
  have hE : ((Real.log N - Real.log n)/B)/2 ≤ 2*(Real.log N - Real.log n)/Real.log (2*(n:ℝ)) := by
    have hchalf_pos : 0 < Real.log (2*(n:ℝ))/2 := by linarith
    have hchalf_le : Real.log (2*(n:ℝ))/2 ≤ 2*B := by linarith
    have key := div_le_div_of_nonneg_left hXnn hchalf_pos hchalf_le
    have e1 : ((Real.log N - Real.log n)/B)/2 = (Real.log N - Real.log n)/(2*B) := by ring
    have hRne : Real.log (2*(n:ℝ)) ≠ 0 := ne_of_gt hlog2npos
    have e2 : (Real.log N - Real.log n)/(Real.log (2*(n:ℝ))/2)
        = 2*(Real.log N - Real.log n)/Real.log (2*(n:ℝ)) := by field_simp
    rw [e1, ← e2]
    exact key
  have hXle : Real.log N - Real.log n ≤ Real.log (2*(N:ℝ)) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hNr)]
    have h1 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hFinal : 2 + 2*(Real.log N - Real.log n)/Real.log (2*(n:ℝ))
      ≤ 2*(1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ))) := by
    have h2 : (Real.log N - Real.log n)/Real.log (2*(n:ℝ))
        ≤ Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ)) :=
      div_le_div_of_nonneg_right hXle (le_of_lt hlog2npos)
    rw [mul_add, mul_one, mul_div_assoc]
    linarith
  have step1 : Real.log A - Real.log B = Real.log (A/B) := (Real.log_div hAne hBne).symm
  calc Real.log A - Real.log B = Real.log (A/B) := step1
    _ ≤ Real.log (2 + (Real.log N - Real.log n)/B) := hlogAB
    _ ≤ 2 + ((Real.log N - Real.log n)/B)/2 := hD
    _ ≤ 2 + 2*(Real.log N - Real.log n)/Real.log (2*(n:ℝ)) := by linarith [hE]
    _ ≤ 2*(1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ))) := hFinal

end Work.ZeroDensity.Ingham
