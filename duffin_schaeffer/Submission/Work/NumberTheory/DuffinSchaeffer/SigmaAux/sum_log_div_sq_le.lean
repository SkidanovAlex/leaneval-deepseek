import Mathlib

namespace Work.NumberTheory.DuffinSchaeffer.SigmaAux

/-- For `x ≥ 0`, `log x ≤ 2 √x`. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv, one_div] at h
  linarith

/-- For `x ≥ 2`, `log x / (x - 1)² ≤ 8 / (x √x)`. -/
lemma log_div_sq_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log x / (x - 1) ^ 2 ≤ 8 / (x * Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hden : 0 < (x - 1) ^ 2 := by nlinarith
  have hq : 0 < x ^ 2 / 4 := by positivity
  have hquarter : x ^ 2 / 4 ≤ (x - 1) ^ 2 := by nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := log_le_two_sqrt hx0.le
  have h2 : 2 * Real.sqrt x / (x ^ 2 / 4) = 8 / (x * Real.sqrt x) := by
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    field_simp
    nlinarith [hsq]
  calc Real.log x / (x - 1) ^ 2
      ≤ 2 * Real.sqrt x / (x - 1) ^ 2 := by
        apply div_le_div_of_nonneg_right hlog hden.le
    _ ≤ 2 * Real.sqrt x / (x ^ 2 / 4) := by
        apply div_le_div_of_nonneg_left (by positivity) hq hquarter
    _ = 8 / (x * Real.sqrt x) := h2

/-- For `n ≥ 2`, `1/(n √n) ≤ 2 (1/√(n-1) - 1/√n)`. -/
lemma inv_mul_sqrt_le (n : ℕ) (hn : 2 ≤ n) :
    1 / ((n : ℝ) * Real.sqrt n) ≤
      2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set a := Real.sqrt ((n : ℝ) - 1) with ha
  set b := Real.sqrt (n : ℝ) with hb
  have ha2 : a ^ 2 = (n : ℝ) - 1 := by rw [ha]; exact Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (n : ℝ) := by rw [hb]; exact Real.sq_sqrt (by positivity)
  have hapos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr (by positivity)
  have hale : a ≤ b := by rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have ha2le : a ^ 2 ≤ b ^ 2 := by nlinarith [mul_self_le_mul_self hapos.le hale]
  have h1 : a ^ 2 * b ≤ b ^ 2 * b := mul_le_mul_of_nonneg_right ha2le hbpos.le
  have h2 : a * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right hale (by positivity)
  have hab : a * b * (a + b) ≤ 2 * b ^ 3 := by nlinarith [h1, h2]
  have hkey : 1 / (2 * b ^ 3) ≤ 1 / (a * b * (a + b)) :=
    one_div_le_one_div_of_le (by positivity) hab
  have hdiff : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    have hba : b - a = 1 / (a + b) := by
      rw [eq_div_iff (by positivity : a + b ≠ 0)]
      nlinarith [ha2, hb2]
    have hd : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    rw [hd, hba]
    field_simp
  have hb3 : b ^ 3 = (n : ℝ) * Real.sqrt n := by
    rw [show b ^ 3 = b ^ 2 * b by ring, hb2, hb]
  have hbne : b ≠ 0 := ne_of_gt hbpos
  calc (1 : ℝ) / ((n : ℝ) * Real.sqrt n) = 1 / b ^ 3 := by rw [hb3]
    _ = 2 * (1 / (2 * b ^ 3)) := by field_simp
    _ ≤ 2 * (1 / (a * b * (a + b))) := mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = 2 * (1 / a - 1 / b) := by rw [hdiff]
    _ = 2 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by rw [ha, hb]

/-- For `n ≥ 2`, `1/√(n-1) - 1/√n ≥ 0`. -/
lemma sqrt_sub_inv_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ 1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hmono : 1 / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt ((n : ℝ) - 1) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hn1) hle
  linarith

/-- Telescoping identity for `M ≥ 2`. -/
lemma sqrt_inv_telescope (M : ℕ) (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ))
      = 1 - 1 / Real.sqrt (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      norm_num
  | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
      rw [ih]
      have hcast : (((M + 1 : ℕ) : ℝ) - 1) = ((M : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      ring

theorem sum_log_div_sq_le (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 30 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨p0, hp0⟩ := hne
  set M := S.sup id with hMdef
  have hM2 : 2 ≤ M := le_trans (hS p0 hp0).two_le (Finset.le_sup (f := id) hp0)
  have hsub : S ⊆ Finset.Icc 2 M := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨(hS n hn).two_le, Finset.le_sup (f := id) hn⟩
  have hstep1 :
      ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2
        ≤ ∑ p ∈ S, 8 / ((p : ℝ) * Real.sqrt (p : ℝ)) :=
    Finset.sum_le_sum (fun p hp => log_div_sq_le (by exact_mod_cast (hS p hp).two_le))
  have hstep2 : ∑ p ∈ S, 8 / ((p : ℝ) * Real.sqrt (p : ℝ))
      ≤ ∑ p ∈ S, 16 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have h := inv_mul_sqrt_le p (hS p hp).two_le
    calc (8 : ℝ) / ((p : ℝ) * Real.sqrt (p : ℝ)) = 8 * (1 / ((p : ℝ) * Real.sqrt (p : ℝ))) := by
          rw [mul_one_div]
      _ ≤ 8 * (2 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 16 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)) := by ring
  have hstep3 : ∑ p ∈ S, 16 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ))
      = 16 * ∑ p ∈ S, (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)) :=
    (Finset.mul_sum S _ 16).symm
  have hstep4 : ∑ p ∈ S, (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ))
      ≤ ∑ n ∈ Finset.Icc 2 M,
          (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x hx _ => sqrt_sub_inv_nonneg x (Finset.mem_Icc.mp hx).1)
  calc ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2
      ≤ ∑ p ∈ S, 8 / ((p : ℝ) * Real.sqrt (p : ℝ)) := hstep1
    _ ≤ ∑ p ∈ S, 16 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)) := hstep2
    _ = 16 * ∑ p ∈ S, (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)) := hstep3
    _ ≤ 16 * ∑ n ∈ Finset.Icc 2 M,
          (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep4 (by norm_num)
    _ = 16 * (1 - 1 / Real.sqrt (M : ℝ)) := by rw [sqrt_inv_telescope M hM2]
    _ ≤ 30 := by
        have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
        have hpos : 0 ≤ 1 / Real.sqrt (M : ℝ) := by positivity
        linarith

end Work.NumberTheory.DuffinSchaeffer.SigmaAux
