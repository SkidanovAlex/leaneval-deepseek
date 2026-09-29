import Mathlib

namespace Work.TMC16Core.Assembly

theorem decay_final_arith {L C : ℝ} (hL : 0 < L) (hC : 0 ≤ C) {q : ℕ → ℕ}
    (hmono : StrictMono q) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, q n ≤ 5 * d →
      C * (1 + 3 * (q n : ℝ)) * Real.exp (5 * (7 * L / 10) + 41 * (7 * L / 10 + Real.log 2))
        ≤ Real.exp (L / 40 * (d : ℝ)) := by
  -- Write `c = L/600`, so that `3c = L/200`.  We will compare the left-hand side with
  -- `exp (c·t)^3 = exp (3c·t) = exp (L/200·t)` where `t = q n`.
  set c : ℝ := L / 600 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  -- The constant appearing in the exponential of the left-hand side.
  set K : ℝ := 5 * (7 * L / 10) + 41 * (7 * L / 10 + Real.log 2) with hK_def
  -- The threshold beyond which all three elementary estimates hold.
  set B : ℝ := max (max (16 / c ^ 2 + 1) ((|Real.log C| + 1) / c)) (K / c) with hB_def
  obtain ⟨M, hM⟩ := exists_nat_ge B
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hmono.tendsto_atTop M
  refine ⟨N, ?_⟩
  intro n hn d hd
  set t : ℝ := (q n : ℝ) with ht_def
  have hqn : M ≤ q n := hN n hn
  have htM : (M : ℝ) ≤ t := by rw [ht_def]; exact_mod_cast hqn
  have htB : B ≤ t := le_trans hM htM
  have ht0 : 0 ≤ t := by rw [ht_def]; positivity
  -- Extract the three thresholds from `B ≤ t`.
  have hx1 : 16 / c ^ 2 + 1 ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htB
  have hx2 : (|Real.log C| + 1) / c ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htB
  have hy : K / c ≤ t := le_trans (le_max_right _ _) htB
  -- (a) `1 + 3t ≤ exp (c t)`.
  have ht1 : (1:ℝ) ≤ t := by
    have h : (0:ℝ) ≤ 16 / c ^ 2 := by positivity
    linarith
  have h16 : 16 ≤ c ^ 2 * t := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < c ^ 2)).mp (by linarith : 16 / c ^ 2 ≤ t)
    simpa [mul_comm] using h
  -- `1 + 3t ≤ 4t ≤ c²t²/4 = (ct/2)² ≤ exp (ct)`.
  have hquad : 1 + 3 * t ≤ c ^ 2 * t ^ 2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h16) (sub_nonneg.mpr ht1)]
  have hexp_sq : (c*t/2)^2 ≤ Real.exp (c*t) := by
    have h1 : c*t/2 + 1 ≤ Real.exp (c*t/2) := Real.add_one_le_exp _
    have h2 : c*t/2 ≤ Real.exp (c*t/2) := by linarith
    have h3 : (c*t/2)^2 ≤ (Real.exp (c*t/2))^2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h4 : (Real.exp (c*t/2))^2 = Real.exp (c*t) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rwa [h4] at h3
  have h1 : 1 + 3 * t ≤ Real.exp (c * t) := by
    have h5 : (c*t/2)^2 = c ^ 2 * t ^ 2 / 4 := by ring
    calc 1 + 3*t ≤ c ^ 2 * t ^ 2 / 4 := hquad
      _ = (c*t/2)^2 := h5.symm
      _ ≤ Real.exp (c*t) := hexp_sq
  -- (b) `C ≤ exp (c t)`.
  have hctC : Real.log C ≤ c * t := by
    have h := (div_le_iff₀ hc).mp hx2
    have h2 : Real.log C ≤ |Real.log C| + 1 := by linarith [le_abs_self (Real.log C)]
    have h3 : Real.log C ≤ t * c := le_trans h2 h
    rwa [mul_comm] at h3
  have hClt : C ≤ Real.exp (c*t) := by
    rcases lt_or_eq_of_le hC with hCpos | hC0
    · have := Real.exp_le_exp.mpr hctC
      rwa [Real.exp_log hCpos] at this
    · rw [← hC0]; positivity
  -- (c) `exp K ≤ exp (c t)`.
  have hctK : K ≤ c*t := by
    have h := (div_le_iff₀ hc).mp hy
    rwa [mul_comm] at h
  have hKlt : Real.exp K ≤ Real.exp (c*t) := Real.exp_le_exp.mpr hctK
  -- Multiply the three estimates.
  have hstep : C * (1 + 3*t) * Real.exp K ≤ (Real.exp (c*t))^3 := by
    have h2' : (1 + 3*t) * Real.exp K ≤ (Real.exp (c*t)) * (Real.exp (c*t)) :=
      mul_le_mul h1 hKlt (le_of_lt (Real.exp_pos K)) (le_of_lt (Real.exp_pos (c*t)))
    have h3' : C * ((1 + 3*t) * Real.exp K) ≤
        (Real.exp (c*t)) * ((Real.exp (c*t)) * (Real.exp (c*t))) :=
      mul_le_mul hClt h2' (by positivity) (le_of_lt (Real.exp_pos (c*t)))
    calc C * (1 + 3*t) * Real.exp K
        = C * ((1 + 3*t) * Real.exp K) := by ring
      _ ≤ (Real.exp (c*t)) * ((Real.exp (c*t)) * (Real.exp (c*t))) := h3'
      _ = (Real.exp (c*t))^3 := by ring
  have hexp3 : (Real.exp (c*t))^3 = Real.exp (L/200 * t) := by
    rw [← Real.exp_nat_mul (c*t) 3]; congr 1; rw [hc_def]; ring
  -- Use `d ≥ t/5` and `L/40 · (t/5) = L/200 · t`.
  have hfinal : Real.exp (L/200 * t) ≤ Real.exp (L/40 * (d:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have htd : t ≤ 5 * (d:ℝ) := by rw [ht_def]; exact_mod_cast hd
    have hdt : t / 5 ≤ (d:ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_left hdt (by positivity : (0:ℝ) ≤ L/40)
    have he : L / 200 * t = L / 40 * (t / 5) := by ring
    rw [he]; exact h
  calc C * (1 + 3 * t) * Real.exp K
      ≤ (Real.exp (c*t))^3 := hstep
    _ = Real.exp (L/200 * t) := hexp3
    _ ≤ Real.exp (L/40 * (d:ℝ)) := hfinal

end Work.TMC16Core.Assembly
