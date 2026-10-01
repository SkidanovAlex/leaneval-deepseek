import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
import Submission.Commons.Analysis.Abel.tail_bound_finite

open scoped BigOperators
open Filter

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

theorem LFunction_partial_sums_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1), 2 ≤ q →
      ∀ {s : ℂ}, 0 < s.re → ∀ {M : ℕ}, 1 ≤ M →
      ‖(∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-s)) - χ.LFunction s‖
        ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * (1 + ‖s‖ / s.re) *
            (M : ℝ) ^ (-s.re) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := charSum_range_le_polyaVinogradov
  refine ⟨C₀, hC₀pos, ?_⟩
  intro q _ χ hχ hq s hs M hM
  have hq1 : q ≠ 1 := by omega
  set a : ℕ → ℂ := fun n => (χ (n : ZMod q) : ℂ) with ha
  have ha0 : a 0 = 0 := by
    rw [ha]
    show χ ((0 : ℕ) : ZMod q) = 0
    rw [Nat.cast_zero]
    exact χ.map_zero' hq1
  set B : ℝ := C₀ * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) with hBdef
  have hsq : (0:ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hlog : (0:ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_nonneg
    have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hBglob : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, a n‖ ≤ B := by
    intro x y hxy
    rw [hBdef]
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      -- x = 0 : strip the n = 0 term, which vanishes
      have hsum0 : ∑ n ∈ Finset.Icc 0 y, a n = ∑ n ∈ Finset.Icc 1 y, a n := by
        have hun : Finset.Icc 0 y = insert 0 (Finset.Icc 1 y) := by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hun, Finset.sum_insert (by simp [Finset.mem_Icc]), ha0, zero_add]
      rw [hsum0]
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ 1 ≤ 0), Finset.sum_empty, norm_zero]
        exact mul_nonneg (mul_nonneg hC₀pos.le hsq) hlog
      · simp only [ha]
        exact hC₀ q (by omega) χ hχ 1 y hy
    · simp only [ha]
      exact hC₀ q (by omega) χ hχ x y hxy
  set SM : ℂ := ∑ n ∈ Finset.Icc 1 M, a n * (n : ℂ) ^ (-s) with hSM
  set T : ℕ → ℂ := fun N => ∑ n ∈ Finset.Icc (M + 1) N, a n * (n : ℂ) ^ (-s) with hTdef
  have hF : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) atTop
      (nhds (χ.LFunction s)) := by
    have h := LSeries_partial_sums_tendsto χ hχ hs
    simpa [ha] using h
  have hT : Tendsto T atTop (nhds (χ.LFunction s - SM)) := by
    have h1 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) - SM) atTop
        (nhds (χ.LFunction s - SM)) := hF.sub tendsto_const_nhds
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop M] with N hN
    simp only [hTdef, hSM]
    have hunion : Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Icc (M + 1) N := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) N) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_Icc] at hn1 hn2
      omega
    rw [hunion, Finset.sum_union hdisj]
    ring
  have hbnd : ∀ᶠ N in atTop, ‖T N‖ ≤ B * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
    rw [eventually_atTop]
    refine ⟨M, fun N hN => ?_⟩
    rcases eq_or_lt_of_le hN with hNM | hNM
    · subst hNM
      have hempty : Finset.Icc (M + 1) M = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
      simp only [hTdef, hempty, Finset.sum_empty, norm_zero]
      have h1 : 0 ≤ (M : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg M) _
      have h2 : 0 ≤ 1 + ‖s‖ / s.re := by positivity
      exact mul_nonneg (mul_nonneg hB0 h1) h2
    · have hle : M + 1 ≤ N := hNM
      have htail := Commons.Analysis.Abel.tail_bound_finite B hBglob s hs (N := M + 1) (M := N) hle (by omega)
      have h2 : ((M + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (M : ℝ) ^ (-s.re) := by
        refine Real.rpow_le_rpow_of_nonpos ?_ ?_ ?_
        · exact_mod_cast (show 0 < M by omega)
        · exact_mod_cast (show M ≤ M + 1 by omega)
        · linarith
      have h2' : 0 ≤ 1 + ‖s‖ / s.re := by positivity
      calc ‖T N‖ = ‖∑ k ∈ Finset.Icc (M + 1) N, a k * (k : ℂ) ^ (-s)‖ := by simp only [hTdef]
        _ ≤ B * ((M + 1 : ℕ) : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := htail
        _ ≤ B * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
            apply mul_le_mul_of_nonneg_right _ h2'
            exact mul_le_mul_of_nonneg_left h2 hB0
  have hfinal : ‖χ.LFunction s - SM‖ ≤ B * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) :=
    le_of_tendsto hT.norm hbnd
  have hmain : ‖(∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-s)) - χ.LFunction s‖
      ≤ C₀ * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * (1 + ‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
    rw [hSM] at hfinal
    rw [norm_sub_rev]
    calc ‖χ.LFunction s - ∑ n ∈ Finset.Icc 1 M, a n * (n : ℂ) ^ (-s)‖
        ≤ B * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := hfinal
      _ = C₀ * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * (1 + ‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
          rw [hBdef]; ring
  simpa [ha] using hmain

end

end Commons.NumberTheory.DirichletCharacter
