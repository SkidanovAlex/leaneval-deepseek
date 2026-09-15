import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex MeasureTheory

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- Integral-test bound for the `p`-series: for `σ > 1` the sum of `n^{-σ}` over `n : ℕ`
is bounded by `1 + 1/(σ-1)`. -/
private lemma tsum_nat_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hlt : -σ < -1 := by linarith
  have hnonpos : -σ ≤ 0 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hnonpos).mono (by
      intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [Set.mem_Ioi]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by simpa using hx))
  have hint : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hlt (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
  have hnonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ t ^ (-σ) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ))
      (le_of_lt ht))) _
  have hkey := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => x ^ (-σ)) 1 hanti hint hnonneg
  have hintval : ∫ x in Set.Ioi ((1 : ℕ) : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt hlt (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)),
      show (-σ) + 1 = 1 - σ by ring, Nat.cast_one, Real.one_rpow]
    rw [show (1 : ℝ) - σ = -(σ - 1) by ring, div_neg, neg_div, neg_neg]
  have htail : ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 / (σ - 1) :=
    hkey.trans hintval.le
  have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr hlt
  have hdecomp : ∑' n : ℕ, (n : ℝ) ^ (-σ)
      = 1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by
    have h := hsumm.sum_add_tsum_nat_add 2
    have hsum2 : ∑ i ∈ Finset.range 2, (i : ℝ) ^ (-σ) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [Real.zero_rpow (ne_of_lt (by linarith : -σ < 0))]
    have hcong : (∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-σ))
        = ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) :=
      tsum_congr fun _ => rfl
    calc ∑' n : ℕ, (n : ℝ) ^ (-σ)
        = (∑ i ∈ Finset.range 2, (i : ℝ) ^ (-σ))
            + ∑' i : ℕ, ((i + 2 : ℕ) : ℝ) ^ (-σ) := h.symm
      _ = 1 + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by rw [hsum2, hcong]
  rw [hdecomp]
  linarith

theorem LFunction_norm_le_inv_sub_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ T : ℝ} (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 + 1 / (σ - 1) := by
  classical
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs_def
  have hsr : s.re = σ := by simp [hs_def]
  have hs1 : 1 < s.re := by rw [hsr]; exact hσ
  have hlt : -σ < -1 := by linarith
  let f : ℕ → ℂ := fun n => (χ (n : ZMod N) : ℂ)
  have hs_eq : DirichletCharacter.LFunction χ s = LSeries f s :=
    DirichletCharacter.LFunction_eq_LSeries χ hs1
  have hsumm_f : LSeriesSummable f s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hterm_le : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ (n : ℝ) ^ (-σ) := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn
      simp only [if_true]
      simp [Real.zero_rpow (ne_of_lt (by linarith : -σ < 0))]
    · rw [if_neg hn, hsr]
      have hfn : ‖f n‖ ≤ 1 := by
        simp only [f]
        exact χ.norm_le_one (n : ZMod N)
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hpos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos _
      calc ‖f n‖ / (n : ℝ) ^ σ ≤ 1 / (n : ℝ) ^ σ :=
            div_le_div_of_nonneg_right hfn (le_of_lt hpos)
        _ = (n : ℝ) ^ (-σ) := by rw [one_div, Real.rpow_neg (le_of_lt hnpos)]
  calc ‖DirichletCharacter.LFunction χ s‖ = ‖LSeries f s‖ := by rw [hs_eq]
    _ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsumm_f.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) :=
        Summable.tsum_le_tsum hterm_le hsumm_f.norm (Real.summable_nat_rpow.mpr hlt)
    _ ≤ 1 + 1 / (σ - 1) := tsum_nat_rpow_neg_le σ hσ

end Commons.NumberTheory.DirichletCharacter