import Mathlib

namespace Commons.Analysis.Real

/-- For `R ≥ 2`, the partial geometric sum `∑_{t<n} (1/R)^t` is at most `2`. -/
lemma geom_inv_sum_le_two {R : ℝ} (hR : 2 ≤ R) (n : ℕ) :
    ∑ t ∈ Finset.range n, (1 / R) ^ t ≤ 2 := by
  have hRpos : 0 < R := by linarith
  set x : ℝ := 1 / R with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hxle : x ≤ 1 / 2 := by
    rw [hx]
    exact (one_div_le_one_div hRpos (by norm_num)).mpr hR
  have hS : (∑ t ∈ Finset.range n, x ^ t) * (1 - x) = 1 - x ^ n := by
    have h := geom_sum_mul x n
    linear_combination -h
  have h1x : 0 < 1 - x := by linarith
  have hxn : 0 ≤ x ^ n := pow_nonneg (le_of_lt hxpos) n
  have hbound : (∑ t ∈ Finset.range n, x ^ t) * (1 - x) ≤ 2 * (1 - x) := by
    rw [hS]
    linarith
  calc ∑ t ∈ Finset.range n, (1 / R) ^ t = ∑ t ∈ Finset.range n, x ^ t := by rw [hx]
    _ ≤ 2 := le_of_mul_le_mul_right hbound h1x

theorem sum_inv_le_two_div {m : ℕ} (A R : ℝ) (lq : Fin m → ℝ) (hA : 0 < A) (hR : 2 ≤ R)
    (hlq : ∀ h, A ≤ lq h)
    (hdec : ∀ i j : Fin m, i ≤ j → R ^ ((j : ℕ) - (i : ℕ)) * lq j ≤ lq i) :
    ∑ h, 1 / lq h ≤ 2 / A := by
  rcases m with _ | n
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg (by norm_num) (le_of_lt hA)
  · have hRpos : 0 < R := by linarith
    have hexp : ∀ i : Fin (n + 1), ((Fin.last n : ℕ) - (i : ℕ)) = (Fin.rev i : ℕ) := by
      intro i
      simp only [Fin.val_last, Fin.val_rev]
      omega
    have hpoint : ∀ i : Fin (n + 1),
        1 / lq i ≤ (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ)) / A := by
      intro i
      have hle : R ^ ((Fin.last n : ℕ) - (i : ℕ)) * A ≤ lq i := by
        have h1 := hdec i (Fin.last n) (Fin.le_last i)
        have h2 : R ^ ((Fin.last n : ℕ) - (i : ℕ)) * A
            ≤ R ^ ((Fin.last n : ℕ) - (i : ℕ)) * lq (Fin.last n) :=
          mul_le_mul_of_nonneg_left (hlq (Fin.last n)) (pow_nonneg (le_of_lt hRpos) _)
        linarith
      have hpos : 0 < R ^ ((Fin.last n : ℕ) - (i : ℕ)) * A := mul_pos (pow_pos hRpos _) hA
      calc 1 / lq i ≤ 1 / (R ^ ((Fin.last n : ℕ) - (i : ℕ)) * A) :=
            one_div_le_one_div_of_le hpos hle
        _ = (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ)) / A := by
            rw [one_div, one_div, div_eq_mul_inv, mul_inv, inv_pow]
    have hgeo : ∑ i : Fin (n + 1), (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ)) ≤ 2 := by
      have hre : ∑ i : Fin (n + 1), (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ))
          = ∑ i : Fin (n + 1), (1 / R) ^ (i : ℕ) := by
        have step1 : ∑ i : Fin (n + 1), (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ))
            = ∑ i : Fin (n + 1), (1 / R) ^ (Fin.rev i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hexp i]
        rw [step1]
        exact Function.Bijective.sum_comp Fin.rev_bijective (fun t : Fin (n + 1) => (1 / R) ^ (t : ℕ))
      rw [hre, Fin.sum_univ_eq_sum_range (fun t => (1 / R) ^ t) (n + 1)]
      exact geom_inv_sum_le_two hR (n + 1)
    calc ∑ h : Fin (n + 1), 1 / lq h
        ≤ ∑ i : Fin (n + 1), (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ)) / A :=
          Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (∑ i : Fin (n + 1), (1 / R) ^ ((Fin.last n : ℕ) - (i : ℕ))) / A := by
          rw [Finset.sum_div]
      _ ≤ 2 / A := div_le_div_of_nonneg_right hgeo (le_of_lt hA)

end Commons.Analysis.Real
