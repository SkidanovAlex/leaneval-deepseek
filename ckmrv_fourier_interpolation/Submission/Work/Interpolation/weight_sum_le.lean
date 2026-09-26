import Mathlib

namespace Work.Interpolation

open scoped BigOperators

/-- The partial sums of `n ↦ 1/(1+n)^2` over `range N` are bounded by `2`:
compare the `n`-th term with `2*(1/(1+n) - 1/(2+n))`, whose sum telescopes. -/
private lemma range_one_div_sq_le_two (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / (1 + (n : ℝ))^2 ≤ 2 := by
  have key : ∀ n : ℕ, (1 : ℝ) / (1 + (n : ℝ))^2 ≤
      2 * ((1 / (1 + (n : ℝ))) - (1 / (1 + ((n + 1 : ℕ) : ℝ)))) := by
    intro n
    have hcast : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = 2 + (n : ℝ) := by push_cast; ring
    rw [hcast]
    have h1 : (0 : ℝ) < 1 + (n : ℝ) := by positivity
    have h2 : (0 : ℝ) < 2 + (n : ℝ) := by positivity
    field_simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc ∑ n ∈ Finset.range N, (1 : ℝ) / (1 + (n : ℝ))^2
      ≤ ∑ n ∈ Finset.range N,
          2 * ((fun k : ℕ => 1 / (1 + (k : ℝ))) n
                - (fun k : ℕ => 1 / (1 + (k : ℝ))) (n + 1)) :=
        Finset.sum_le_sum (fun n _ => key n)
    _ = 2 * ∑ n ∈ Finset.range N,
          ((fun k : ℕ => 1 / (1 + (k : ℝ))) n
            - (fun k : ℕ => 1 / (1 + (k : ℝ))) (n + 1)) := by
        rw [Finset.mul_sum]
    _ = 2 * ((fun k : ℕ => 1 / (1 + (k : ℝ))) 0
              - (fun k : ℕ => 1 / (1 + (k : ℝ))) N) := by
        rw [Finset.sum_range_sub']
    _ ≤ 2 := by
        have h0 : (fun k : ℕ => 1 / (1 + (k : ℝ))) 0 = 1 := by norm_num
        have hN : 0 ≤ (fun k : ℕ => 1 / (1 + (k : ℝ))) N := by positivity
        rw [h0]; linarith

/-- `n ↦ 1/(1+n)^2` is summable on `ℕ` with total mass at most `2`. -/
private lemma summable_nat_one_div_sq :
    Summable (fun n : ℕ => (1 : ℝ) / (1 + (n : ℝ))^2) ∧
      ∑' n : ℕ, (1 : ℝ) / (1 + (n : ℝ))^2 ≤ 2 := by
  have hnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (1 + (n : ℝ))^2 := fun n => by positivity
  exact ⟨summable_of_sum_range_le hnn range_one_div_sq_le_two,
    Real.tsum_le_of_sum_range_le hnn range_one_div_sq_le_two⟩

/-- Restricting `n ↦ 1/(1+n)^2` to `Set.Ici k₀` keeps summability and a total mass `≤ 2`. -/
private lemma summable_Ici_one_div_sq (k₀ : ℕ) :
    Summable (fun a : Set.Ici k₀ => (1 : ℝ) / (1 + (a : ℝ))^2) ∧
      ∑' a : Set.Ici k₀, (1 : ℝ) / (1 + (a : ℝ))^2 ≤ 2 := by
  obtain ⟨hsumm, hb⟩ := summable_nat_one_div_sq
  refine ⟨?_, ?_⟩
  · have h := hsumm.subtype (fun n => n ∈ Set.Ici k₀)
    exact h
  · calc ∑' a : Set.Ici k₀, (1 : ℝ) / (1 + (a : ℝ))^2
        = ∑' n : ℕ, (Set.Ici k₀).indicator (fun n : ℕ => (1 : ℝ) / (1 + (n : ℝ))^2) n :=
          tsum_subtype (Set.Ici k₀) (fun n : ℕ => (1 : ℝ) / (1 + (n : ℝ))^2)
      _ ≤ ∑' n : ℕ, (1 : ℝ) / (1 + (n : ℝ))^2 := by
          refine Summable.tsum_le_tsum (fun n => ?_) (hsumm.indicator _) hsumm
          rw [Set.indicator_apply]
          by_cases h : n ∈ Set.Ici k₀
          · simp [h]
          · simp only [h, ↓reduceIte]
            positivity
      _ ≤ 2 := hb

lemma weight_sum_le (k₀ : ℕ) :
    Summable (fun i : Set.Ici k₀ × Fin 4 => 1 / (1 + (i.1.1 : ℝ))^2) ∧
    ∑' i : Set.Ici k₀ × Fin 4, 1 / (1 + (i.1.1 : ℝ))^2 ≤ 8 := by
  obtain ⟨hsumm, hb⟩ := summable_Ici_one_div_sq k₀
  set g : Set.Ici k₀ → ℝ := fun a => (1 : ℝ) / (1 + (a : ℝ))^2 with hg
  have hprod : Summable (fun i : Set.Ici k₀ × Fin 4 => g i.1) := by
    have h := Summable.mul_of_nonneg hsumm
      (Summable.of_finite (f := fun _ : Fin 4 => (1 : ℝ)))
      (fun a => by simp only [hg]; positivity) (fun _ => by norm_num)
    simpa using h
  have hgoal : (fun i : Set.Ici k₀ × Fin 4 => 1 / (1 + (i.1.1 : ℝ))^2)
      = fun i => g i.1 := by
    funext i; simp only [hg]
  refine ⟨?_, ?_⟩
  · rw [hgoal]; exact hprod
  · rw [hgoal]
    have h1 : (∑' i : Set.Ici k₀ × Fin 4, g i.1)
        = ∑' a : Set.Ici k₀, ∑' j : Fin 4, g a := hprod.tsum_prod
    rw [h1]
    have h2 : ∀ a : Set.Ici k₀, (∑' j : Fin 4, g a) = 4 * g a := by
      intro a; rw [tsum_const, Nat.card_fin]; simp
    rw [tsum_congr h2, tsum_mul_left]
    have h4 : (4 : ℝ) * (∑' a : Set.Ici k₀, g a) ≤ 4 * 2 :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    linarith

end Work.Interpolation
