import Mathlib.Algebra.Order.Star.Real

namespace Commons.MeasureTheory.Real

theorem staircase_pointwise_bounds (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (1/(N:ℝ)) * ((Finset.Icc 1 (N-1)).filter (fun i : ℕ => (i:ℝ)/(N:ℝ) ≤ f x)).card ≤ f x ∧
    f x ≤ (1/(N:ℝ)) * ((Finset.Icc 1 (N-1)).filter (fun i : ℕ => (i:ℝ)/(N:ℝ) ≤ f x)).card
      + 1/(N:ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ N := hN
  have ht0 : 0 ≤ f x := hf0 x
  have ht1 : f x ≤ 1 := hf1 x
  set t := f x with ht
  have ht0' : 0 ≤ t := ht0
  have ht1' : t ≤ 1 := ht1
  set m : ℕ := ⌊(N:ℝ) * t⌋₊ with hm
  have hfloornn : (0:ℝ) ≤ (N:ℝ) * t := by positivity
  have hmle : (m:ℝ) ≤ (N:ℝ) * t := Nat.floor_le hfloornn
  have hmlt : (N:ℝ) * t < (m:ℝ) + 1 := Nat.lt_floor_add_one _
  have hmem : ∀ i : ℕ, i ∈ (Finset.Icc 1 (N-1)).filter (fun i : ℕ => (i:ℝ)/(N:ℝ) ≤ t) ↔
      i ∈ Finset.Icc 1 (min (N-1) m) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h3' : (i:ℝ) ≤ t * (N:ℝ) := (div_le_iff₀ hNpos).mp h3
      have hi : i ≤ m := by
        rw [hm, Nat.le_floor_iff hfloornn]
        linarith
      exact ⟨h1, le_min h2 hi⟩
    · rintro ⟨h1, hmin⟩
      have h2 : i ≤ N - 1 := le_trans hmin (min_le_left _ _)
      have hi : i ≤ m := le_trans hmin (min_le_right _ _)
      have hi' : (i:ℝ) ≤ (N:ℝ) * t := by
        rw [hm] at hi
        exact (Nat.le_floor_iff hfloornn).mp hi
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [div_le_iff₀ hNpos]
      linarith
  have hset : (Finset.Icc 1 (N-1)).filter (fun i : ℕ => (i:ℝ)/(N:ℝ) ≤ t)
      = Finset.Icc 1 (min (N-1) m) := by
    ext i
    exact hmem i
  have hcard : ((Finset.Icc 1 (N-1)).filter (fun i : ℕ => (i:ℝ)/(N:ℝ) ≤ t)).card
      = min (N-1) m := by
    rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard]
  constructor
  · have h1 : ((min (N-1) m : ℕ) : ℝ) ≤ (m:ℝ) := by
      exact_mod_cast min_le_right (N-1) m
    calc (1/(N:ℝ)) * ((min (N-1) m : ℕ) : ℝ)
        ≤ (1/(N:ℝ)) * (m:ℝ) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (1/(N:ℝ)) * ((N:ℝ) * t) := by
          exact mul_le_mul_of_nonneg_left hmle (by positivity)
      _ = t := by
          rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hNpos)]
  · have hkey : (N:ℝ) * t ≤ ((min (N-1) m : ℕ) : ℝ) + 1 := by
      rcases le_total m (N-1) with hle | hge
      · have hmin : min (N-1) m = m := min_eq_right hle
        rw [hmin]
        linarith [hmlt]
      · have hmin : min (N-1) m = N - 1 := min_eq_left hge
        rw [hmin]
        have hleN : (N:ℝ) * t ≤ (N:ℝ) := by nlinarith [ht1', hNpos]
        have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N:ℝ) := by
          rw [Nat.cast_sub hN1]; ring
        rw [hcast]
        exact hleN
    have heq : (1/(N:ℝ)) * ((min (N-1) m : ℕ) : ℝ) + 1/(N:ℝ)
        = (((min (N-1) m : ℕ) : ℝ) + 1) / (N:ℝ) := by ring
    rw [heq, le_div_iff₀ hNpos]
    linarith [hkey]

end Commons.MeasureTheory.Real