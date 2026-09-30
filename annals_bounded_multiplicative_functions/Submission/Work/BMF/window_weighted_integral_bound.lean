import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted integral of a function with bounded unit-window integrals

If `F ≥ 0` is continuous and every unit window integral `∫_c^{c+1} F` is at most `B`, then the
weighted integral `∫_{-T}^{T} F τ / (a² + τ²) dτ` is at most `8B`, provided `a ≥ 1`.

The weight `1/(a² + τ²)` is decreasing in `|τ|` and comparable to `1/(a² + k²)` on the unit
window `[k, k+1]`; summing the window bounds gives `∑_{k≥0} B/(a²+k²) ≤ 4B` on each half-line.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral

/-- The series bound `∑_{k<M} 1/(a² + k²) ≤ 4` for `a ≥ 1`, proved by comparison with the
telescoping series `∑ (4/(k+1) - 4/(k+2)) ≤ 4`. -/
private lemma sum_range_inv_sq_add_le_four (a : ℝ) (ha : 1 ≤ a) (M : ℕ) :
    ∑ k ∈ Finset.range M, 1 / (a^2 + (k:ℝ)^2) ≤ 4 := by
  have htel : ∑ k ∈ Finset.range M, (4 / ((k:ℝ)+1) - 4 / ((k:ℝ)+1+1)) ≤ 4 := by
    have h := Finset.sum_range_sub (f := fun i : ℕ => -4 / ((i:ℝ)+1)) M
    simp only [Nat.cast_add, Nat.cast_one] at h
    have heq : (∑ k ∈ Finset.range M, (4 / ((k:ℝ)+1) - 4 / ((k:ℝ)+1+1)))
        = ∑ x ∈ Finset.range M, (-4 / ((x:ℝ)+1+1) - -4 / ((x:ℝ)+1)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq, h]
    simp only [Nat.cast_zero, zero_add]
    have : -4 / ((M:ℝ)+1) - -4 / 1 = 4 - 4 / ((M:ℝ)+1) := by ring
    rw [this]
    have hpos : (0:ℝ) ≤ 4 / ((M:ℝ)+1) := by positivity
    linarith
  calc ∑ k ∈ Finset.range M, 1 / (a^2 + (k:ℝ)^2)
      ≤ ∑ k ∈ Finset.range M, (4 / ((k:ℝ)+1) - 4 / ((k:ℝ)+1+1)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [show (4 / ((k:ℝ)+1) - 4 / ((k:ℝ)+1+1))
              = 4 / (((k:ℝ)+1) * ((k:ℝ)+1+1)) by field_simp; ring]
        rw [le_div_iff₀ (by positivity)]
        rw [show 1 / (a^2 + (k:ℝ)^2) * (((k:ℝ)+1) * ((k:ℝ)+1+1))
              = ((k:ℝ)+1) * ((k:ℝ)+1+1) / (a^2 + (k:ℝ)^2) by ring]
        rw [div_le_iff₀ (by nlinarith [ha, sq_nonneg (k:ℝ), sq_nonneg a])]
        nlinarith [ha, sq_nonneg (k:ℝ), sq_nonneg a, sq_nonneg ((k:ℝ) - 1/2)]
    _ ≤ 4 := htel

/-- Auxiliary endpoint bound: for `F ≥ 0` continuous with unit-window integrals `≤ B` and
`a ≥ 1`, `B ≥ 0`, `T ≥ 0`,
`∫_0^T F τ / (a² + τ²) dτ ≤ 4 B`. -/
private lemma integral_zero_to_le_four
    (F : ℝ → ℝ) (hFc : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    (B a T : ℝ) (ha : 1 ≤ a) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hwin : ∀ c : ℝ, ∫ τ in c..(c+1), F τ ≤ B) :
    (∫ τ in (0:ℝ)..T, F τ / (a^2 + τ^2)) ≤ 4 * B := by
  set W : ℝ → ℝ := fun τ => F τ / (a^2 + τ^2) with hW
  have hden_pos : ∀ τ : ℝ, 0 < a^2 + τ^2 := by
    intro τ; nlinarith [ha, sq_nonneg τ]
  have hW_nonneg : ∀ τ : ℝ, 0 ≤ W τ := by
    intro τ; rw [hW]; exact div_nonneg (hFnn τ) (le_of_lt (hden_pos τ))
  have hW_cont : Continuous W := by
    rw [hW]; exact hFc.div (by continuity) (fun τ => ne_of_gt (hden_pos τ))
  have hW_int : ∀ x y : ℝ, IntervalIntegrable W volume x y :=
    fun x y => hW_cont.intervalIntegrable x y
  -- Step A: extend the upper limit to the ceiling
  have hA : (∫ τ in (0:ℝ)..T, W τ) ≤ ∫ τ in (0:ℝ)..(⌈T⌉₊ : ℝ), W τ := by
    refine integral_mono_interval (c := (0:ℝ)) (d := (⌈T⌉₊ : ℝ)) le_rfl hT (Nat.le_ceil T)
      (Filter.Eventually.of_forall hW_nonneg) (hW_int _ _)
  -- Step B: split into unit windows
  have hB_split : ∀ n : ℕ, (∫ τ in (0:ℝ)..(n:ℝ), W τ)
      = ∑ k ∈ Finset.range n, ∫ τ in (k:ℝ)..((k:ℝ)+1), W τ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih,
          show ((m+1:ℕ):ℝ) = (m:ℝ)+1 by push_cast; ring]
        exact (integral_add_adjacent_intervals (hW_int 0 (m:ℝ))
          (hW_int (m:ℝ) ((m:ℝ)+1))).symm
  -- Step C: bound each window integral
  have hterm : ∀ k : ℕ,
      ∫ τ in (k:ℝ)..((k:ℝ)+1), W τ ≤ B / (a^2 + (k:ℝ)^2) := by
    intro k
    have hconst_pos : 0 < a^2 + (k:ℝ)^2 := hden_pos (k:ℝ)
    have hkk : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
    have hkey : ∀ τ ∈ Set.Icc (k:ℝ) ((k:ℝ)+1),
        W τ ≤ F τ / (a^2 + (k:ℝ)^2) := by
      intro τ hτ
      rw [hW]
      refine div_le_div_of_nonneg_left (hFnn τ) hconst_pos ?_
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      nlinarith [hτ.1, hk0]
    have h2 : IntervalIntegrable (fun τ : ℝ => F τ / (a^2 + (k:ℝ)^2)) volume (k:ℝ) ((k:ℝ)+1) :=
      (hFc.div continuous_const (fun τ => ne_of_gt hconst_pos)).intervalIntegrable _ _
    calc ∫ τ in (k:ℝ)..((k:ℝ)+1), W τ
        ≤ ∫ τ in (k:ℝ)..((k:ℝ)+1), F τ / (a^2 + (k:ℝ)^2) :=
          integral_mono_on hkk (hW_int _ _) h2 hkey
      _ = (∫ τ in (k:ℝ)..((k:ℝ)+1), F τ) / (a^2 + (k:ℝ)^2) :=
          intervalIntegral.integral_div _ _
      _ ≤ B / (a^2 + (k:ℝ)^2) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hconst_pos)
          have h := hwin (k:ℝ)
          simpa using h
  calc (∫ τ in (0:ℝ)..T, W τ)
      ≤ ∫ τ in (0:ℝ)..(⌈T⌉₊ : ℝ), W τ := hA
    _ = ∑ k ∈ Finset.range ⌈T⌉₊, ∫ τ in (k:ℝ)..((k:ℝ)+1), W τ := hB_split ⌈T⌉₊
    _ ≤ ∑ k ∈ Finset.range ⌈T⌉₊, B / (a^2 + (k:ℝ)^2) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = B * ∑ k ∈ Finset.range ⌈T⌉₊, 1 / (a^2 + (k:ℝ)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ B * 4 := mul_le_mul_of_nonneg_left (sum_range_inv_sq_add_le_four a ha ⌈T⌉₊) hB
    _ = 4 * B := by ring

theorem window_weighted_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ), Continuous F → (∀ τ, 0 ≤ F τ) →
      ∀ B a T : ℝ, 1 ≤ a → 1 ≤ T →
      (∀ c : ℝ, ∫ τ in c..(c+1), F τ ≤ B) →
      (∫ τ in (-T)..T, F τ / (a^2 + τ^2)) ≤ C * B := by
  refine ⟨8, by norm_num, ?_⟩
  intro F hFc hFnn B a T ha hT hwin
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hB : 0 ≤ B := by
    have h0 : (0:ℝ) ≤ ∫ τ in (0:ℝ)..(1:ℝ), F τ :=
      integral_nonneg (by norm_num) (fun u _ => hFnn u)
    have h1 : (∫ τ in (0:ℝ)..(1:ℝ), F τ) ≤ B := by simpa using hwin 0
    linarith
  have hpos : (∫ τ in (0:ℝ)..T, F τ / (a^2 + τ^2)) ≤ 4 * B :=
    integral_zero_to_le_four F hFc hFnn B a T ha hT0 hB hwin
  -- the reflected function
  have hGc : Continuous (fun τ : ℝ => F (-τ)) := hFc.comp continuous_neg
  have hGnn : ∀ τ, 0 ≤ F (-τ) := fun τ => hFnn (-τ)
  have hGwin : ∀ c : ℝ, ∫ τ in c..(c+1), F (-τ) ≤ B := by
    intro c
    have h := hwin (-c - 1)
    have hEq : (∫ τ in c..(c+1), F (-τ)) = ∫ τ in (-c-1)..((-c-1)+1), F τ := by
      rw [integral_comp_neg F]
      congr 1 <;> ring
    rw [hEq]
    exact h
  have hneg : (∫ τ in (0:ℝ)..T, F (-τ) / (a^2 + τ^2)) ≤ 4 * B :=
    integral_zero_to_le_four (fun τ : ℝ => F (-τ)) hGc hGnn B a T ha hT0 hB hGwin
  -- identify the negative half with the reflected integral
  have hden_pos : ∀ τ : ℝ, 0 < a^2 + τ^2 := fun τ => by nlinarith [ha, sq_nonneg τ]
  have hf_cont : Continuous (fun τ : ℝ => F τ / (a^2 + τ^2)) :=
    hFc.div (by continuity) (fun τ => ne_of_gt (hden_pos τ))
  have hfi : ∀ x y : ℝ, IntervalIntegrable (fun τ : ℝ => F τ / (a^2 + τ^2)) volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hrel : (∫ τ in (-T)..(0:ℝ), F τ / (a^2 + τ^2))
      = ∫ τ in (0:ℝ)..T, F (-τ) / (a^2 + τ^2) := by
    have h := integral_comp_neg (f := fun x : ℝ => F x / (a^2 + x^2)) (a := (0:ℝ)) (b := T)
    simpa using h.symm
  have hsplit : (∫ τ in (-T)..T, F τ / (a^2 + τ^2))
      = (∫ τ in (-T)..(0:ℝ), F τ / (a^2 + τ^2))
        + ∫ τ in (0:ℝ)..T, F τ / (a^2 + τ^2) :=
    (integral_add_adjacent_intervals (hfi (-T) 0) (hfi 0 T)).symm
  calc (∫ τ in (-T)..T, F τ / (a^2 + τ^2))
      = (∫ τ in (-T)..(0:ℝ), F τ / (a^2 + τ^2))
          + ∫ τ in (0:ℝ)..T, F τ / (a^2 + τ^2) := hsplit
    _ = (∫ τ in (0:ℝ)..T, F (-τ) / (a^2 + τ^2))
          + ∫ τ in (0:ℝ)..T, F τ / (a^2 + τ^2) := by rw [hrel]
    _ ≤ 4 * B + 4 * B := add_le_add hneg hpos
    _ = 8 * B := by ring

end Work.BMF
