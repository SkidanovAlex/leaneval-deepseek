import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open MeasureTheory intervalIntegral Filter Set
open scoped BigOperators

/-- For `a ≥ 1` and `T ≥ 1`, the partial sum `∑_{k<n} 1/(a² + (T+k)²)` is at most `2/T`. -/
private lemma window_sum_sq_bound (a T : ℝ) (_ha : 1 ≤ a) (hT : 1 ≤ T) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / (a ^ 2 + (T + (k : ℝ)) ^ 2) ≤ 2 / T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hterm : ∀ k : ℕ, 1 / (a ^ 2 + (T + (k : ℝ)) ^ 2) ≤ 1 / (T + (k : ℝ)) ^ 2 := by
    intro k
    have hk : 0 < T + (k : ℝ) := by positivity
    have hle : (T + (k : ℝ)) ^ 2 ≤ a ^ 2 + (T + (k : ℝ)) ^ 2 := by
      have : (0:ℝ) ≤ a ^ 2 := sq_nonneg a
      linarith
    exact one_div_le_one_div_of_le (by positivity) hle
  refine (Finset.sum_le_sum (fun k _ => hterm k)).trans ?_
  have hstep : ∀ k : ℕ,
      1 / (T + ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (T + (k : ℝ)) - 1 / (T + ((k + 1 : ℕ) : ℝ)) := by
    intro k
    have hx : 0 < T + (k : ℝ) := by positivity
    have hx1 : 0 < T + (k : ℝ) + 1 := by linarith
    rw [show T + ((k + 1 : ℕ) : ℝ) = T + (k : ℝ) + 1 by push_cast; ring]
    rw [div_sub_div (1:ℝ) (1:ℝ) (ne_of_gt hx) (ne_of_gt hx1)]
    rw [div_le_div_iff₀ (pow_pos hx1 2) (mul_pos hx hx1)]
    nlinarith [hx]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp only [Finset.range_zero, Finset.sum_empty]; positivity
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [Finset.sum_range_succ']
  have h0e : 1 / (T + ((0 : ℕ) : ℝ)) ^ 2 = 1 / T ^ 2 := by simp
  have htel : ∑ k ∈ Finset.range m, 1 / (T + ((k + 1 : ℕ) : ℝ)) ^ 2
      ≤ 1 / T - 1 / (T + (m : ℝ)) := by
    calc ∑ k ∈ Finset.range m, 1 / (T + ((k + 1 : ℕ) : ℝ)) ^ 2
        ≤ ∑ k ∈ Finset.range m, (1 / (T + (k : ℝ)) - 1 / (T + ((k + 1 : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum; intro k _; exact hstep k
      _ = 1 / T - 1 / (T + (m : ℝ)) := by
          rw [show ∑ k ∈ Finset.range m, (1 / (T + (k : ℝ)) - 1 / (T + ((k + 1 : ℕ) : ℝ)))
                = ∑ k ∈ Finset.range m,
                    (-(1 / (T + ((k + 1 : ℕ) : ℝ))) - - (1 / (T + (k : ℝ)))) by
              apply Finset.sum_congr rfl; intro k _; ring]
          rw [Finset.sum_range_sub (f := fun k : ℕ => -(1 / (T + (k : ℝ))))]
          simp only [Nat.cast_zero, add_zero]
          ring
  rw [h0e]
  calc ∑ k ∈ Finset.range m, 1 / (T + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1 / T ^ 2
      ≤ (1 / T - 1 / (T + (m : ℝ))) + 1 / T ^ 2 := add_le_add htel le_rfl
    _ ≤ 2 / T := by
        have h1 : 0 ≤ 1 / (T + (m : ℝ)) := by positivity
        have h2 : 1 / T ^ 2 ≤ 1 / T := one_div_le_one_div_of_le hTpos (by nlinarith)
        have hs : 1 / T - 1 / (T + (m : ℝ)) ≤ 1 / T := by
          rw [sub_le_iff_le_add]; exact le_add_of_nonneg_right h1
        calc (1 / T - 1 / (T + (m : ℝ))) + 1 / T ^ 2 ≤ 1 / T + 1 / T := add_le_add hs h2
          _ = 2 / T := by ring

/-- Reflection identity: `∫_{(-∞,-T)} g = ∫_{(T,∞)} g(-·)`. -/
private lemma integral_Iio_neg_eq_Ioi (T : ℝ) (g : ℝ → ℝ) :
    (∫ τ in Set.Iio (-T), g τ) = ∫ σ in Set.Ioi T, g (-σ) := by
  rw [← integral_Iic_eq_integral_Iio]
  exact (integral_comp_neg_Ioi T g).symm

/-- **Positive half-line.**  If `F ≥ 0` is continuous with unit-window integrals `≤ B`, then
`∫_{τ > T} F τ/(a²+τ²) dτ ≤ 2B/T`, for `a ≥ 1`, `T ≥ 1`, `B ≥ 0`. -/
private lemma Ioi_weighted_le (F : ℝ → ℝ) (hFc : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    (B a T : ℝ) (ha : 1 ≤ a) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hwin : ∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) :
    (∫ τ in Set.Ioi T, F τ / (a ^ 2 + τ ^ 2)) ≤ 2 * B / T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hden : ∀ τ : ℝ, 0 < a ^ 2 + τ ^ 2 := fun τ => by nlinarith [ha, sq_nonneg τ]
  set W : ℝ → ℝ := fun τ => F τ / (a ^ 2 + τ ^ 2) with hW
  change (∫ τ in Set.Ioi T, W τ) ≤ 2 * B / T
  have hWnn : ∀ τ : ℝ, 0 ≤ W τ := by
    intro τ; rw [hW]; exact div_nonneg (hFnn τ) (le_of_lt (hden τ))
  have hWc : Continuous W := by
    rw [hW]; exact hFc.div (by continuity) (fun τ => ne_of_gt (hden τ))
  have hWint : ∀ x y : ℝ, IntervalIntegrable W volume x y := fun x y => hWc.intervalIntegrable x y
  have hterm : ∀ k : ℕ,
      (∫ τ in (T + (k : ℝ))..(T + (k : ℝ) + 1), W τ) ≤ B / (a ^ 2 + (T + (k : ℝ)) ^ 2) := by
    intro k
    set c : ℝ := T + (k : ℝ) with hc
    change (∫ τ in c..(c + 1), W τ) ≤ B / (a ^ 2 + c ^ 2)
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hck : c ≤ c + 1 := by linarith
    have hdenk : 0 < a ^ 2 + c ^ 2 := hden c
    have hkey : ∀ τ ∈ Icc c (c + 1), W τ ≤ F τ / (a ^ 2 + c ^ 2) := by
      intro τ hτ
      rw [hW]
      apply div_le_div_of_nonneg_left (hFnn τ) hdenk
      nlinarith [hτ.1, hc0, sq_nonneg c, sq_nonneg τ]
    have h2 : IntervalIntegrable (fun τ => F τ / (a ^ 2 + c ^ 2)) volume c (c + 1) :=
      (hFc.div continuous_const (fun _ => ne_of_gt hdenk)).intervalIntegrable _ _
    calc (∫ τ in c..(c + 1), W τ)
        ≤ ∫ τ in c..(c + 1), F τ / (a ^ 2 + c ^ 2) := integral_mono_on hck (hWint _ _) h2 hkey
      _ = (∫ τ in c..(c + 1), F τ) / (a ^ 2 + c ^ 2) := intervalIntegral.integral_div _ _
      _ ≤ B / (a ^ 2 + c ^ 2) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hdenk)
          simpa using hwin c
  have hsplit : ∀ n : ℕ, (∫ τ in T..(T + (n : ℝ)), W τ)
      = ∑ k ∈ Finset.range n, ∫ τ in (T + (k : ℝ))..(T + (k : ℝ) + 1), W τ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih]
        have : T + ((m + 1 : ℕ) : ℝ) = T + (m : ℝ) + 1 := by push_cast; ring
        rw [this]
        exact (integral_add_adjacent_intervals (hWint T (T + (m : ℝ)))
          (hWint (T + (m : ℝ)) (T + (m : ℝ) + 1))).symm
  have htrunc : ∀ n : ℕ, (∫ τ in T..(T + (n : ℝ)), W τ) ≤ 2 * B / T := by
    intro n
    calc (∫ τ in T..(T + (n : ℝ)), W τ)
        = ∑ k ∈ Finset.range n, ∫ τ in (T + (k : ℝ))..(T + (k : ℝ) + 1), W τ := hsplit n
      _ ≤ ∑ k ∈ Finset.range n, B / (a ^ 2 + (T + (k : ℝ)) ^ 2) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = B * ∑ k ∈ Finset.range n, 1 / (a ^ 2 + (T + (k : ℝ)) ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ B * (2 / T) := mul_le_mul_of_nonneg_left (window_sum_sq_bound a T ha hT n) hB
      _ = 2 * B / T := by ring
  have htruncM : ∀ M : ℝ, T ≤ M → (∫ τ in T..M, W τ) ≤ 2 * B / T := by
    intro M hTM
    have hMle : M ≤ T + (⌈M - T⌉₊ : ℝ) := by
      have := Nat.le_ceil (M - T); linarith
    calc (∫ τ in T..M, W τ)
        ≤ ∫ τ in T..(T + (⌈M - T⌉₊ : ℝ)), W τ :=
          integral_mono_interval le_rfl hTM hMle (Eventually.of_forall hWnn) (hWint T _)
      _ ≤ 2 * B / T := htrunc ⌈M - T⌉₊
  have hInt : IntegrableOn W (Set.Ioi T) volume := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (μ := volume) (f := W) (b := fun n : ℕ => (n : ℝ)) (l := (atTop : Filter ℕ))
      (I := 2 * B / T) (a := T) ?_ ?_ ?_
    · intro n
      exact (hWc.integrableOn_Icc (a := T) (b := (n : ℝ))).mono_set Ioc_subset_Icc_self
    · exact tendsto_natCast_atTop_atTop (R := ℝ)
    · filter_upwards [eventually_ge_atTop ⌈T⌉₊] with n hn
      have hTn : T ≤ (n : ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast hn)
      have hcg : (∫ x in T..(n : ℝ), ‖W x‖) = ∫ x in T..(n : ℝ), W x :=
        intervalIntegral.integral_congr (fun x _ => Real.norm_of_nonneg (hWnn x))
      rw [hcg]
      exact htruncM (n : ℝ) hTn
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := W) (μ := volume) (b := id)
    (l := (atTop : Filter ℝ)) T hInt tendsto_id
  exact le_of_tendsto hlim
    (by filter_upwards [eventually_ge_atTop T] with M hM; exact htruncM M hM)

/-- **Far-window weighted integral bound.**  If `F ≥ 0` is continuous and every unit-window
integral `∫_c^{c+1} F` is at most `B`, then the weighted integrals of `F(τ)/(a²+τ²)` over the two
half-lines `|τ| > T` are `O(B/T)`, uniformly in `a ≥ 1`.  (Companion of
`Work.BMF.window_weighted_integral_bound`, which handles `|τ| ≤ T`.) -/
theorem casdiv_far_window :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ), Continuous F → (∀ τ, 0 ≤ F τ) →
      ∀ B a T : ℝ, 1 ≤ a → 1 ≤ T → (∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) →
        (∫ τ in Set.Ioi T, F τ / (a ^ 2 + τ ^ 2)) ≤ C * B / T ∧
        (∫ τ in Set.Iio (-T), F τ / (a ^ 2 + τ ^ 2)) ≤ C * B / T := by
  refine ⟨2, by norm_num, ?_⟩
  intro F hFc hFnn B a T ha hT hwin
  have hB : 0 ≤ B := by
    have h0 : (0 : ℝ) ≤ ∫ τ in (0 : ℝ)..1, F τ := integral_nonneg (by norm_num) (fun u _ => hFnn u)
    have h1 : (∫ τ in (0 : ℝ)..1, F τ) ≤ B := by simpa using hwin 0
    linarith
  refine ⟨Ioi_weighted_le F hFc hFnn B a T ha hT hB hwin, ?_⟩
  have hGc : Continuous (fun σ : ℝ => F (-σ)) := hFc.comp continuous_neg
  have hGnn : ∀ σ : ℝ, 0 ≤ F (-σ) := fun σ => hFnn (-σ)
  have hGwin : ∀ c : ℝ, (∫ τ in c..(c+1), F (-τ)) ≤ B := by
    intro c
    have h := hwin (-c - 1)
    have hEq : (∫ τ in c..(c+1), F (-τ)) = ∫ τ in (-c - 1)..((-c - 1) + 1), F τ := by
      rw [intervalIntegral.integral_comp_neg F]; congr 1 <;> ring
    rw [hEq]; exact h
  have hG := Ioi_weighted_le (fun σ : ℝ => F (-σ)) hGc hGnn B a T ha hT hB hGwin
  have hEq2 : (∫ τ in Set.Iio (-T), F τ / (a ^ 2 + τ ^ 2))
      = ∫ σ in Set.Ioi T, F (-σ) / (a ^ 2 + σ ^ 2) := by
    rw [integral_Iio_neg_eq_Ioi T (fun τ => F τ / (a ^ 2 + τ ^ 2))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro σ _
    ring
  rw [hEq2]
  exact hG

end Work.BMF.mrlas
