import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.window_sum_summand
import Submission.Work.HP.ceil_logb_bounds

namespace Work.HP

open Finset

/-- Arithmetic bound for `κ = ⌈logb 2 (2^r * Kmink * (Δ+1))⌉₊` and `Δ ≥ 1`:
the two factors `2^((n-1)κ)` and `(1+κ)^2` are absorbed by `Δ^(n-1)` and
`(log (2Δ))^2` up to a constant depending only on `n`, `r` and `Kmink`. -/
theorem window_sum_const_aux (n r : ℕ) (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Δ : ℝ), 1 ≤ Δ →
      (2 : ℝ) ^ ((n - 1) * ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊)
        * (1 + ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊) ^ 2
      ≤ C * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ r * Kmink := by
    have := mul_le_mul h2r hKmink (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (2:ℝ) ^ r)
    simpa using this
  have hlogbX : 0 ≤ Real.logb 2 ((2 : ℝ) ^ r * Kmink) :=
    Real.logb_nonneg (by norm_num) hX1
  refine ⟨((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 : ℝ) ^ (n - 1)
      * ((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2) ^ 2, ?_, ?_⟩
  · have h1 : (0 : ℝ) < ((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) := by positivity
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := by positivity
    have h3 : (0 : ℝ) < (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 :=
      div_pos (by linarith) hlog2pos
    positivity
  · intro Δ hΔ
    set N := ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ with hN
    have hz1 : (1 : ℝ) ≤ (2 : ℝ) ^ r * Kmink * (Δ + 1) := by
      have hd1 : (1 : ℝ) ≤ Δ + 1 := by linarith
      have := mul_le_mul hX1 hd1 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (2:ℝ)^r * Kmink)
      simpa using this
    have hceil : (2 : ℝ) ^ N ≤ 2 * ((2 : ℝ) ^ r * Kmink * (Δ + 1)) := by
      rw [hN]; exact (ceil_logb_bounds hz1).2
    -- power bound
    have hpow : (2 : ℝ) ^ ((n - 1) * N)
        ≤ ((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 : ℝ) ^ (n - 1) * Δ ^ (n - 1) := by
      rw [show (n - 1) * N = N * (n - 1) by ring, pow_mul]
      calc ((2 : ℝ) ^ N) ^ (n - 1)
          ≤ (2 * ((2 : ℝ) ^ r * Kmink * (Δ + 1))) ^ (n - 1) :=
            pow_le_pow_left₀ (by positivity) hceil (n - 1)
        _ = ((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (Δ + 1) ^ (n - 1) := by
            rw [show (2 * ((2 : ℝ) ^ r * Kmink * (Δ + 1)))
                  = (2 * ((2 : ℝ) ^ r * Kmink)) * (Δ + 1) by ring, mul_pow]
        _ ≤ ((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 * Δ) ^ (n - 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) (n - 1)
        _ = ((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 : ℝ) ^ (n - 1) * Δ ^ (n - 1) := by
            rw [mul_pow]; ring
    -- log bound
    have hlog : (1 + (N : ℝ)) ^ 2
        ≤ ((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2) ^ 2 * (Real.log (2 * Δ)) ^ 2 := by
      have hNub : (N : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1)) + 1 := by
        rw [hN]
        exact le_of_lt (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hz1))
      have hsplit : Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))
          = Real.logb 2 ((2 : ℝ) ^ r * Kmink) + Real.logb 2 (Δ + 1) := by
        rw [Real.logb_mul (by positivity) (by positivity)]
      have hlogb_le : Real.logb 2 (Δ + 1) ≤ Real.log (2 * Δ) / Real.log 2 := by
        unfold Real.logb
        rw [div_le_div_iff_of_pos_right hlog2pos]
        exact Real.log_le_log (by linarith) (by linarith)
      have ht1 : (1 : ℝ) ≤ Real.log (2 * Δ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos, one_mul]
        exact Real.log_le_log (by norm_num) (by linarith)
      have ht0 : (0 : ℝ) ≤ Real.log (2 * Δ) / Real.log 2 := by linarith
      have hA : (0 : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 2 := by linarith
      have hstep : 1 + (N : ℝ)
          ≤ (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 * Real.log (2 * Δ) := by
        have e1 : 1 + (N : ℝ)
            ≤ Real.logb 2 ((2 : ℝ) ^ r * Kmink) + Real.log (2 * Δ) / Real.log 2 + 2 := by
          rw [hsplit] at hNub; linarith
        have e4 : (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 2 + 1) * (Real.log (2 * Δ) / Real.log 2)
            = (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 * Real.log (2 * Δ) := by
          field_simp
          ring
        have hcore : Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 2 + Real.log (2 * Δ) / Real.log 2
            ≤ (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 2 + 1) * (Real.log (2 * Δ) / Real.log 2) := by
          nlinarith [hA, ht1, ht0,
            mul_nonneg hA (by linarith : (0:ℝ) ≤ Real.log (2 * Δ) / Real.log 2 - 1)]
        linarith [e1, hcore, e4.le]
      have hn1 : (0 : ℝ) ≤ 1 + (N : ℝ) := by positivity
      have hn2 : (0 : ℝ) ≤ (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 * Real.log (2 * Δ) := by
        have h3 : (0 : ℝ) ≤ (Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 :=
          div_nonneg (by linarith) hlog2pos.le
        exact mul_nonneg h3 (Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Δ))
      calc (1 + (N : ℝ)) ^ 2
          ≤ ((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2 * Real.log (2 * Δ)) ^ 2 :=
            pow_le_pow_left₀ hn1 hstep 2
        _ = ((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2) ^ 2 * (Real.log (2 * Δ)) ^ 2 :=
            mul_pow _ _ 2
    calc (2 : ℝ) ^ ((n - 1) * N) * (1 + (N : ℝ)) ^ 2
        ≤ (((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 : ℝ) ^ (n - 1) * Δ ^ (n - 1))
          * (((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2) ^ 2 * (Real.log (2 * Δ)) ^ 2) :=
          mul_le_mul hpow hlog (sq_nonneg _) (by positivity)
      _ = (((2 : ℝ) * ((2 : ℝ) ^ r * Kmink)) ^ (n - 1) * (2 : ℝ) ^ (n - 1)
            * ((Real.logb 2 ((2 : ℝ) ^ r * Kmink) + 3) / Real.log 2) ^ 2)
            * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := by ring

theorem window_sum_arith (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (Cdya : ℝ) (hCdya : 0 < Cdya)
    (hdya : ∀ (L' : ℝ), 0 ≤ L' →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L'⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L'⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
        else 0))
      ≤ Cdya * 2 ^ (((n + 1) - 2) * L') * (1 + L') ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Δ : ℝ), 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ K * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  have _hrn : r ≤ n + 1 := hrn
  obtain ⟨Cb, hCbpos, hCb⟩ := window_sum_const_aux n r Kmink hKmink
  -- general `N` form of the transfer step
  have key : ∀ N : ℕ,
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ N then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ Cdya * (2 : ℝ) ^ ((n - 1) * N) * (1 + (N : ℝ)) ^ 2 := by
    intro N
    -- the summand of the target sum equals the summand of the dyadic hypothesis
    have hsum : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
              ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
                (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
          else 0))
        = (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
          else 0)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact if_congr Iff.rfl (window_sum_summand n r (by omega) hr k) rfl
    -- the dyadic hypothesis, instantiated at `L' = N`
    have hdy : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j, k j) ≤ N then
            (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
          else 0))
        ≤ Cdya * (2 : ℝ) ^ ((n - 1) * N) * (1 + (N : ℝ)) ^ 2 := by
      have h := hdya (N : ℝ) (Nat.cast_nonneg N)
      simp only [Nat.ceil_natCast] at h
      have hpoweq : (2 : ℝ) ^ (((n : ℝ) + 1 - 2) * (N : ℝ)) = (2 : ℝ) ^ ((n - 1) * N) := by
        have h1 : ((n : ℝ) + 1 - 2) = ((n - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; ring
        rw [h1, ← Nat.cast_mul, Real.rpow_natCast]
      rw [hpoweq] at h
      exact h
    exact hsum.le.trans hdy
  refine ⟨Cdya * Cb, mul_pos hCdya hCbpos, ?_⟩
  intro Δ hΔ
  have hbound := hCb Δ hΔ
  have hmin : 2 * min (r - 2) 1 = 2 := by
    rw [Nat.min_eq_right (by omega : 1 ≤ r - 2)]
  calc (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
              (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ Cdya * (2 : ℝ) ^ ((n - 1) * ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊)
          * (1 + (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ : ℝ)) ^ 2 :=
        key ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊
    _ = Cdya * ((2 : ℝ) ^ ((n - 1) * ⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊)
          * (1 + (⌈Real.logb 2 ((2 : ℝ) ^ r * Kmink * (Δ + 1))⌉₊ : ℝ)) ^ 2) := by ring
    _ ≤ Cdya * (Cb * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hCdya.le
    _ = (Cdya * Cb) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
        rw [hmin]; ring

end Work.HP
