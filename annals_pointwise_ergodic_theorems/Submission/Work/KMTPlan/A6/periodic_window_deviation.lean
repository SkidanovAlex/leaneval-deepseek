import Mathlib

/-!
# Deviation of a windowed mean from the period mean (KMT A6)

For a `Q`-periodic function `w : ℤ → ℂ` with `‖w n‖ ≤ 1` and any integer window
`{N/2 + 1, …, N}` we have

  `‖(1/N) ∑_{N/2 < n ≤ N} w n - (1/(2Q)) ∑_{z < Q} w z‖ ≤ 3Q/N`.

The proof is the classical "block decomposition" of a periodic sequence: a sum of
`m` consecutive terms of a `Q`-periodic sequence equals `⌊m/Q⌋` full periods plus
a remainder of at most `m % Q` terms, each of modulus at most one; the window has
`c = N - N/2 = ⌈N/2⌉` terms, whence `2Q⌊c/Q⌋` differs from `N` by at most `2Q`.
-/

namespace Work.KMTPlan.A6

open Finset

/-- Shifting the index of a full-period sum of a `Q`-periodic function by one
does not change the sum. -/
private lemma period_sum_succ (w : ℤ → ℂ) (Q : ℕ)
    (hw : ∀ n : ℤ, w (n + (Q:ℤ)) = w n) (b : ℤ) :
    ∑ j ∈ Finset.range Q, w (b + 1 + (j:ℤ)) = ∑ j ∈ Finset.range Q, w (b + (j:ℤ)) := by
  set g : ℕ → ℂ := fun i => w (b + (i:ℤ)) with hg
  have hL : ∑ j ∈ Finset.range Q, w (b + 1 + (j:ℤ)) = ∑ j ∈ Finset.range Q, g (j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hg]
    congr 1
    push_cast
    ring
  rw [hL]
  have h1 : ∑ j ∈ Finset.range Q, g (j+1) + g 0 = ∑ j ∈ Finset.range (Q+1), g j :=
    (Finset.sum_range_succ' g Q).symm
  have h2 : ∑ j ∈ Finset.range (Q+1), g j = ∑ j ∈ Finset.range Q, g j + g Q :=
    Finset.sum_range_succ g Q
  have h3 : g Q = g 0 := by simpa [hg] using hw b
  have hgoal : ∑ j ∈ Finset.range Q, g (j+1) = ∑ j ∈ Finset.range Q, g j := by
    have : ∑ j ∈ Finset.range Q, g (j+1) + g 0 = ∑ j ∈ Finset.range Q, g j + g 0 := by
      rw [h1, h2, h3]
    exact add_right_cancel this
  rw [hgoal]

/-- A full-period sum of a `Q`-periodic function does not depend on where the
period is started. -/
private lemma period_sum_eq (w : ℤ → ℂ) (Q : ℕ)
    (hw : ∀ n : ℤ, w (n + (Q:ℤ)) = w n) (b : ℤ) :
    ∑ j ∈ Finset.range Q, w (b + (j:ℤ)) = ∑ j ∈ Finset.range Q, w ((j:ℤ)) := by
  refine Int.induction_on b ?_ ?_ ?_
  · simp
  · intro i ih
    have h := period_sum_succ w Q hw (i:ℤ)
    rw [h, ih]
  · intro i ih
    have h := period_sum_succ w Q hw (-(i:ℤ) - 1)
    have h2 : ∑ j ∈ Finset.range Q, w ((-(i:ℤ)) + (j:ℤ))
        = ∑ j ∈ Finset.range Q, w ((-(i:ℤ) - 1) + (j:ℤ)) := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    rw [← h2]
    exact ih

/-- `Q` terms followed by `m` further terms: a sum over `range (Q + m)` splits
into one full period plus the sum over `range m` beginning at the same point. -/
private lemma range_sum_add_Q (w : ℤ → ℂ) (Q : ℕ)
    (hw : ∀ n : ℤ, w (n + (Q:ℤ)) = w n) (b : ℤ) (m : ℕ) :
    ∑ j ∈ Finset.range (Q + m), w (b + (j:ℤ))
      = (∑ z ∈ Finset.range Q, w (z:ℤ)) + ∑ j ∈ Finset.range m, w (b + (j:ℤ)) := by
  rw [Finset.sum_range_add]
  congr 1
  · exact period_sum_eq w Q hw b
  · apply Finset.sum_congr rfl
    intro j hj
    push_cast
    rw [show b + ((Q:ℤ) + (j:ℤ)) = (b + (j:ℤ)) + (Q:ℤ) by ring]
    exact hw (b + (j:ℤ))

/-- Block decomposition of a sum of `m` consecutive terms of a `Q`-periodic
function: `⌊m/Q⌋` full periods plus a remainder of `m % Q` terms. -/
private lemma range_sum_decomp (w : ℤ → ℂ) (Q : ℕ)
    (hw : ∀ n : ℤ, w (n + (Q:ℤ)) = w n) (b : ℤ) (m : ℕ) :
    ∑ j ∈ Finset.range m, w (b + (j:ℤ))
      = ((m / Q : ℕ) : ℂ) * (∑ z ∈ Finset.range Q, w (z:ℤ))
        + ∑ j ∈ Finset.range (m % Q), w (b + (j:ℤ)) := by
  have key : ∀ k s : ℕ, ∑ j ∈ Finset.range (Q * k + s), w (b + (j:ℤ))
      = (k : ℂ) * (∑ z ∈ Finset.range Q, w (z:ℤ)) + ∑ j ∈ Finset.range s, w (b + (j:ℤ)) := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      have hQS : Q * (k+1) + s = Q + (Q * k + s) := by ring
      rw [hQS, range_sum_add_Q w Q hw b (Q*k+s), ih s]
      push_cast
      ring
  conv_lhs => rw [← Nat.div_add_mod m Q]
  exact key _ _

/-- Reindexing an integer interval `{a+1, …, b}` as `range (b - a)`. -/
private lemma sum_Ioc_eq_sum_range_int (w : ℤ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, w (n:ℤ) = ∑ j ∈ Finset.range (b - a), w ((a:ℤ) + 1 + (j:ℤ)) := by
  rw [show Finset.Ioc a b = Finset.Ico (a+1) (b+1) by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show b + 1 - (a + 1) = b - a by omega]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

/-- **Period-mean deviation of a window.**  The mean of a `Q`-periodic bounded
sequence over the window `{N/2 + 1, …, N}` differs from half the period mean by at
most `3Q/N`. -/
theorem periodic_window_deviation (w : ℤ → ℂ) (Q N : ℕ) (hQ : 0 < Q) (hN : 1 ≤ N)
    (hw : ∀ n : ℤ, w (n + (Q : ℤ)) = w n) (hw1 : ∀ n : ℤ, ‖w n‖ ≤ 1) :
    ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, w n
        - (2 * (Q : ℂ))⁻¹ * ∑ z ∈ Finset.range Q, w z‖ ≤ 3 * (Q : ℝ) / (N : ℝ) := by
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  set S : ℂ := ∑ z ∈ Finset.range Q, w z with hS
  set c : ℕ := N - N / 2 with hc
  set q : ℕ := c / Q with hq
  set r : ℕ := c % Q with hr
  -- elementary divisor facts
  have hqQ_le : q * Q ≤ c := by rw [hq]; exact Nat.div_mul_le_self c Q
  have hc_lt : c < q * Q + Q := by rw [hq]; exact Nat.lt_div_mul_add hQ
  have hc_eq : 2 * c = N + N % 2 := by
    rw [hc]
    have := Nat.div_add_mod N 2
    omega
  have hmod2 : N % 2 ≤ 1 := by
    have := Nat.mod_lt N (by norm_num : 0 < 2); omega
  have hr_lt : r < Q := by rw [hr]; exact Nat.mod_lt _ hQ
  -- their real-valued counterparts
  have hqQ_leR : (q:ℝ) * (Q:ℝ) ≤ (c:ℝ) := by exact_mod_cast hqQ_le
  have hc_ltR : (c:ℝ) < (q:ℝ) * (Q:ℝ) + (Q:ℝ) := by exact_mod_cast hc_lt
  have hc_eqR : 2 * (c:ℝ) = (N:ℝ) + ((N % 2 : ℕ):ℝ) := by exact_mod_cast hc_eq
  have hmod2R : ((N % 2 : ℕ):ℝ) ≤ 1 := by exact_mod_cast hmod2
  have h2c_ge : (N:ℝ) ≤ 2 * (c:ℝ) := by nlinarith [hc_eqR, hmod2R]
  -- `2*Q*⌊c/Q⌋` differs from `N` by at most `2*Q`
  have hb1 : 2 * (Q:ℝ) * (q:ℝ) ≤ (N:ℝ) + 1 := by nlinarith [hqQ_leR, hc_eqR, hmod2R]
  have hb2 : (N:ℝ) - 2*(Q:ℝ) ≤ 2*(Q:ℝ)*(q:ℝ) := by nlinarith [hc_ltR, h2c_ge]
  have hb3 : 2*(Q:ℝ)*(q:ℝ) - (N:ℝ) ≤ 2*(Q:ℝ) := by nlinarith [hb1, hQ1]
  have habs : |2*(Q:ℝ)*(q:ℝ) - (N:ℝ)| ≤ 2*(Q:ℝ) := by
    rw [abs_le']; exact ⟨hb3, by linarith⟩
  -- the coefficient `q/N - 1/(2Q)` of the period mean is at most `1/N`
  have hαeq : (q:ℝ)/(N:ℝ) - 1/(2*(Q:ℝ))
      = (2*(Q:ℝ)*(q:ℝ) - (N:ℝ))/(2*(Q:ℝ)*(N:ℝ)) := by
    field_simp
  have hα : |(q:ℝ)/(N:ℝ) - 1/(2*(Q:ℝ))| ≤ 1/(N:ℝ) := by
    rw [hαeq, abs_div]
    rw [abs_of_pos (by positivity : (0:ℝ) < 2*(Q:ℝ)*(N:ℝ))]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(Q:ℝ)*(N:ℝ))]
    have h2 : (1/(N:ℝ)) * (2*(Q:ℝ)*(N:ℝ)) = 2*(Q:ℝ) := by field_simp
    rw [h2]
    exact habs
  -- block decomposition of the window sum
  set R : ℂ := ∑ j ∈ Finset.range r, w (((N/2 : ℕ) : ℤ) + 1 + (j:ℤ)) with hR
  have hwindow : ∑ n ∈ Finset.Ioc (N / 2) N, w n = (q : ℂ) * S + R := by
    exact (sum_Ioc_eq_sum_range_int w (a := N/2) (b := N) (Nat.div_le_self N 2)).trans
      (range_sum_decomp w Q hw (((N/2:ℕ):ℤ)+1) c)
  have hS_le : ‖S‖ ≤ (Q:ℝ) := by
    rw [hS]
    calc ‖∑ z ∈ Finset.range Q, w z‖ ≤ ∑ z ∈ Finset.range Q, ‖w z‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ Finset.range Q, (1:ℝ) := by
            apply Finset.sum_le_sum; intro z hz; exact hw1 (z:ℤ)
      _ = (Q:ℝ) := by simp
  have hR_le : ‖R‖ ≤ (r:ℝ) := by
    rw [hR]
    calc ‖∑ j ∈ Finset.range r, w (((N/2:ℕ):ℤ) + 1 + (j:ℤ))‖
          ≤ ∑ j ∈ Finset.range r, ‖w (((N/2:ℕ):ℤ) + 1 + (j:ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range r, (1:ℝ) := by
            apply Finset.sum_le_sum; intro j hj; exact hw1 _
      _ = (r:ℝ) := by simp
  have hB : ((N:ℂ)⁻¹ * (q:ℂ) - (2*(Q:ℂ))⁻¹)
      = (((q:ℝ)/(N:ℝ) - 1/(2*(Q:ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  have hB_le : ‖(N:ℂ)⁻¹ * (q:ℂ) - (2*(Q:ℂ))⁻¹‖ ≤ 1/(N:ℝ) := by
    rw [hB]
    exact (RCLike.norm_ofReal (K := ℂ) ((q:ℝ)/(N:ℝ) - 1/(2*(Q:ℝ)))).trans_le hα
  have hNinv : ‖((N:ℂ))⁻¹‖ = 1/(N:ℝ) := by rw [norm_inv]; simp
  have hr_leR : (r:ℝ) ≤ (Q:ℝ) - 1 := by
    have : r + 1 ≤ Q := hr_lt
    have h2 : (r:ℝ) + 1 ≤ (Q:ℝ) := by exact_mod_cast this
    linarith
  rw [hwindow]
  have hdecomp : (N:ℂ)⁻¹*((q:ℂ)*S + R) - (2*(Q:ℂ))⁻¹*S
      = ((N:ℂ)⁻¹*(q:ℂ) - (2*(Q:ℂ))⁻¹)*S + (N:ℂ)⁻¹*R := by ring
  rw [hdecomp]
  calc ‖((N:ℂ)⁻¹*(q:ℂ) - (2*(Q:ℂ))⁻¹)*S + (N:ℂ)⁻¹*R‖
      ≤ ‖((N:ℂ)⁻¹*(q:ℂ) - (2*(Q:ℂ))⁻¹)*S‖ + ‖(N:ℂ)⁻¹*R‖ := norm_add_le _ _
    _ ≤ ‖(N:ℂ)⁻¹*(q:ℂ) - (2*(Q:ℂ))⁻¹‖ * ‖S‖ + ‖(N:ℂ)⁻¹‖ * ‖R‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (1/(N:ℝ)) * (Q:ℝ) + (1/(N:ℝ)) * (r:ℝ) := by
        apply add_le_add
        · exact mul_le_mul hB_le hS_le (norm_nonneg _) (by positivity)
        · rw [hNinv]
          exact mul_le_mul_of_nonneg_left hR_le (by positivity)
    _ ≤ 3 * (Q:ℝ) / (N:ℝ) := by
        have hsum : (1/(N:ℝ)) * (Q:ℝ) + (1/(N:ℝ)) * (r:ℝ)
            = (1/(N:ℝ)) * ((Q:ℝ) + (r:ℝ)) := by ring
        rw [hsum]
        have hQr : (Q:ℝ) + (r:ℝ) ≤ 3*(Q:ℝ) := by linarith
        calc (1/(N:ℝ)) * ((Q:ℝ) + (r:ℝ)) ≤ (1/(N:ℝ)) * (3*(Q:ℝ)) :=
              mul_le_mul_of_nonneg_left hQr (by positivity)
          _ = 3 * (Q:ℝ) / (N:ℝ) := by ring

end Work.KMTPlan.A6
