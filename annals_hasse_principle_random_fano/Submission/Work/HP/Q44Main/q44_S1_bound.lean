import Mathlib

namespace Work.HP.Q44Main

/-- Geometric-sum bound: `∑_{i<n} 4^i ≤ 4^n / 3` for `n : ℕ`. -/
private lemma q44_geom_four_le (n : ℕ) : (∑ i ∈ Finset.range n, (4:ℝ)^i) ≤ (4:ℝ)^n / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h4 : (4:ℝ)^(n+1) = 4 * (4:ℝ)^n := by rw [pow_succ]; ring
    rw [h4]
    linarith

/--
Bound for the first dyadic sum `S₁` in the `ℓ^{(56)}` estimate: over all triples
`a ≤ b ≤ c` with `a + b + c ≤ N`, the sum of `2^{4a+2b+2c}` is at most
`2 (N+1)^2 2^{3N}`.

The proof writes `4a + 2b + 2c = 2a + 2(a+b+c) ≤ 2N + 2a`, so each term is at most
`2^{2N} · 4^a`; the outer variable satisfies `a ≤ N/3`, so the outer sum is a truncated
geometric series in `4^a`, bounded by `(4/3)·4^{N/3} ≤ (4/3)·2^N`.
-/
theorem q44_S1_bound (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) else 0))
    ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by
  -- Pointwise-in-`a` bound for the two inner sums.
  have hfa : ∀ a, (∑ b ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2:ℝ)^(4*a+2*b+2*c) else 0))
      ≤ ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (4:ℝ)^a := by
    intro a
    have h22 : (2:ℝ)^(2*a) = (4:ℝ)^a := by
      rw [show (4:ℝ) = 2^2 by norm_num]
      exact pow_mul 2 2 a
    have hstep : ∀ b c, (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2:ℝ)^(4*a+2*b+2*c) else 0)
        ≤ (2:ℝ)^(2*N) * (4:ℝ)^a := by
      intro b c
      by_cases h : a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
      · rw [ite_eq_left h]
        have hle : 4*a + 2*b + 2*c ≤ 2*N + 2*a := by omega
        calc (2:ℝ)^(4*a+2*b+2*c) ≤ (2:ℝ)^(2*N+2*a) := pow_le_pow_right₀ (by norm_num) hle
          _ = (2:ℝ)^(2*N) * (2:ℝ)^(2*a) := by rw [pow_add]
          _ = (2:ℝ)^(2*N) * (4:ℝ)^a := by rw [h22]
      · rw [ite_eq_right h]; positivity
    calc (∑ b ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
        (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2:ℝ)^(4*a+2*b+2*c) else 0))
        ≤ ∑ b ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1), (2:ℝ)^(2*N) * (4:ℝ)^a := by
          apply Finset.sum_le_sum; intro b hb
          apply Finset.sum_le_sum; intro c hc
          exact hstep b c
      _ = ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (4:ℝ)^a := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- For `a > N/3` every summand vanishes, so the outer sum may be truncated at `N/3`.
  have hsub : Finset.range (N/3+1) ⊆ Finset.range (N+1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ Finset.range (N+1), x ∉ Finset.range (N/3+1) →
      (∑ b ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
        (if x ≤ b ∧ b ≤ c ∧ x + b + c ≤ N then (2:ℝ)^(4*x+2*b+2*c) else 0)) = 0 := by
    intro x _ hxnot
    simp only [Finset.mem_range, not_lt] at hxnot
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    have hnc : ¬ (x ≤ b ∧ b ≤ c ∧ x + b + c ≤ N) := by
      rintro ⟨h1, h2, h3⟩
      omega
    rw [ite_eq_right hnc]
  calc (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) else 0))
      = ∑ a ∈ Finset.range (N/3+1), ∑ b ∈ Finset.range (N+1), ∑ c ∈ Finset.range (N+1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) else 0) :=
        (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ a ∈ Finset.range (N/3+1), ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (4:ℝ)^a :=
        Finset.sum_le_sum (fun a _ => hfa a)
    _ = ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (∑ a ∈ Finset.range (N/3+1), (4:ℝ)^a) := by
        rw [Finset.mul_sum]
    _ ≤ ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * ((4:ℝ)^(N/3+1)/3) := by
        apply mul_le_mul_of_nonneg_left (q44_geom_four_le (N/3+1))
        positivity
    _ = ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (4 * (4:ℝ)^(N/3) / 3) := by
        rw [pow_succ]; ring
    _ ≤ ((N:ℝ)+1)^2 * (2:ℝ)^(2*N) * (4 * (2:ℝ)^N / 3) := by
        apply mul_le_mul_of_nonneg_left
        · have h4A : (4:ℝ)^(N/3) ≤ (2:ℝ)^N := by
            have h2 : 2*(N/3) ≤ N := by omega
            have hp := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) h2
            rw [show (4:ℝ)^(N/3) = (2:ℝ)^(2*(N/3)) by
              rw [show (4:ℝ) = 2^2 by norm_num, pow_mul]]
            exact hp
          linarith
        · positivity
    _ = (4/3) * (((N:ℝ)+1)^2 * (2:ℝ)^(3*N)) := by
        have hpow : (2:ℝ)^(2*N) * (2:ℝ)^N = (2:ℝ)^(3*N) := by
          rw [← pow_add]; congr 1; ring
        rw [← hpow]; ring
    _ ≤ 2 * ((N:ℝ)+1)^2 * (2:ℝ)^(3*N) := by
        have hnn : (0:ℝ) ≤ ((N:ℝ)+1)^2 * (2:ℝ)^(3*N) := by positivity
        linarith

end Work.HP.Q44Main
