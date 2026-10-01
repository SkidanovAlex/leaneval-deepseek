import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.Nat

/-- For a sigma type with constant fiber over `ℕ`, equality is componentwise. -/
theorem sigma_const_ext {a b c d : ℕ} (h1 : a = c) (h2 : b = d) :
    (⟨a, b⟩ : Sigma fun _ : ℕ => ℕ) = ⟨c, d⟩ := by rw [h1, h2]

/-- Reindexing a double sum over `m < N` and `d ∈ (N-m).divisors` as a double sum over
`d ∈ Icc 1 N` and `e ∈ Icc 1 (N/d)`, with `m = N - d*e`. -/
theorem sum_range_divisors_reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    (∑ m ∈ Finset.range N, ∑ d ∈ (N - m).divisors, f m d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f (N - d * e) d := by
  have hL : (∑ m ∈ Finset.range N, ∑ d ∈ (N - m).divisors, f m d)
      = ∑ p ∈ (Finset.range N).sigma (fun m => (N - m).divisors), f p.1 p.2 :=
    Finset.sum_sigma' (Finset.range N) (fun m => (N - m).divisors) f
  have hR : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f (N - d * e) d)
      = ∑ q ∈ (Finset.Icc 1 N).sigma (fun d => Finset.Icc 1 (N / d)),
          f (N - q.1 * q.2) q.1 :=
    Finset.sum_sigma' (Finset.Icc 1 N) (fun d => Finset.Icc 1 (N / d))
      (fun d e => f (N - d * e) d)
  rw [hL, hR]
  refine Finset.sum_bij'
    (fun p _ => (⟨p.2, (N - p.1) / p.2⟩ : Sigma fun _ : ℕ => ℕ))
    (fun q _ => (⟨N - q.1 * q.2, q.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_ ?_
  · -- `(m, d) ↦ (d, (N - m)/d)` lands in `Icc 1 N × Icc 1 (N/d)`
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
    rw [Finset.mem_range] at hp1
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hp2
    have hpos : 0 < p.2 := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hne)
    have hle : p.2 ≤ N - p.1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    have hNle : N - p.1 ≤ N := Nat.sub_le N p.1
    rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hpos, le_trans hle hNle⟩, Nat.div_pos hle hpos, Nat.div_le_div_right hNle⟩
  · -- `(d, e) ↦ (N - d*e, d)` lands in `range N × (N - (N - d*e)).divisors`
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_sigma.mp hq
    rw [Finset.mem_Icc] at hq1 hq2
    obtain ⟨hq1a, hq1b⟩ := hq1
    obtain ⟨hq2a, hq2b⟩ := hq2
    have hq1pos : 0 < q.1 := hq1a
    have hq2pos : 0 < q.2 := hq2a
    have hmul : q.1 * q.2 ≤ N :=
      calc q.1 * q.2 ≤ q.1 * (N / q.1) := Nat.mul_le_mul_left q.1 hq2b
        _ ≤ N := Nat.mul_div_le N q.1
    rw [Finset.mem_sigma, Finset.mem_range, Nat.mem_divisors]
    exact ⟨Nat.sub_lt (lt_of_lt_of_le hq1pos hq1b) (Nat.mul_pos hq1pos hq2pos),
      by rw [Nat.sub_sub_self hmul]
         exact ⟨dvd_mul_right q.1 q.2, Nat.mul_ne_zero (ne_of_gt hq1pos) (ne_of_gt hq2pos)⟩⟩
  · -- left inverse
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
    rw [Finset.mem_range] at hp1
    obtain ⟨hdvd, _hne⟩ := Nat.mem_divisors.mp hp2
    refine sigma_const_ext ?_ rfl
    rw [Nat.mul_div_cancel' hdvd, Nat.sub_sub_self (Nat.le_of_lt hp1)]
  · -- right inverse
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_sigma.mp hq
    rw [Finset.mem_Icc] at hq1 hq2
    obtain ⟨hq1a, hq1b⟩ := hq1
    obtain ⟨hq2a, hq2b⟩ := hq2
    have hq1pos : 0 < q.1 := hq1a
    have hmul : q.1 * q.2 ≤ N :=
      calc q.1 * q.2 ≤ q.1 * (N / q.1) := Nat.mul_le_mul_left q.1 hq2b
        _ ≤ N := Nat.mul_div_le N q.1
    refine sigma_const_ext rfl ?_
    rw [Nat.sub_sub_self hmul, Nat.mul_div_right q.2 hq1pos]
  · -- the summands agree
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
    rw [Finset.mem_range] at hp1
    obtain ⟨hdvd, _hne⟩ := Nat.mem_divisors.mp hp2
    rw [Nat.mul_div_cancel' hdvd, Nat.sub_sub_self (Nat.le_of_lt hp1)]

end Commons.NumberTheory.Nat