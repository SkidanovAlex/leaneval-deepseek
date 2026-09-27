import Mathlib

namespace Work.Misiurewicz

open Finset

/-- Arithmetic form of the Galois connection for ceiling division:
for `M > 0`, `i < a ⌈/⌉ M` iff `i * M < a`. -/
theorem lt_ceilDiv_iff (a M i : ℕ) (hM : 0 < M) : i < a ⌈/⌉ M ↔ i * M < a := by
  rw [lt_iff_not_ge, ceilDiv_le_iff_le_mul hM, not_le, mul_comm]

/-- For `j < M` and `j < N`, the `j`-th congruence class in `[0, N)` is exactly the image
of the arithmetic progression `i ↦ j + i * M` for `i` in `range ((N - j) ⌈/⌉ M)`. -/
theorem sum_ceilDiv_eq_sum_filter (f : ℕ → ℝ) {M N j : ℕ} (hM : 0 < M) (hj : j < M)
    (hjN : j < N) :
    ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), f (j + i * M)
      = ∑ k ∈ (Finset.range N).filter (fun k => k % M = j), f k := by
  refine Finset.sum_nbij' (fun a => j + a * M) (fun b => b / M) ?_ ?_ ?_ ?_ (fun a _ => rfl)
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have h' : a * M < N - j := (lt_ceilDiv_iff (N - j) M a hM).1 ha
      have h2 := Nat.add_lt_add_right h' j
      rw [Nat.sub_add_cancel (le_of_lt hjN)] at h2
      rwa [Nat.add_comm (a * M) j] at h2
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hbN, hbmod⟩ := hb
    rw [Finset.mem_range]
    have hbm : j + (b / M) * M = b := by
      rw [mul_comm (b / M) M, ← hbmod]
      exact Nat.mod_add_div b M
    have hmul : (b / M) * M < N - j := by
      rw [Nat.lt_sub_iff_add_lt, Nat.add_comm ((b / M) * M) j, hbm]
      exact hbN
    exact (lt_ceilDiv_iff (N - j) M (b / M) hM).2 hmul
  · intro a _
    rw [Nat.add_mul_div_right j a hM, Nat.div_eq_of_lt hj, Nat.zero_add]
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨-, hbmod⟩ := hb
    rw [mul_comm (b / M) M, ← hbmod]
    exact Nat.mod_add_div b M

theorem sum_range_ceilDiv_range (f : ℕ → ℝ) {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N) :
    ∑ j ∈ Finset.range M, ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), f (j + i * M)
      = ∑ k ∈ Finset.range N, f k := by
  have hMpos : 0 < M := hM
  have step : ∀ j ∈ Finset.range M,
      ∑ i ∈ Finset.range ((N - j) ⌈/⌉ M), f (j + i * M)
        = ∑ k ∈ (Finset.range N).filter (fun k => k % M = j), f k := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact sum_ceilDiv_eq_sum_filter f hMpos hj (lt_of_lt_of_le hj hN)
  rw [Finset.sum_congr rfl step]
  exact Finset.sum_fiberwise_of_maps_to (g := fun k => k % M) (s := Finset.range N)
    (t := Finset.range M) (f := f) (fun k _ => Finset.mem_range.2 (Nat.mod_lt k hMpos))

end Work.Misiurewicz
