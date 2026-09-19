import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.Commons.NumberTheory.DirichletCharacter.sum_characters_eq_sum_primitive_lifts

namespace Commons.NumberTheory.DirichletCharacter

theorem sum_filter_dvd_char_range {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d)
    (c N : ℕ) (hc : 0 < c) :
    ∑ n ∈ (Finset.range (N + 1)).filter (fun n => c ∣ n), (ψ (n : ZMod d) : ℂ)
      = (ψ (c : ZMod d) : ℂ) * ∑ k ∈ Finset.range (N / c + 1), (ψ (k : ZMod d) : ℂ) := by
  -- The multiples of `c` below `N` correspond bijectively to `k ≤ N / c`.
  have hset : (Finset.range (N + 1)).filter (fun n => c ∣ n)
      = (Finset.range (N / c + 1)).image (fun k => c * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, hdvd⟩
      refine ⟨n / c, ?_, Nat.mul_div_cancel' hdvd⟩
      have hle : n ≤ N := by omega
      have := Nat.div_le_div_right hle (c := c)
      omega
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, ⟨k, rfl⟩⟩
      have hk' : k ≤ N / c := by omega
      have h1 : c * k ≤ c * (N / c) := Nat.mul_le_mul_left c hk'
      have h2 := Nat.mul_div_le N c
      omega
  rw [hset, Finset.sum_image (fun x _ y _ h => Nat.mul_left_cancel hc h)]
  -- Each summand `ψ (c * k)` factors as `ψ c * ψ k`.
  have hterm : ∀ k, (ψ (((c * k : ℕ) : ZMod d)) : ℂ)
      = (ψ (c : ZMod d) : ℂ) * (ψ (k : ZMod d) : ℂ) := by
    intro k
    rw [Nat.cast_mul, map_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.mul_sum]

end Commons.NumberTheory.DirichletCharacter