import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Cast.Defs

open Finset

namespace Commons.Algebra.BigOperators

/-- Reindexing a sum over `Icc 1 N` restricted to the multiples of `d ≥ 1`. -/
lemma sum_Icc_filter_dvd {M : Type*} [AddCommMonoid M] (d N : ℕ) (f : ℕ → M) :
    (∑ i ∈ (Finset.Icc 1 N).filter (fun i => d ∣ i), f i) =
      ∑ k ∈ Finset.Icc 1 (N / d), f (d * k) := by
  have hset : (Finset.Icc 1 N).filter (fun i => d ∣ i) =
      (Finset.Icc 1 (N / d)).image (fun k => d * k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, hk⟩
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h; rw [Nat.zero_mul] at hk; omega
        · exact h
      refine ⟨k, ⟨?_, ?_⟩, hk.symm⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · subst h; rw [Nat.mul_zero] at hk; omega
        · exact h
      · rw [Nat.le_div_iff_mul_le hdpos, Nat.mul_comm]
        omega
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h; rw [Nat.div_zero] at hk2; omega
        · exact h
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
      · exact Nat.mul_pos (by omega) (by omega)
      · calc d * k ≤ d * (N / d) := Nat.mul_le_mul_left d hk2
          _ ≤ N := Nat.mul_div_le N d
  have hinj : Set.InjOn (fun k => d * k) (↑(Finset.Icc 1 (N / d)) : Set ℕ) := by
    intro a ha b hb hab
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h
        rw [Nat.div_zero] at ha
        simp only [Finset.mem_coe, Finset.mem_Icc] at ha
        omega
      · exact h
    exact Nat.mul_left_cancel hdpos hab
  rw [hset, Finset.sum_image hinj]

end Commons.Algebra.BigOperators
