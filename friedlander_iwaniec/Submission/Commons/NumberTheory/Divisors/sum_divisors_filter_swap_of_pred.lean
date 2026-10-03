import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.Divisors

open Finset

theorem sum_divisors_filter_swap_of_pred {N : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ b ∈ n.divisors.filter p, F n b)
      = ∑ b ∈ (Finset.Icc 1 N).filter p,
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b := by
  have h1 : ∀ n ∈ Finset.Icc 1 N,
      (∑ b ∈ n.divisors.filter p, F n b)
        = ∑ b ∈ Finset.Icc 1 N, (if b ∣ n ∧ p b then F n b else 0) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hset : n.divisors.filter p = (Finset.Icc 1 N).filter (fun b => b ∣ n ∧ p b) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hbdvd, _⟩, hpb⟩
        have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hbdvd (by omega)
        have hbN : b ≤ N := le_trans (Nat.le_of_dvd (by omega) hbdvd) hnN
        exact ⟨⟨hb1, hbN⟩, hbdvd, hpb⟩
      · rintro ⟨⟨_, _⟩, hbdvd, hpb⟩
        exact ⟨⟨hbdvd, hn0⟩, hpb⟩
    rw [hset, Finset.sum_filter]
  calc
    (∑ n ∈ Finset.Icc 1 N, ∑ b ∈ n.divisors.filter p, F n b)
        = ∑ n ∈ Finset.Icc 1 N,
            ∑ b ∈ Finset.Icc 1 N, (if b ∣ n ∧ p b then F n b else 0) :=
          Finset.sum_congr rfl h1
    _ = ∑ b ∈ Finset.Icc 1 N,
            ∑ n ∈ Finset.Icc 1 N, (if b ∣ n ∧ p b then F n b else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ b ∈ Finset.Icc 1 N,
            ∑ n ∈ Finset.Icc 1 N, (if p b then (if b ∣ n then F n b else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro n _
          by_cases hb : p b <;> by_cases hd : b ∣ n <;> simp [hb, hd]
    _ = ∑ b ∈ Finset.Icc 1 N,
            (if p b then ∑ n ∈ Finset.Icc 1 N, (if b ∣ n then F n b else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : p b <;> simp [hb]
    _ = ∑ b ∈ Finset.Icc 1 N,
            (if p b then ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_filter]
    _ = ∑ b ∈ (Finset.Icc 1 N).filter p,
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b := by
          exact (Finset.sum_filter (p := p)
            (f := fun b => ∑ n ∈ (Finset.Icc 1 N).filter (fun n => b ∣ n), F n b)).symm

end Commons.NumberTheory.Divisors