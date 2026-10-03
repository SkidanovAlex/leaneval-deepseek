import Mathlib

namespace Work.FIArea7

/-- Reindexing lemma: a double sum over `n ∈ [1,N]` and divisors `a ∣ n` with `Y < a`,
of a term `F a (n / a)`, equals the sum over `a ∈ [Y+1,N]` and `m ∈ [1, N/a]` of `F a m`. -/
lemma sum_Icc_divisors_swap {M : Type*} [AddCommMonoid M] (N Y : ℕ) (F : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a), F a (n / a))
      = ∑ a ∈ Finset.Icc (Y + 1) N, ∑ m ∈ Finset.Icc 1 (N / a), F a m := by
  set A : Finset ℕ := Finset.Icc (Y + 1) N with hA
  have step0 : (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a), F a (n / a))
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ A, (if a ∣ n then F a (n / a) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : n.divisors.filter (fun a => Y < a) = A.filter (fun a => a ∣ n) := by
      rw [hA]
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, hn0⟩, hY⟩
        exact ⟨⟨by omega, le_trans (Nat.le_of_dvd (by omega) hdvd) hn.2⟩, hdvd⟩
      · rintro ⟨⟨ha1, haN⟩, hdvd⟩
        exact ⟨⟨hdvd, by omega⟩, by omega⟩
    rw [hset, Finset.sum_filter]
  rw [step0, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [hA] at ha
  have hapos : 0 < a := by rw [Finset.mem_Icc] at ha; omega
  have hlhs : (∑ n ∈ Finset.Icc 1 N, (if a ∣ n then F a (n / a) else 0))
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => a ∣ n), F a (n / a) := by
    rw [Finset.sum_filter]
  rw [hlhs]
  refine Finset.sum_bij' (fun n _ => n / a) (fun m _ => a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hnN⟩
    rw [Nat.one_le_div_iff hapos]
    exact Nat.le_of_dvd (by omega) hdvd
  · intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmN⟩ := hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right a m⟩
    · have h : 0 < a * m := Nat.mul_pos hapos (by omega)
      omega
    · calc a * m ≤ a * (N / a) := Nat.mul_le_mul_left a hmN
        _ ≤ N := Nat.mul_div_le N a
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _
    exact Nat.mul_div_cancel_left m hapos
  · intro n _
    rfl

theorem sum_Icc_divisors_double_gt {M : Type*} [AddCommMonoid M] (N Y : ℕ) (G : ℕ → ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a),
        ∑ b ∈ (n / a).divisors.filter (fun b => Y < b), G a b n)
      = ∑ a ∈ Finset.Icc (Y + 1) N, ∑ m ∈ Finset.Icc 1 (N / a),
          ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m) := by
  have hL : (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a),
        ∑ b ∈ (n / a).divisors.filter (fun b => Y < b), G a b n)
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a),
          ∑ b ∈ (n / a).divisors.filter (fun b => Y < b), G a b (a * (n / a)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b _
    obtain ⟨ha_div, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp ha_div
    rw [Nat.mul_div_cancel' hdvd]
  rw [hL]
  exact sum_Icc_divisors_swap N Y
    (fun a m => ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m))

end Work.FIArea7
