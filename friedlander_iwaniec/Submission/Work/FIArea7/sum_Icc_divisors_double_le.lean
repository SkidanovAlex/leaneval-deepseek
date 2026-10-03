import Mathlib

/-!
# Reindexing a double divisor sum

We prove the double-counting identity

`∑_{n ≤ N} ∑_{a ∣ n, a ≤ Y} ∑_{b ∣ n/a, b ≤ Y} G a b n
   = ∑_{a ≤ Y} ∑_{b ≤ Y} ∑_{m ≤ N/(a b)} G a b (a b m)`.

The bijection is `(n, a, b) ↦ (a, b, n/(a b))`, whose inverse is `(a, b, m) ↦ (a b m, a, b)`;
the conditions `a ∣ n`, `b ∣ n/a` are exactly `a b ∣ n`.

The proof goes in three steps.  First the two divisor filters `· ∣ n` with `· ≤ Y` are replaced
by `(Icc 1 Y).filter (· ∣ n)` (valid because `n ≥ 1`), and the filtered sums are turned into sums
of indicators.  Then the three independent sums over `Icc 1 N`, `Icc 1 Y`, `Icc 1 Y` are
commuted.  Finally, for fixed `a, b` the indicator `[a b ∣ n]` is removed by reindexing the
multiples of `a b` in `[1, N]` by `n ↦ n/(a b)`, which bijects them with `[1, N/(a b)]`.
-/

namespace Work.FIArea7

open Finset

/-- For `n ≥ 1`, the divisors of `n` that are `≤ Y` are exactly the `a ≤ Y` (with `a ≥ 1`)
dividing `n`. -/
lemma divisors_filter_le_eq_Icc_filter (n Y : ℕ) (hn : 1 ≤ n) :
    n.divisors.filter (fun a => a ≤ Y) = (Finset.Icc 1 Y).filter (fun a => a ∣ n) := by
  ext a
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, hn0⟩, hle⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
  · rintro ⟨⟨h1, hle⟩, hdvd⟩
    exact ⟨⟨hdvd, by omega⟩, hle⟩

/-- The inner double divisor sum over a single `n` is a sum of the indicators `[a * b ∣ n]`. -/
lemma inner_eq {M : Type*} [AddCommMonoid M] (n Y : ℕ) (hn : 1 ≤ n) (G : ℕ → ℕ → ℕ → M) :
    (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
        ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y), G a b n)
      = ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
          (if a * b ∣ n then G a b n else 0) := by
  rw [divisors_filter_le_eq_Icc_filter n Y hn, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mem_Icc] at ha
  by_cases hac : a ∣ n
  · rw [if_pos hac]
    have hna : 1 ≤ n / a := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hac
    rw [divisors_filter_le_eq_Icc_filter (n / a) Y hna, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [if_congr (Nat.dvd_div_iff_mul_dvd hac) rfl rfl]
  · rw [if_neg hac]
    rw [Finset.sum_eq_zero]
    intro b hb
    rw [if_neg]
    intro hcontra
    exact hac (dvd_trans (dvd_mul_right a b) hcontra)

/-- Reindex the multiples of `a * b` in `[1, N]` by division: the map `n ↦ n/(a b)` is a bijection
onto `[1, N/(a b)]`, with inverse `m ↦ a b m`. -/
lemma sum_filter_mul_dvd_eq {M : Type*} [AddCommMonoid M] (a b N : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (H : ℕ → M) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => a * b ∣ n), H n)
      = ∑ m ∈ Finset.Icc 1 (N / (a * b)), H (a * b * m) := by
  have hab : 0 < a * b := Nat.mul_pos (by omega) (by omega)
  have hset : (Finset.Icc 1 N).filter (fun n => a * b ∣ n)
      = (Finset.Icc 1 (N / (a * b))).image (fun m => a * b * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdvd⟩
      refine ⟨n / (a * b), ⟨⟨?_, ?_⟩, ?_⟩⟩
      · rw [Nat.one_le_div_iff hab]; exact Nat.le_of_dvd (by omega) hdvd
      · exact Nat.div_le_div_right hnN
      · exact Nat.mul_div_cancel' hdvd
    · rintro ⟨m, ⟨⟨hm1, hmN⟩, rfl⟩⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · exact Nat.succ_le_of_lt (Nat.mul_pos hab (by omega))
      · calc a * b * m ≤ a * b * (N / (a * b)) := Nat.mul_le_mul_left _ hmN
          _ ≤ N := Nat.mul_div_le N (a * b)
  rw [hset]
  exact Finset.sum_image (fun x hx y hy hxy => Nat.mul_left_cancel hab hxy)

/-- Commuting the three independent sums. -/
lemma sum_comm3 {M : Type*} [AddCommMonoid M] {α β γ : Type*}
    (s : Finset α) (t : Finset β) (u : Finset γ) (f : α → β → γ → M) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z) = ∑ y ∈ t, ∑ z ∈ u, ∑ x ∈ s, f x y z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y hy
  rw [Finset.sum_comm]

theorem sum_Icc_divisors_double_le {M : Type*} [AddCommMonoid M] (N Y : ℕ) (G : ℕ → ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
        ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y), G a b n)
      = ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
          ∑ m ∈ Finset.Icc 1 (N / (a * b)), G a b (a * b * m) := by
  classical
  trans ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
          (if a * b ∣ n then G a b n else 0)
  · refine Finset.sum_congr rfl ?_
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact inner_eq n Y hn.1 G
  trans ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 N,
          (if a * b ∣ n then G a b n else 0)
  · exact sum_comm3 _ _ _ _
  · refine Finset.sum_congr rfl ?_
    intro a ha
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [Finset.mem_Icc] at ha hb
    rw [← Finset.sum_filter]
    exact sum_filter_mul_dvd_eq a b N ha.1 hb.1 (fun n => G a b n)

end Work.FIArea7
