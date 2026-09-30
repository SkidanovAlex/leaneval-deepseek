import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reindexing the double sum `∑_{d ≤ N} ∑_{m ≤ N/d} F d m`

The hyperbola identity

`∑_{d ≤ N} ∑_{m ≤ N/d} F d m = ∑_{n ≤ N} ∑_{d ∣ n} F d (n/d)`

counts, in two ways, the pairs `(d, m)` of positive integers with `d * m ≤ N`: the left hand
side groups them by their first coordinate `d`, while the right hand side groups them by the
product `n = d * m` (the divisors of `n` index the possible first coordinates and the second
coordinate is recovered as `n / d`).

The proof below shows that each side equals the sum of `F` over the single finset of pairs
`{(d, m) : 1 ≤ d ≤ N, 1 ≤ m ≤ N, d * m ≤ N}`.
-/

namespace Work.BMF.KfPrimeSum

open Finset

/-- For `1 ≤ d`, the index range `1 ≤ m ≤ N / d` is the range `1 ≤ m ≤ N` restricted to
`d * m ≤ N`. -/
private lemma Icc_one_div_eq_filter (d N : ℕ) (hd : 1 ≤ d) :
    Finset.Icc 1 (N / d) = (Finset.Icc 1 N).filter (fun m => d * m ≤ N) := by
  have hd0 : 0 < d := by omega
  ext m
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨hm1, hm2⟩
    have h : m * d ≤ N := (Nat.le_div_iff_mul_le hd0).mp hm2
    exact ⟨⟨hm1, le_trans hm2 (Nat.div_le_self N d)⟩, by rwa [mul_comm] at h⟩
  · rintro ⟨⟨hm1, _⟩, hdm⟩
    refine ⟨hm1, (Nat.le_div_iff_mul_le hd0).mpr ?_⟩
    rwa [mul_comm] at hdm

/-- Membership in the hyperbola region `{p : 1 ≤ p.1 ≤ N, 1 ≤ p.2 ≤ N, p.1 * p.2 ≤ N}`. -/
private lemma mem_pairRegion_iff (N : ℕ) (p : ℕ × ℕ) :
    p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
      ↔ 1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N ∧ p.1 * p.2 ≤ N := by
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- For `1 ≤ n ≤ N`, the antidiagonal of `n` (the pairs of positive integers with product `n`) is
the fibre of the hyperbola region over the value `n` of the product map. -/
private lemma divisorsAntidiagonal_eq_filter_region (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    n.divisorsAntidiagonal
      = (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  ext p
  rw [Nat.mem_divisorsAntidiagonal, Finset.mem_filter, mem_pairRegion_iff]
  constructor
  · rintro ⟨hpn, _⟩
    have hpos : 0 < p.1 * p.2 := by omega
    have hp1pos : 0 < p.1 := Nat.pos_of_mul_pos_right hpos
    have hp2pos : 0 < p.2 := Nat.pos_of_mul_pos_left hpos
    have h1 : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hp2pos
    have h2 : p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left p.2 hp1pos
    exact ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, hpn⟩
  · rintro ⟨-, hpn⟩
    exact ⟨hpn, by omega⟩

/-- The product map sends the hyperbola region into `[1, N]`. -/
private lemma mapsTo_pairRegion (N : ℕ) :
    ∀ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
      p.1 * p.2 ∈ Finset.Icc 1 N := by
  intro p hp
  rw [mem_pairRegion_iff] at hp
  obtain ⟨hp11, -, hp21, -, hle⟩ := hp
  exact Finset.mem_Icc.mpr ⟨by simpa using Nat.mul_le_mul hp11 hp21, hle⟩

/-- The left hand side, grouped by the first coordinate, is the sum of `F` over the hyperbola
region. -/
private lemma lhs_eq_pairRegion (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m)
      = ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
          F p.1 p.2 := by
  calc (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (if d * m ≤ N then F d m else 0) := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        rw [← Finset.sum_filter]
        exact Finset.sum_congr (Icc_one_div_eq_filter d N (Finset.mem_Icc.mp hd).1)
          (fun m _ => rfl)
    _ = ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          (if p.1 * p.2 ≤ N then F p.1 p.2 else 0) := by
        exact (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
          (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then F p.1 p.2 else 0)).symm
    _ = ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
          F p.1 p.2 := by
        exact (Finset.sum_filter (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))
          (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) (fun p : ℕ × ℕ => F p.1 p.2)).symm

/-- The right hand side, grouped by the product, is the sum of `F` over the hyperbola region. -/
private lemma rhs_eq_pairRegion (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d))
      = ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun p : ℕ × ℕ => p.1 * p.2 ≤ N),
          F p.1 p.2 := by
  have step1 : (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d))
      = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact (Nat.sum_divisorsAntidiagonal (fun d m => F d m)).symm
  rw [step1]
  rw [← Finset.sum_fiberwise_of_maps_to
        (s := ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p : ℕ × ℕ => p.1 * p.2 ≤ N))
        (t := Finset.Icc 1 N) (g := fun p : ℕ × ℕ => p.1 * p.2)
        (f := fun p : ℕ × ℕ => F p.1 p.2) (mapsTo_pairRegion N)]
  exact Finset.sum_congr rfl (fun n hn =>
    Finset.sum_congr (divisorsAntidiagonal_eq_filter_region N n hn) (fun _ _ => rfl))

lemma sum_Icc_sigma_eq_sum_divisors (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m)
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d) :=
  (lhs_eq_pairRegion F N).trans (rhs_eq_pairRegion F N).symm

end Work.BMF.KfPrimeSum
