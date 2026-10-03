import Mathlib
import Submission.Work.Analysis.Variation.RawFamily

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- For `0 < M` the indices `x` whose block `(M x, min (M (x+1)) K]` of the tiling of `(0, K]`
is full, i.e. `x < nb K M = ⌈K / M⌉`, are exactly those with `x * M < K`. -/
lemma lt_nb_iff_mul_lt {K M x : ℕ} (hM : 0 < M) : x < nb K M ↔ x * M < K := by
  show x < (K + M - 1) / M ↔ x * M < K
  rw [Nat.lt_div_iff_mul_lt hM]
  omega

/-- The raw dyadic family at scale `2 ^ m` is dominated by the tiling family: every nonzero value
`rawH a m k = a (2^m * k) - a (2^m * (k - k % 2))` (which occurs for `k` odd, and is then the
increment over the full aligned block `(2^m * (k-1), 2^m * k]`) is one of the blocks of size `2^m`
tiling `(0, K]`, namely the one with index `x = k - 1 < nb K (2^m)`, where
`min (2^m * (x+1)) K = 2^m * k`.  Hence the `ℓ^r` sum over the raw family is at most the `ℓ^r` sum
over the tiling family. -/
theorem rawLp_le_incLp {r : ℝ} (hr : 0 < r) (K m : ℕ) (a : ℕ → ℂ) :
    rawLp r K m a ≤ incLp r K (2 ^ m) a := by
  -- The heart of the argument: the inequality between the two `ℓ^r` sums.
  have key : (∑ k ∈ Finset.range (K / 2 ^ m + 1), ‖rawH a m k‖ₑ ^ r)
      ≤ (∑ x ∈ Finset.range (nb K (2 ^ m)),
          ‖a (min (2 ^ m * (x + 1)) K) - a (2 ^ m * x)‖ₑ ^ r) := by
    -- Every index of the raw family is a multiple of `2 ^ m` not exceeding `K`.
    have hbound : ∀ k ∈ Finset.range (K / 2 ^ m + 1), 2 ^ m * k ≤ K := by
      intro k hk
      have hk' : k ≤ K / 2 ^ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact (Nat.mul_le_mul_left _ hk').trans (Nat.mul_div_le K (2 ^ m))
    -- At an odd index `k` the raw summand is the tiling summand at index `k - 1`.
    have hterm : ∀ k ∈ (Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1),
        ‖rawH a m k‖ₑ ^ r
          = ‖a (min (2 ^ m * ((k - 1) + 1)) K) - a (2 ^ m * (k - 1))‖ₑ ^ r := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hkpos : 1 ≤ k := by
        have := Nat.mod_le k 2
        omega
      have h2mk : 2 ^ m * k ≤ K := hbound k hk1
      have hraw : rawH a m k = a (2 ^ m * k) - a (2 ^ m * (k - 1)) := by
        unfold rawH
        rw [hk2]
      rw [hraw, Nat.sub_add_cancel hkpos, min_eq_left h2mk]
    -- At an even index the raw summand vanishes.
    have hzero : ∀ k ∈ Finset.range (K / 2 ^ m + 1),
        k ∉ (Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1) →
        ‖rawH a m k‖ₑ ^ r = 0 := by
      intro k hk hkS
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · have hraw : rawH a m k = 0 := by
          unfold rawH
          rw [h0, Nat.sub_zero, sub_self]
        rw [hraw, enorm_zero, ENNReal.zero_rpow_of_pos hr]
      · exact absurd (Finset.mem_filter.mpr ⟨hk, h1⟩) hkS
    -- The map `k ↦ k - 1` sends the odd indices into the tiling index set.
    have hsub : ((Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1)).image
        (fun k => k - 1) ⊆ Finset.range (nb K (2 ^ m)) := by
      intro x hx
      obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hkpos : 1 ≤ k := by
        have := Nat.mod_le k 2
        omega
      have h2mk : 2 ^ m * k ≤ K := hbound k hk1
      have h2pos : 0 < 2 ^ m := by positivity
      have hxk : x < k := by omega
      have h2mk' : k * 2 ^ m ≤ K := by rw [Nat.mul_comm k (2 ^ m)]; exact h2mk
      exact Finset.mem_range.mpr
        ((lt_nb_iff_mul_lt h2pos).mpr ((Nat.mul_lt_mul_of_pos_right hxk h2pos).trans_le h2mk'))
    -- `k ↦ k - 1` is injective on the odd indices.
    have hinj : Set.InjOn (fun k : ℕ => k - 1)
        ((Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1) : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
      obtain ⟨-, hx2⟩ := hx
      obtain ⟨-, hy2⟩ := hy
      have hxle := Nat.mod_le x 2
      have hyle := Nat.mod_le y 2
      have hxy' : x - 1 = y - 1 := hxy
      omega
    calc (∑ k ∈ Finset.range (K / 2 ^ m + 1), ‖rawH a m k‖ₑ ^ r)
        = ∑ k ∈ (Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1),
            ‖rawH a m k‖ₑ ^ r :=
          (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
      _ = ∑ k ∈ (Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1),
            ‖a (min (2 ^ m * ((k - 1) + 1)) K) - a (2 ^ m * (k - 1))‖ₑ ^ r :=
          Finset.sum_congr rfl hterm
      _ = ∑ x ∈ ((Finset.range (K / 2 ^ m + 1)).filter (fun k => k % 2 = 1)).image
            (fun k => k - 1),
            ‖a (min (2 ^ m * (x + 1)) K) - a (2 ^ m * x)‖ₑ ^ r :=
          (Finset.sum_image
            (f := fun x => ‖a (min (2 ^ m * (x + 1)) K) - a (2 ^ m * x)‖ₑ ^ r)
            (g := fun k => k - 1) hinj).symm
      _ ≤ ∑ x ∈ Finset.range (nb K (2 ^ m)),
            ‖a (min (2 ^ m * (x + 1)) K) - a (2 ^ m * x)‖ₑ ^ r :=
          Finset.sum_le_sum_of_subset hsub
  rw [rawLp, incLp]
  exact ENNReal.rpow_le_rpow key (le_of_lt (one_div_pos.mpr hr))

end Work.Analysis.Variation
