import Mathlib
import Submission.Work.Analysis.Variation.Defs

namespace Work.Analysis.Variation

/-! ### Elementary arithmetic of the tiling by blocks of length `M` -/

/-- For `K ≥ 1` the number of blocks is `(K - 1) / M + 1`. -/
private theorem bts_nb_eq (K M : ℕ) (hK : 0 < K) (hM : 0 < M) :
    nb K M = (K - 1) / M + 1 := by
  unfold nb
  have h1 : K + M - 1 = (K - 1) + M := by omega
  have h2 : (K - 1) + M = (K - 1) + M * 1 := by rw [Nat.mul_one]
  rw [h1, h2]
  exact Nat.add_mul_div_left (K - 1) 1 hM

/-- Every `k < K` lies in one of the `nb K M` blocks. -/
private theorem bts_div_lt_nb (K M k : ℕ) (hM : 0 < M) (hK : 0 < K) (hk : k < K) :
    k / M < nb K M := by
  rw [bts_nb_eq K M hK hM]
  have h1 : k / M ≤ (K - 1) / M := Nat.div_le_div_right (by omega)
  omega

/-- A block index `j < nb K M` starts below `K`. -/
private theorem bts_mul_lt_of_lt_nb (K M j : ℕ) (hM : 0 < M) (hj : j < nb K M) :
    M * j < K := by
  unfold nb at hj
  have h := (Nat.lt_div_iff_mul_lt hM).mp hj
  have h2 : (K + M - 1) - (M - 1) = K := by omega
  rw [h2] at h
  rw [Nat.mul_comm M j]
  exact h

/-- `k` is strictly below the end of its own block. -/
private theorem bts_lt_succ_block (M k : ℕ) (hM : 0 < M) :
    k < M * (k / M + 1) := by
  have h1 : M * (k / M) + k % M = k := Nat.div_add_mod k M
  have h2 : k % M < M := Nat.mod_lt k hM
  have h3 : M * (k / M + 1) = M * (k / M) + M := by rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The `j`-th block of the tiling of `(0, K]` is exactly the fiber of `k ↦ k / M` over `j`. -/
private theorem bts_filter_div_eq_Ico (K M j : ℕ) (hM : 0 < M) :
    (Finset.range K).filter (fun k => k / M = j)
      = Finset.Ico (M * j) (min (M * (j + 1)) K) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hkK, hkj⟩
    subst hkj
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_comm]
      exact Nat.div_mul_le_self k M
    · have := bts_lt_succ_block M k hM
      omega
  · rintro ⟨hle, hlt⟩
    refine ⟨by omega, ?_⟩
    exact Nat.div_eq_of_lt_le (by rw [Nat.mul_comm j M]; exact hle)
      (by rw [Nat.mul_comm (j + 1) M]; omega)

/-- Telescoping over a block of consecutive indices. -/
private theorem bts_telescoping_Ico {V : Type*} [AddCommGroup V] (f : ℕ → V) (a b : ℕ)
    (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a := by
  have h1 := Finset.sum_Ico_eq_sum_range (fun k => f (k + 1) - f k) a b
  have h2 := Finset.sum_range_sub (fun i => f (a + i)) (b - a)
  calc ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)
      = ∑ k ∈ Finset.range (b - a), (f (a + k + 1) - f (a + k)) := h1
    _ = ∑ k ∈ Finset.range (b - a), (f (a + (k + 1)) - f (a + k)) :=
        Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]
    _ = f (a + (b - a)) - f (a + 0) := h2
    _ = f b - f a := by rw [Nat.add_zero, Nat.add_sub_cancel' hab]

/-- **Tiling identity for the signed block increments.**  Let `M ≥ 1`, `K ≥ 0`, `f : ℕ → V` a
sequence in a `ℂ`-module `V` and `d : ℕ → Bool` an arbitrary sign sequence.  Then the signed sum of
the increments of `f` over the `nb K M = ⌈K/M⌉` tiling blocks `(M i, min (M (i+1)) K]` of `(0, K]`
equals the signed sum of the elementary increments `f (k+1) - f k` over `k < K`, where the sign of
`k` is the sign of its block index `k / M`.

This is the combinatorial step ("tiling identity") of the paper's Corollary `rm-bil`: it exhibits
every block-sign vector `d ∘ (· / M)` as a full sign vector on `{±1}^K`, which is what lets the
Rademacher supremum of the bilinear corollary be taken over `Fin K → Bool`.

Proof strategy.  Let `J = nb K M`.  For `j < J` put `b j = min (M * (j+1)) K`.  Elementary Nat
arithmetic (using `M ≥ 1`) gives: `nb K M = 0` for `K = 0`; `nb K M = (K-1)/M + 1` for `K ≥ 1`;
`M * j ≤ b j` and `M * j ≤ K` for `j < J`; and `k < K → k / M < J`.  Moreover, for `k < K`,
`k / M = j ↔ M * j ≤ k ∧ k < min (M * (j+1)) K` (this uses `Nat.div_eq_of_lt_le` and
`Nat.div_lt_iff_lt_mul`), whence
`(Finset.range K).filter (fun k => k / M = j) = Finset.Ico (M * j) (b j)`.
Both sides then equal `∑ j ∈ range J, ∑ k ∈ Finset.Ico (M*j) (b j), sgn (d j) • (f (k+1) - f k)`:
the left side by the telescoping `f (b j) - f (M*j) = ∑_{k ∈ Ico (M*j) (b j)} (f (k+1) - f k)`
and `Finset.smul_sum`; the right side by `Finset.sum_fiberwise_of_maps_to` (applied with
`g := fun k => k / M`, `t := range J`) followed by the description of the fibers above. -/
theorem bilinear_tiling_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K M : ℕ) (hM : 0 < M) (f : ℕ → V) (d : ℕ → Bool) :
    (∑ i : Fin (Work.Analysis.Variation.nb K M),
        Work.Analysis.Variation.sgn (d (i : ℕ)) •
          (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))))
      = ∑ k : Fin K, Work.Analysis.Variation.sgn (d ((k : ℕ) / M)) •
          (f ((k : ℕ) + 1) - f (k : ℕ)) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · -- `K = 0`: both sides are empty sums.
    have hnb : nb 0 M = 0 := by
      unfold nb
      rw [Nat.zero_add]
      exact Nat.div_eq_of_lt (Nat.sub_lt hM Nat.one_pos)
    rw [hnb]
    simp
  · -- `K ≥ 1`.
    have hL : ∑ i ∈ Finset.range (nb K M),
        sgn (d i) • (f (min (M * (i + 1)) K) - f (M * i))
        = ∑ j ∈ Finset.range (nb K M),
            ∑ k ∈ Finset.Ico (M * j) (min (M * (j + 1)) K),
              sgn (d j) • (f (k + 1) - f k) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < nb K M := Finset.mem_range.mp hj
      have hMj : M * j < K := bts_mul_lt_of_lt_nb K M j hM hjlt
      have hle1 : M * j ≤ M * (j + 1) := by rw [Nat.mul_add, Nat.mul_one]; exact Nat.le_add_right _ _
      have hle : M * j ≤ min (M * (j + 1)) K := by omega
      have htel := bts_telescoping_Ico f (M * j) (min (M * (j + 1)) K) hle
      rw [← htel, Finset.smul_sum]
    have hmaps : ∀ k ∈ Finset.range K, k / M ∈ Finset.range (nb K M) := fun k hk =>
      Finset.mem_range.mpr (bts_div_lt_nb K M k hM hK (Finset.mem_range.mp hk))
    have hfib := Finset.sum_fiberwise_of_maps_to (g := fun k => k / M) hmaps
      (f := fun k => sgn (d (k / M)) • (f (k + 1) - f k))
    have hR : ∑ k ∈ Finset.range K, sgn (d (k / M)) • (f (k + 1) - f k)
        = ∑ j ∈ Finset.range (nb K M),
            ∑ k ∈ Finset.Ico (M * j) (min (M * (j + 1)) K),
              sgn (d j) • (f (k + 1) - f k) := by
      rw [← hfib]
      refine Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr (bts_filter_div_eq_Ico K M j hM) fun k hk => ?_
      have hkI := Finset.mem_Ico.mp hk
      have hkj : k / M = j := Nat.div_eq_of_lt_le
        (by rw [Nat.mul_comm j M]; exact hkI.1)
        (by rw [Nat.mul_comm (j + 1) M]; omega)
      rw [hkj]
    calc (∑ i : Fin (Work.Analysis.Variation.nb K M),
          Work.Analysis.Variation.sgn (d (i : ℕ)) •
            (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))))
        = ∑ i ∈ Finset.range (nb K M),
            sgn (d i) • (f (min (M * (i + 1)) K) - f (M * i)) :=
          Fin.sum_univ_eq_sum_range
            (fun i => sgn (d i) • (f (min (M * (i + 1)) K) - f (M * i))) (nb K M)
      _ = ∑ j ∈ Finset.range (nb K M),
            ∑ k ∈ Finset.Ico (M * j) (min (M * (j + 1)) K),
              sgn (d j) • (f (k + 1) - f k) := hL
      _ = ∑ k ∈ Finset.range K,
            sgn (d (k / M)) • (f (k + 1) - f k) := hR.symm
      _ = ∑ k : Fin K, Work.Analysis.Variation.sgn (d ((k : ℕ) / M)) •
            (f ((k : ℕ) + 1) - f (k : ℕ)) :=
          (Fin.sum_univ_eq_sum_range
            (fun k => sgn (d (k / M)) • (f (k + 1) - f k)) K).symm

end Work.Analysis.Variation
