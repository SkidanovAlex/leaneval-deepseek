/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Transferring a window-sum bound from length `L` to length `M`

This file proves the elementary "block transfer" estimate behind the peeling step of §5 of
Krause–Mirek–Tao: if `ψ` is supported in the symmetric interval `[-N,N]` and bounded by `1`, then
the sum over `x ∈ [-N,N]` of the squares of the *`M`-window* sums of `ψ` is controlled by the
corresponding sum of the *`L`-window* sums (`L ≤ M`), with the loss of the number of `L`-blocks
`K = ⌈M/L⌉` in the main term and a single block's worth of `L² · #[-N,N]` in the error term:

`∑_{x ∈ [-N,N]} |∑_{y ≤ M} ψ(x+y)|² ≤ 2 K² ∑_{x ∈ [-N,N]} |∑_{y ≤ L} ψ(x+y)|² + 2 L² #[-N,N]`.

The mechanism is the exact block decomposition

`∑_{y ≤ K L} ψ(x+y) = ∑_{j < K} ∑_{y ≤ L} ψ(x + jL + y)`

(right-hand side: the `K` consecutive length-`L` windows), the observation that a length-`M` window
is a length-`K L` window minus the at most `L` terms of the excess, Cauchy–Schwarz over the `K`
blocks, and the *support* condition: the length-`L` window sum `x ↦ ∑_{y ≤ L} ψ(x+y)` vanishes for
`N ≤ x`, so shifting its summation index by the non-negative amount `jL` can only remove terms from
the sum over `[-N,N]`.

## Reference

B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Ann. of Math. **195** (2022), §5.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Peel

/-! ## Two elementary auxiliary lemmas -/

/-- Cauchy–Schwarz for a finite sum in `ℂ`: `‖∑_{i ∈ s} f i‖² ≤ #s · ∑_{i ∈ s} ‖f i‖²`. -/
lemma norm_sum_sq_le_card_mul_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have h2 : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  linarith

/-- Block decomposition of a half-open interval of naturals: the interval `[1, K L]` is the
disjoint union of the `K` blocks `[jL+1, jL+L]`, `j < K`. -/
lemma sum_range_Ico_blocks (K L : ℕ) (g : ℕ → ℂ) :
    (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Ico (j * L + 1) (j * L + L + 1), g y)
      = ∑ z ∈ Finset.Ico 1 (K * L + 1), g z := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul]
    rw [← Finset.sum_Ico_consecutive g (show 1 ≤ K * L + 1 by omega)
      (show K * L + 1 ≤ K * L + L + 1 by omega)]

/-- Block decomposition of a closed interval of naturals: the interval `[1, K L]` is the disjoint
union of the `K` blocks `[jL+1, jL+L]`, `j < K`. -/
lemma sum_range_Icc_blocks (K L : ℕ) (g : ℕ → ℂ) :
    (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc (j * L + 1) (j * L + L), g y)
      = ∑ z ∈ Finset.Icc 1 (K * L), g z := by
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  exact sum_range_Ico_blocks K L g

/-- Reindexing a sum over `[a,b]` by a constant shift: `∑_{y ∈ [a,b]} g (c + y) = ∑_{z ∈ [c+a,c+b]} g z`. -/
lemma sum_Icc_add_const (g : ℕ → ℂ) (c a b : ℕ) :
    (∑ y ∈ Finset.Icc a b, g (c + y)) = ∑ z ∈ Finset.Icc (c + a) (c + b), g z := by
  rw [← Finset.Ico_add_one_right_eq_Icc (c + a) (c + b),
      ← Finset.Ico_add_one_right_eq_Icc a b]
  rw [Finset.sum_Ico_add g a (b + 1) c]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_Ico]
  omega

/-- Shifting the summation index over `[-N,N]` by a *non-negative* amount `c` can only lose terms,
for a non-negative function `G` that vanishes on `[N,∞)`: the shifted index set
`[-N,N] + c = [-N+c, N+c]` meets `(-∞, N-1]` in a subset of `[-N,N] ∩ (-∞,N-1]`. -/
lemma sum_symIcc_pos_shift_le {N : ℕ} {c : ℤ} (hc : 0 ≤ c) {G : ℤ → ℝ}
    (hG0 : ∀ u, 0 ≤ G u) (hGN : ∀ u, (N : ℤ) ≤ u → G u = 0) :
    ∑ x ∈ Work.Peluse.symIcc N, G (x + c) ≤ ∑ x ∈ Work.Peluse.symIcc N, G x := by
  have hA : ∑ x ∈ Work.Peluse.symIcc N, G (x + c)
      = ∑ x ∈ (Work.Peluse.symIcc N).filter (fun x => x + c < (N : ℤ)), G (x + c) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : x + c < (N : ℤ)
    · simp [h]
    · have h2 : (N : ℤ) ≤ x + c := by omega
      simp [h, hGN (x + c) h2]
  rw [hA]
  have hinj : Set.InjOn (fun x : ℤ => x + c)
      ↑((Work.Peluse.symIcc N).filter (fun x => x + c < (N : ℤ))) := by
    intro a _ b _ hab
    have hab' : a + c = b + c := hab
    omega
  rw [← Finset.sum_image (f := G) hinj]
  have hsub1 : ((Work.Peluse.symIcc N).filter (fun x => x + c < (N : ℤ))).image (fun x => x + c)
      ⊆ Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1) := by
    intro u hu
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc, Work.Peluse.symIcc] at hu ⊢
    obtain ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, rfl⟩ := hu
    omega
  have hsub2 : Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1) ⊆ Work.Peluse.symIcc N := by
    intro u hu
    simp only [Finset.mem_Icc, Work.Peluse.symIcc] at hu ⊢
    omega
  calc ∑ x ∈ ((Work.Peluse.symIcc N).filter (fun x => x + c < (N : ℤ))).image
          (fun x => x + c), G x
      ≤ ∑ u ∈ Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1), G u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun i _ _ => hG0 i)
    _ ≤ ∑ x ∈ Work.Peluse.symIcc N, G x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => hG0 i)

/-! ## The block transfer -/

theorem windowSum_block_transfer {N M L : ℕ} (hL : 1 ≤ L) (hLM : L ≤ M) (ψ : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → ψ x = 0)
    (hbd : ∀ x : ℤ, ‖ψ x‖ ≤ 1) :
    (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ))‖ ^ 2)
      ≤ 2 * (((M + L - 1) / L : ℕ) : ℝ) ^ 2
          * (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 L, ψ (x + (y : ℤ))‖ ^ 2)
        + 2 * (L : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
  classical
  -- the number of length-`L` blocks and the two interval sums
  set K : ℕ := (M + L - 1) / L with hKdef
  set Ω : Finset ℤ := Work.Peluse.symIcc N with hΩdef
  set Q : ℝ := ∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 L, ψ (x + (y : ℤ))‖ ^ 2 with hQdef
  -- arithmetic: `M ≤ K L` and `K L ≤ M + L - 1`
  have hLpos : 0 < L := hL
  have hKL : K * L ≤ M + L - 1 := by
    rw [hKdef]; exact Nat.div_mul_le_self _ _
  have hMKL : M ≤ K * L := by
    by_contra h
    simp only [not_le] at h
    have h' : (K + 1) * L ≤ M + L - 1 := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 := (Nat.le_div_iff_mul_le hLpos).mpr h'
    rw [hKdef] at h2
    omega
  -- the two windows and the excess
  -- pointwise decomposition of the `M`-window sum
  have hpoint : ∀ x : ℤ,
      ‖∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ))‖ ^ 2
        ≤ 2 * ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
              ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2
          + 2 * ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2 := by
    intro x
    have hsplit : (∑ z ∈ Finset.Icc 1 M, ψ (x + (z : ℤ)))
        + (∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ)))
        = ∑ z ∈ Finset.Icc 1 (K * L), ψ (x + (z : ℤ)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) M,
        ← Finset.Ico_add_one_right_eq_Icc (M + 1) (K * L),
        ← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) (K * L)]
      exact Finset.sum_Ico_consecutive (fun z : ℕ => ψ (x + (z : ℤ))) (by omega)
        (by omega)
    have hblocks : (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
          ψ (x + ((j * L + y : ℕ) : ℤ)))
        = ∑ z ∈ Finset.Icc 1 (K * L), ψ (x + (z : ℤ)) := by
      calc (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
              ψ (x + ((j * L + y : ℕ) : ℤ)))
          = ∑ j ∈ Finset.range K, ∑ z ∈ Finset.Icc (j * L + 1) (j * L + L),
              ψ (x + (z : ℤ)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simpa using sum_Icc_add_const (fun z : ℕ => ψ (x + (z : ℤ))) (j * L) 1 L
        _ = ∑ z ∈ Finset.Icc 1 (K * L), ψ (x + (z : ℤ)) :=
            sum_range_Icc_blocks K L (fun z : ℕ => ψ (x + (z : ℤ)))
    have hsum : (∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ)))
        + (∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ)))
        = ∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
            ψ (x + ((j * L + y : ℕ) : ℤ)) := by
      rw [hsplit, hblocks]
    have hid : (∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ)))
        = (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ)))
          - (∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))) :=
      (eq_sub_iff_add_eq).mpr hsum
    rw [hid]
    have h2 : ‖(∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ)))
          - (∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ)))‖ ^ 2
        ≤ (‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖
            + ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    nlinarith [h2,
      sq_nonneg (‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖
        - ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖),
      norm_nonneg (∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))),
      norm_nonneg (∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ)))]
  -- the main term: Cauchy–Schwarz over the `K` blocks and the shift estimate
  have hshift : ∀ j : ℕ,
      ∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2 ≤ Q := by
    intro j
    have hpt : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ)))
        = ∑ y ∈ Finset.Icc 1 L, ψ ((x + ((j * L : ℕ) : ℤ)) + (y : ℤ)) := by
      intro x
      refine Finset.sum_congr rfl (fun y _ => ?_)
      congr 1
      push_cast
      ring
    have hG := sum_symIcc_pos_shift_le (N := N) (c := ((j * L : ℕ) : ℤ))
      (by positivity)
      (G := fun u : ℤ => ‖∑ y ∈ Finset.Icc 1 L, ψ (u + (y : ℤ))‖ ^ 2)
      (fun u => by positivity)
      (fun u hu => by
        have hzero : (∑ y ∈ Finset.Icc 1 L, ψ (u + (y : ℤ))) = 0 := by
          refine Finset.sum_eq_zero (fun y hy => ?_)
          refine hsup _ ?_
          intro hmem
          have hmem' : -(N : ℤ) ≤ u + (y : ℤ) ∧ u + (y : ℤ) ≤ (N : ℤ) := by
            simpa only [hΩdef, Work.Peluse.symIcc, Finset.mem_Icc] using hmem
          have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).1
          omega
        show ‖∑ y ∈ Finset.Icc 1 L, ψ (u + (y : ℤ))‖ ^ 2 = 0
        rw [hzero, norm_zero]
        norm_num)
    calc ∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2
        = ∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 L, ψ ((x + ((j * L : ℕ) : ℤ)) + (y : ℤ))‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [hpt x]
      _ ≤ Q := hG
  have hMainTerm : (∑ x ∈ Ω, ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
        ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2)
      ≤ (K : ℝ) * ((K : ℝ) * Q) := by
    calc (∑ x ∈ Ω, ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
          ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2)
        ≤ ∑ x ∈ Ω, (K : ℝ) * ∑ j ∈ Finset.range K,
            ‖∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2 := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          simpa [Finset.card_range] using
            norm_sum_sq_le_card_mul_sq (Finset.range K)
              (fun j => ∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ)))
      _ = (K : ℝ) * ∑ x ∈ Ω, ∑ j ∈ Finset.range K,
            ‖∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (K : ℝ) * ∑ j ∈ Finset.range K, ∑ x ∈ Ω,
            ‖∑ y ∈ Finset.Icc 1 L, ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2 := by
          rw [Finset.sum_comm]
      _ ≤ (K : ℝ) * ∑ j ∈ Finset.range K, Q := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hshift j)) ?_
          positivity
      _ = (K : ℝ) * ((K : ℝ) * Q) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the error term: the excess is at most `L` terms, each of norm at most `1`
  have hErr : (∑ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2)
      ≤ (L : ℝ) ^ 2 * (Ω.card : ℝ) := by
    have hcardle : (Finset.Icc (M + 1) (K * L)).card ≤ L := by
      have hsub : Finset.Icc (M + 1) (K * L) ⊆ Finset.Icc (M + 1) (M + L - 1) := by
        intro z hz
        simp only [Finset.mem_Icc] at hz ⊢
        omega
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hcard ⊢
      omega
    have hstep : ∀ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2
        ≤ (L : ℝ) ^ 2 := by
      intro x _
      have h1 : ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ≤ (L : ℝ) := by
        calc ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖
            ≤ ∑ z ∈ Finset.Icc (M + 1) (K * L), ‖ψ (x + (z : ℤ))‖ := norm_sum_le _ _
          _ ≤ ∑ z ∈ Finset.Icc (M + 1) (K * L), (1 : ℝ) :=
              Finset.sum_le_sum (fun z _ => hbd _)
          _ = ((Finset.Icc (M + 1) (K * L)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (L : ℝ) := by exact_mod_cast hcardle
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (∑ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2)
        ≤ ∑ x ∈ Ω, (L : ℝ) ^ 2 := Finset.sum_le_sum hstep
      _ = (L : ℝ) ^ 2 * (Ω.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- assembly
  have hpointSum : (∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ))‖ ^ 2)
      ≤ 2 * (∑ x ∈ Ω, ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
              ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2)
        + 2 * (∑ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2) := by
    calc (∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ))‖ ^ 2)
        ≤ ∑ x ∈ Ω, (2 * ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
                ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2
              + 2 * ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2) :=
            Finset.sum_le_sum (fun x _ => hpoint x)
      _ = 2 * (∑ x ∈ Ω, ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
                ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2)
            + 2 * (∑ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc (∑ x ∈ Ω, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + (y : ℤ))‖ ^ 2)
      ≤ 2 * (∑ x ∈ Ω, ‖∑ j ∈ Finset.range K, ∑ y ∈ Finset.Icc 1 L,
              ψ (x + ((j * L + y : ℕ) : ℤ))‖ ^ 2)
        + 2 * (∑ x ∈ Ω, ‖∑ z ∈ Finset.Icc (M + 1) (K * L), ψ (x + (z : ℤ))‖ ^ 2) :=
          hpointSum
    _ ≤ 2 * ((K : ℝ) * ((K : ℝ) * Q)) + 2 * ((L : ℝ) ^ 2 * (Ω.card : ℝ)) := by
          have h1 := mul_le_mul_of_nonneg_left hMainTerm (by norm_num : (0 : ℝ) ≤ 2)
          have h2 := mul_le_mul_of_nonneg_left hErr (by norm_num : (0 : ℝ) ≤ 2)
          linarith
    _ = 2 * ((K : ℕ) : ℝ) ^ 2 * Q + 2 * (L : ℝ) ^ 2 * (Ω.card : ℝ) := by ring

end Work.Peluse.Peel
