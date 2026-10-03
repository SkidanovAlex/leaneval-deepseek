import Mathlib
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.sharpNorm_two_FIgtil
import Submission.Work.FIChain.prod_inv_le_of_window_bounds
import Submission.Work.FIChain.window_sum_FIgtil_le
import Submission.Work.FIChain.sieveDens_le_one_sub

/-!
# `Work.FIChain.zprime_prod_le`

The `z`-part of the FI endgame: the §6 Euler product over the *small* primes
`p < Δ^{1/19}` is bounded by a constant times the same product over *all* primes
`p < Δ`.  This is the "prime-by-prime" comparison `∏_{p<z} ↔ ∏_{p<Δ}` (second
Mertens theorem over the window `Δ^{1/19} ≤ p < Δ`, whose `log log`-width is
`log 19 + O(1)`).

Write `g̃ = Submission.ASP.FIgtil`, `x_p = g̃(p)`, `t_p = p^{-1/log Δ}` and
`f_p = 1 − g̃(p)·hSieveC g̃ (1/log Δ) p`.  For a prime,

    f_p = (1 − x_p)/(1 + t_p x_p)   and   f_p⁻¹ = (1 + t_p x_p)/(1 − x_p),

so `f_p⁻¹ ≤ exp(t_p x_p + x_p + 3 x_p²)` (`Work.FIChain.factor_inv_le_exp`).
Since `primesBelow ⌈Δ^{1/19}⌉ ⊆ primesBelow Δ`, the two products differ by the
window `W = {p < Δ : p ≥ ⌈Δ^{1/19}⌉}`:

    ∏_{p<Δ} f_p = (∏_{p<z} f_p) · (∏_{p∈W} f_p),

hence `∏_{p<z} f_p = (∏_{p<Δ} f_p)·(∏_{p∈W} f_p)⁻¹`, and it suffices to bound
`(∏_{p∈W} f_p)⁻¹` by a constant.  Multiplying the pointwise bounds and using
`t_p ≤ 1`, `x_p ≤ 2/3` (so `3 x_p² ≤ 2 x_p`),

    (∏_{p∈W} f_p)⁻¹ ≤ exp(Σ_{p∈W} (t_p x_p + x_p + 3 x_p²)) ≤ exp(4 Σ_{p∈W} x_p),

and the second Mertens bound `Work.FIChain.window_sum_FIgtil_le` with the window
`[⌈Δ^{1/19}⌉, Δ]` gives `Σ_{p∈W} x_p ≤ log log Δ − log log ⌈Δ^{1/19}⌉ + C ≤ log 19 + C`,
because `log⌈Δ^{1/19}⌉ ≥ (1/19) log Δ`.  This yields `K = exp(4(log 19 + C))`. -/

namespace Work.FIChain

open Finset
open scoped BigOperators

theorem zprime_prod_le :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      (∏ p ∈ Nat.primesBelow (⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊),
          (1 - Submission.ASP.FIgtil p * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p))
        ≤ K * ∏ p ∈ Nat.primesBelow Δ,
            (1 - Submission.ASP.FIgtil p * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p) := by
  -- the second Mertens bound over a window, and the uniform "factor `< 1`" bound
  obtain ⟨C, hCnn, hCwin⟩ := Work.FIChain.window_sum_FIgtil_le
  obtain ⟨δ, hδpos, hδ⟩ := Work.FIChain.sieveDens_le_one_sub
  refine ⟨Real.exp (4 * (Real.log 19 + C)), Real.exp_pos _, ?_⟩
  intro Δ hΔ
  set N : ℕ := ⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊ with hNdef
  set ε : ℝ := 1 / Real.log (Δ : ℝ) with hεdef
  have hΔpos : (0:ℝ) < (Δ:ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hΔ1 : (1:ℝ) < (Δ:ℝ) := by exact_mod_cast (by omega : 1 < Δ)
  have hlogΔ : 0 < Real.log (Δ:ℝ) := Real.log_pos hΔ1
  have hεnn : 0 ≤ ε := by rw [hεdef]; positivity
  have hNge : ((Δ:ℝ) ^ ((1:ℝ)/19)) ≤ (N:ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  -- `2 ≤ N`
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    have h1 : (1:ℝ) < ((Δ:ℝ) ^ ((1:ℝ)/19)) := Real.one_lt_rpow hΔ1 (by norm_num)
    have h2 : (1:ℝ) < (⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊ : ℝ) := lt_of_lt_of_le h1 (Nat.le_ceil _)
    have hN1 : 1 < ⌈((Δ : ℝ) ^ ((1 : ℝ) / 19))⌉₊ := by exact_mod_cast h2
    omega
  -- `N ≤ Δ`, so `primesBelow N ⊆ primesBelow Δ`
  have hNΔ : N ≤ Δ := by
    rw [hNdef, Nat.ceil_le]
    have h1 : (Δ:ℝ) ^ ((1:ℝ)/19) ≤ (Δ:ℝ) ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hΔ1) (by norm_num)
    rwa [Real.rpow_one] at h1
  -- `log log Δ - log log N ≤ log 19`
  have hll : Real.log (Real.log (Δ:ℝ)) - Real.log (Real.log (N:ℝ)) ≤ Real.log 19 := by
    have hlogN_pos : 0 < Real.log (N:ℝ) := by
      apply Real.log_pos
      have h2 : (1:ℝ) < (N:ℝ) := lt_of_lt_of_le (Real.one_lt_rpow hΔ1 (by norm_num)) hNge
      exact_mod_cast h2
    have h1 : (1/19) * Real.log (Δ:ℝ) ≤ Real.log (N:ℝ) := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hΔpos _) hNge
      rwa [Real.log_rpow hΔpos] at h
    have h2 : Real.log ((1/19) * Real.log (Δ:ℝ)) ≤ Real.log (Real.log (N:ℝ)) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log ((1/19) * Real.log (Δ:ℝ)) = Real.log (Real.log (Δ:ℝ)) - Real.log 19 := by
      have : (1/19) * Real.log (Δ:ℝ) = Real.log (Δ:ℝ) / 19 := by ring
      rw [this, Real.log_div (ne_of_gt hlogΔ) (by norm_num : (19:ℝ) ≠ 0)]
    linarith [h2, h3]
  set f : ℕ → ℝ := fun p => 1 - Submission.ASP.FIgtil p * Work.FIChain.hSieveC Submission.ASP.FIgtil ε p
    with hfdef
  set S : Finset ℕ := (Nat.primesBelow Δ).filter (fun p : ℕ => N ≤ (p:ℝ) ∧ (p:ℝ) < (Δ:ℝ))
    with hSdef
  -- the sieve factor is bounded below uniformly
  have hfpos : ∀ p ∈ Nat.primesBelow Δ, 0 < f p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hb := hδ ε hεnn p hpp
    rw [hfdef]
    linarith
  -- the window is exactly `primesBelow Δ \ primesBelow N`
  have hS_eq : S = Nat.primesBelow Δ \ Nat.primesBelow N := by
    rw [hSdef]
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpΔ, hpp⟩, hNp, -⟩
      refine ⟨⟨hpΔ, hpp⟩, ?_⟩
      intro hmem
      have hNp' : N ≤ p := by exact_mod_cast hNp
      omega
    · rintro ⟨⟨hpΔ, hpp⟩, hnot⟩
      refine ⟨⟨hpΔ, hpp⟩, ?_, ?_⟩
      · by_contra hlt
        exact hnot ⟨by exact_mod_cast (not_le.mp hlt), hpp⟩
      · exact_mod_cast hpΔ
  -- second Mertens over the window
  have hSsum : (∑ p ∈ S, Submission.ASP.FIgtil p) ≤ Real.log 19 + C := by
    by_cases hNlt : N < Δ
    · have hw : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
      have hwz : (N:ℝ) < (Δ:ℝ) := by exact_mod_cast hNlt
      have hwin := hCwin Δ (N:ℝ) (Δ:ℝ) hw hwz le_rfl
      rw [← hSdef] at hwin
      linarith [hwin, hll]
    · -- `N ≥ Δ`: the window is empty
      have hSempty : S = ∅ := by
        rw [hSdef]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
        obtain ⟨⟨hpΔ, -⟩, hNp, -⟩ := hp
        have hNp' : N ≤ p := by exact_mod_cast hNp
        omega
      rw [hSempty, Finset.sum_empty]
      have h19 : 0 < Real.log 19 := Real.log_pos (by norm_num)
      linarith
  -- the exponent is bounded by `4 (log 19 + C)`
  have hsum : (∑ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p + Submission.ASP.FIgtil p
        + 3 * Submission.ASP.FIgtil p^2)) ≤ 4 * (Real.log 19 + C) := by
    have hpoint : ∀ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p + Submission.ASP.FIgtil p
          + 3 * Submission.ASP.FIgtil p^2) ≤ 4 * Submission.ASP.FIgtil p := by
      intro p hp
      rw [hSdef] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
      have hx0 : 0 ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
      have hx23 : Submission.ASP.FIgtil p ≤ 2/3 :=
        Work.FIChain.sieveDens_FIgtil_prime_le_two_thirds hpp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.one_le
      have ht : (p:ℝ)^(-ε) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -ε ≤ 0 by linarith)
        rwa [Real.rpow_zero] at h
      have h1 : (p:ℝ)^(-ε) * Submission.ASP.FIgtil p ≤ Submission.ASP.FIgtil p := by
        calc (p:ℝ)^(-ε) * Submission.ASP.FIgtil p ≤ 1 * Submission.ASP.FIgtil p :=
              mul_le_mul_of_nonneg_right ht hx0
          _ = Submission.ASP.FIgtil p := one_mul _
      have h2 : 3 * Submission.ASP.FIgtil p ^ 2 ≤ 2 * Submission.ASP.FIgtil p := by
        nlinarith [hx0, hx23]
      linarith
    calc (∑ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p + Submission.ASP.FIgtil p
            + 3 * Submission.ASP.FIgtil p^2))
        ≤ ∑ p ∈ S, 4 * Submission.ASP.FIgtil p := Finset.sum_le_sum hpoint
      _ = 4 * ∑ p ∈ S, Submission.ASP.FIgtil p := by rw [Finset.mul_sum]
      _ ≤ 4 * (Real.log 19 + C) := mul_le_mul_of_nonneg_left hSsum (by norm_num)
  -- the window product of inverses is bounded
  have hWinv : (∏ p ∈ S, f p)⁻¹ ≤ Real.exp (4 * (Real.log 19 + C)) := by
    rw [← Finset.prod_inv_distrib f]
    have hpoint : ∀ p ∈ S, (f p)⁻¹ ≤ Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
          + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) := by
      intro p hp
      rw [hSdef] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
      rw [hfdef]
      exact Work.FIChain.factor_inv_le_exp hpp ε
    have hnn : ∀ p ∈ S, 0 ≤ (f p)⁻¹ := by
      intro p hp
      rw [hSdef] at hp
      exact le_of_lt (inv_pos.mpr (hfpos p (Finset.mem_filter.mp hp).1))
    calc (∏ p ∈ S, (f p)⁻¹)
        ≤ ∏ p ∈ S, Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
            + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) :=
          Finset.prod_le_prod₀ hnn hpoint
      _ = Real.exp (∑ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p + Submission.ASP.FIgtil p
            + 3 * Submission.ASP.FIgtil p^2)) := (Real.exp_sum S _).symm
      _ ≤ Real.exp (4 * (Real.log 19 + C)) := Real.exp_le_exp.mpr hsum
  -- splitting the full product
  have hdecomp : (∏ p ∈ Nat.primesBelow Δ, f p) =
      (∏ p ∈ S, f p) * (∏ p ∈ Nat.primesBelow N, f p) := by
    rw [hS_eq]
    exact (Finset.prod_sdiff (f := f) (Nat.primesBelow_mono hNΔ)).symm
  have hPbig_nn : 0 ≤ ∏ p ∈ Nat.primesBelow Δ, f p :=
    Finset.prod_nonneg (fun p hp => le_of_lt (hfpos p hp))
  have hWpos : 0 < ∏ p ∈ S, f p := by
    apply Finset.prod_pos
    intro p hp
    rw [hSdef] at hp
    exact hfpos p (Finset.mem_filter.mp hp).1
  have hWne : (∏ p ∈ S, f p) ≠ 0 := ne_of_gt hWpos
  calc (∏ p ∈ Nat.primesBelow N, f p)
      = (∏ p ∈ Nat.primesBelow Δ, f p) * (∏ p ∈ S, f p)⁻¹ := by
        rw [hdecomp, mul_assoc,
          mul_comm (∏ p ∈ Nat.primesBelow N, f p) (∏ p ∈ S, f p)⁻¹,
          ← mul_assoc, mul_inv_cancel₀ hWne, one_mul]
      _ ≤ (∏ p ∈ Nat.primesBelow Δ, f p) * Real.exp (4 * (Real.log 19 + C)) :=
        mul_le_mul_of_nonneg_left hWinv hPbig_nn
      _ = Real.exp (4 * (Real.log 19 + C)) * ∏ p ∈ Nat.primesBelow Δ, f p := by ring

end Work.FIChain
