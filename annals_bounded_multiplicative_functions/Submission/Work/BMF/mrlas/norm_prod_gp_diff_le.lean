import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.sum_le_tsum_tail
import Submission.Work.BMF.mrlas.norm_prod_one_add_le_exp
import Submission.Work.BMF.mrlas.sum_primesBelow_rpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Euler-product tail bound

For a `1`-bounded multiplicative-type function `f : ℕ → ℂ` with `f 1 = 1` and `σ > 1`, the
difference of the truncated Euler products
`∏_{p < N'} g_p(z) - ∏_{p < N} g_p(z)` (with `g_p` the local factor `gp f p`) is bounded, uniformly
for `N ≤ N'` and `Re z > σ`, by a constant times `exp (2 ∑_{k} (N + k)^{-σ}) - 1`.

The proof factors out the product over the primes below `N` (whose norm is bounded by
`exp (2 ζ(σ))`), and bounds the remaining tail product by `exp (2 ∑_{k} (N+k)^{-σ}) - 1` using
`‖g_p - 1‖ ≤ 2 p^{-σ}` (from `Work.BMF.norm_gp_sub_one_le`) and the fact that the primes in the
tail dominate the tail of the `p`-series (`Work.BMF.mrlas.sum_le_tsum_tail`).
-/

namespace Work.BMF.mrlas

open Finset Real Complex

/-- For a finite product of factors `1 + h n` with `h : ι → ℂ`, the distance of the product
from `1` is bounded by the corresponding expression for the norms, `∏ (1 + ‖h n‖) - 1`.
This is the crude multiplicative triangle inequality, proved by induction:
`(1 + h a) Φ - 1 = h a + (1 + h a) (Φ - 1)`. -/
theorem norm_prod_one_add_sub_one_le {ι : Type*} (S : Finset ι) (h : ι → ℂ) :
    ‖(∏ n ∈ S, (1 + h n)) - 1‖ ≤ (∏ n ∈ S, (1 + ‖h n‖)) - 1 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a S ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hkey : (1 + h a) * ∏ n ∈ S, (1 + h n) - 1
        = h a + (1 + h a) * (∏ n ∈ S, (1 + h n) - 1) := by ring
    rw [hkey]
    calc ‖h a + (1 + h a) * (∏ n ∈ S, (1 + h n) - 1)‖
        ≤ ‖h a‖ + ‖(1 + h a) * (∏ n ∈ S, (1 + h n) - 1)‖ := norm_add_le _ _
      _ = ‖h a‖ + ‖1 + h a‖ * ‖(∏ n ∈ S, (1 + h n)) - 1‖ := by rw [norm_mul]
      _ ≤ ‖h a‖ + (1 + ‖h a‖) * (∏ n ∈ S, (1 + ‖h n‖) - 1) := by
          have hna : ‖1 + h a‖ ≤ 1 + ‖h a‖ := by simpa using norm_add_le (1 : ℂ) (h a)
          have := mul_le_mul hna ih (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1 + ‖h a‖)
          linarith
      _ = (1 + ‖h a‖) * ∏ n ∈ S, (1 + ‖h n‖) - 1 := by ring

/-- Uniform bound on the partial Euler products: for `Re z > σ` and every `N`,
`‖∏_{p < N} g_p(z)‖ ≤ exp (2 ∑_n n^{-σ})`. -/
theorem norm_prod_gp_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (N : ℕ) {z : ℂ} (hz : σ < z.re) :
    ‖∏ p ∈ N.primesBelow, Work.BMF.gp f p z‖
      ≤ Real.exp (2 * ∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
  have hEq : ∏ p ∈ N.primesBelow, Work.BMF.gp f p z
      = ∏ p ∈ N.primesBelow, (1 + (Work.BMF.gp f p z - 1)) :=
    Finset.prod_congr rfl (fun p _ => by ring)
  rw [hEq]
  calc ‖∏ p ∈ N.primesBelow, (1 + (Work.BMF.gp f p z - 1))‖
      ≤ Real.exp (∑ p ∈ N.primesBelow, ‖Work.BMF.gp f p z - 1‖) :=
        Work.BMF.mrlas.norm_prod_one_add_le_exp _ _
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, 2 * (p : ℝ) ^ (-σ)) := by
        apply Real.exp_le_exp.mpr
        apply Finset.sum_le_sum
        intro p hp
        exact Work.BMF.norm_gp_sub_one_le f hf1 hb hσ p (Nat.prime_of_mem_primesBelow hp) hz
    _ ≤ Real.exp (2 * ∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (Work.BMF.mrlas.sum_primesBelow_rpow_le σ hσ N) (by norm_num)

theorem norm_prod_gp_diff_le (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N N' : ℕ), N ≤ N' → ∀ z : ℂ, σ < z.re →
      ‖(∏ p ∈ N'.primesBelow, Work.BMF.gp f p z) - (∏ p ∈ N.primesBelow, Work.BMF.gp f p z)‖
        ≤ B * (Real.exp (2 * (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ))) - 1) := by
  classical
  refine ⟨Real.exp (2 * ∑' n : ℕ, (n : ℝ) ^ (-σ)), Real.exp_pos _, ?_⟩
  intro N N' hNN' z hz
  set T : Finset ℕ := N'.primesBelow \ N.primesBelow with hTdef
  have hsub : N.primesBelow ⊆ N'.primesBelow := Nat.primesBelow_mono hNN'
  have hTmem : ∀ n ∈ T, N ≤ n := by
    intro n hn
    have hn' : n ∈ N'.primesBelow \ N.primesBelow := by rw [hTdef] at hn; exact hn
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hn'
    by_contra hcon
    exact h2 (Nat.mem_primesBelow.mpr ⟨not_le.mp hcon, Nat.prime_of_mem_primesBelow h1⟩)
  have hTprime : ∀ n ∈ T, n.Prime := by
    intro n hn
    have hn' : n ∈ N'.primesBelow \ N.primesBelow := by rw [hTdef] at hn; exact hn
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hn').1
  have hfac : (∏ p ∈ N'.primesBelow, Work.BMF.gp f p z)
      = (∏ p ∈ T, Work.BMF.gp f p z) * ∏ p ∈ N.primesBelow, Work.BMF.gp f p z := by
    have h := Finset.prod_sdiff (f := fun p => Work.BMF.gp f p z) hsub
    rw [← hTdef] at h
    exact h.symm
  have hdiff : (∏ p ∈ N'.primesBelow, Work.BMF.gp f p z)
        - (∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      = (∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
        * ((∏ p ∈ T, Work.BMF.gp f p z) - 1) := by
    rw [hfac]; ring
  have hTnorm : ‖(∏ p ∈ T, Work.BMF.gp f p z) - 1‖
      ≤ Real.exp (2 * (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ))) - 1 := by
    have hEq : ∏ p ∈ T, Work.BMF.gp f p z
        = ∏ p ∈ T, (1 + (Work.BMF.gp f p z - 1)) :=
      Finset.prod_congr rfl (fun p _ => by ring)
    rw [hEq]
    have h1 : ‖(∏ p ∈ T, (1 + (Work.BMF.gp f p z - 1))) - 1‖
        ≤ (∏ p ∈ T, (1 + ‖Work.BMF.gp f p z - 1‖)) - 1 :=
      norm_prod_one_add_sub_one_le T _
    have h2 : (∏ p ∈ T, (1 + ‖Work.BMF.gp f p z - 1‖))
        ≤ ∏ p ∈ T, (1 + 2 * (p : ℝ) ^ (-σ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp; positivity
      · intro p hp
        have hp' := hTprime p hp
        have := Work.BMF.norm_gp_sub_one_le f hf1 hb hσ p hp' hz
        linarith
    have h3 : (∏ p ∈ T, (1 + 2 * (p : ℝ) ^ (-σ)))
        ≤ Real.exp (2 * (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ))) := by
      calc (∏ p ∈ T, (1 + 2 * (p : ℝ) ^ (-σ)))
          ≤ Real.exp (∑ p ∈ T, 2 * (p : ℝ) ^ (-σ)) :=
            Real.prod_one_add_le_exp_sum T
              (fun p => mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
        _ ≤ Real.exp (2 * (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ))) := by
            apply Real.exp_le_exp.mpr
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left
              (Work.BMF.mrlas.sum_le_tsum_tail σ hσ T N hTmem) (by norm_num)
    linarith
  calc ‖(∏ p ∈ N'.primesBelow, Work.BMF.gp f p z)
          - (∏ p ∈ N.primesBelow, Work.BMF.gp f p z)‖
      = ‖∏ p ∈ N.primesBelow, Work.BMF.gp f p z‖
        * ‖(∏ p ∈ T, Work.BMF.gp f p z) - 1‖ := by rw [hdiff, norm_mul]
    _ ≤ Real.exp (2 * ∑' n : ℕ, (n : ℝ) ^ (-σ))
        * (Real.exp (2 * (∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ))) - 1) :=
        mul_le_mul (norm_prod_gp_le f hf1 hb hσ N hz) hTnorm (norm_nonneg _)
          (le_of_lt (Real.exp_pos _))

end Work.BMF.mrlas
