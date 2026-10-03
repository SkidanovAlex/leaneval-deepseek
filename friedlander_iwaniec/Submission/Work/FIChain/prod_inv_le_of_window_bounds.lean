import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.sieveDens_le_one_sub

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary estimates

The proof of the main theorem reduces, prime by prime, to two elementary estimates:

* the Euler factor `(1 − g̃(p)·hSieveC g̃ ε p)⁻¹` equals `(1 + p^{-ε} g̃(p))/(1 − g̃(p))`,
* and `(1 + a)/(1 − b) ≤ exp(a + b + 3 b²)` for `a ≥ 0` and `0 ≤ b ≤ 2/3`. -/

/-- At a prime the inverse sieve factor collapses to a single Euler factor:
`(1 − g̃(p)·hSieveC g̃ ε p)⁻¹ = (1 + p^{-ε} g̃(p))/(1 − g̃(p))`. -/
lemma hSieveC_inv_factor {p : ℕ} (hp : p.Prime) (ε : ℝ) :
    (1 - Submission.ASP.FIgtil p * hSieveC Submission.ASP.FIgtil ε p)⁻¹
      = (1 + (p : ℝ) ^ (-ε) * Submission.ASP.FIgtil p) / (1 - Submission.ASP.FIgtil p) := by
  have hp' : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have ht : 0 < (p:ℝ) ^ (-ε) := Real.rpow_pos_of_pos hp' _
  have hg : 0 ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
  have hden : 1 + (p:ℝ)^(-ε) * Submission.ASP.FIgtil p ≠ 0 := by
    have h : (0:ℝ) < 1 + (p:ℝ)^(-ε) * Submission.ASP.FIgtil p := by
      have := mul_nonneg (le_of_lt ht) hg; linarith
    exact ne_of_gt h
  have hlt : Submission.ASP.FIgtil p ≤ 2/3 := sieveDens_FIgtil_prime_le_two_thirds hp
  have hden2 : 1 - Submission.ASP.FIgtil p ≠ 0 := by
    have h : (0:ℝ) < 1 - Submission.ASP.FIgtil p := by linarith
    exact ne_of_gt h
  rw [hSieveC_prime Submission.ASP.FIgtil ε hp]
  have hmain : 1 - Submission.ASP.FIgtil p * ((1 + (p:ℝ)^(-ε)) / (1 + (p:ℝ)^(-ε) * Submission.ASP.FIgtil p))
      = (1 - Submission.ASP.FIgtil p) / (1 + (p:ℝ)^(-ε) * Submission.ASP.FIgtil p) := by
    field_simp
    ring
  rw [hmain, inv_div]

/-- For `0 ≤ b ≤ 2/3` one has `1/(1 − b) ≤ exp(b + 3 b²)`.  Indeed `log(1/(1−b)) = log(1 + b/(1−b))`
and `log(1+x) ≤ x` gives `log(1/(1−b)) ≤ b/(1−b) ≤ b + 3 b²`, the last since `b ≤ 2/3` makes
`2 − 3b ≥ 0`. -/
lemma one_div_one_sub_le_exp {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 2/3) :
    1 / (1 - b) ≤ Real.exp (b + 3 * b^2) := by
  have h1 : 0 < 1 - b := by linarith
  have hpos : 0 < 1 / (1 - b) := by positivity
  have hb2 : 0 ≤ 2 - 3*b := by linarith
  have hbd : b / (1 - b) ≤ b + 3 * b^2 := by
    rw [div_le_iff₀ h1]
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) hb2]
  have h_eq : 1 / (1 - b) = 1 + b / (1 - b) := by
    field_simp
    ring
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + b/(1-b) by positivity)
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  calc Real.log (1 / (1 - b)) = Real.log (1 + b/(1-b)) := by rw [h_eq]
    _ ≤ 1 + b/(1-b) - 1 := hlog
    _ = b/(1-b) := by ring
    _ ≤ b + 3*b^2 := hbd

/-- The pointwise sieve-factor bound at a prime:
`(1 − g̃(p)·hSieveC g̃ ε p)⁻¹ ≤ exp(p^{-ε} g̃(p) + g̃(p) + 3 g̃(p)²)`. -/
lemma factor_inv_le_exp {p : ℕ} (hp : p.Prime) (ε : ℝ) :
    (1 - Submission.ASP.FIgtil p * hSieveC Submission.ASP.FIgtil ε p)⁻¹
      ≤ Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
          + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) := by
  rw [hSieveC_inv_factor hp ε]
  set t := (p:ℝ)^(-ε) with ht_def
  set b := Submission.ASP.FIgtil p with hb_def
  have hb0 : 0 ≤ b := Submission.ASP.FIgtil_nonneg p
  have hb : b ≤ 2/3 := sieveDens_FIgtil_prime_le_two_thirds hp
  have h1b : 0 < 1 - b := by linarith
  calc (1 + t*b)/(1-b)
      = (1 + t*b) * (1/(1-b)) := by rw [mul_one_div]
    _ ≤ Real.exp (t*b) * Real.exp (b + 3*b^2) := by
        apply mul_le_mul
        · linarith [Real.add_one_le_exp (t*b)]
        · exact one_div_one_sub_le_exp hb0 hb
        · positivity
        · positivity
    _ = Real.exp (t*b + (b + 3*b^2)) := (Real.exp_add (t*b) (b + 3*b^2)).symm
    _ = Real.exp (t*b + b + 3*b^2) := by
        rw [show t*b + (b + 3*b^2) = t*b + b + 3*b^2 by ring]

/-- **The §6 Euler product over a window, from the two window estimates.**  Given

* `hwin : ∑_{p < Δ prime, w ≤ p < z'} g̃ p ≤ log log z' − log log w + Cw`,
* `hsq  : ∑_{p < Δ} g̃ p² ≤ Cs`,

and `3 ≤ Δ`, `2 ≤ w`, `w < z'`, `z' ≤ Δ`, one has

    ∏_{w ≤ p < z'} (1 − g̃(p)·hSieveC g̃ (1/log Δ) p)⁻¹
        ≤ exp(2·Cw + 3·Cs) · (log z' / log w)².

Proof route (self-contained; does NOT import `FIChain.sieveFactor_inv_le_exp`): for a prime `p`,
`hSieveC g̃ ε p = (1 + p^{-ε})/(1 + p^{-ε}·g̃ p)` (the product over `p.primeFactors` collapses), so
`1 − g̃ p · hSieveC g̃ ε p = (1 − g̃ p)/(1 + p^{-ε} g̃ p)` and the factor equals
`(1 + p^{-ε} g̃ p)/(1 − g̃ p)`.  For `ε = 1/log Δ ≥ 0` (as `Δ ≥ 3`) and `p ≥ 2` one has
`p^{-ε} ∈ (0,1]`, and `g̃ p ∈ [0, 2/3]` (`Submission.ASP.FIgtil_nonneg`, and
`Work.FIChain.sieveDens_FIgtil_prime_le_two_thirds` from `FIChain.sieveDens_le_one_sub`), so
`(1 + p^{-ε} g̃ p)/(1 − g̃ p) ≤ Real.exp(p^{-ε} g̃ p + g̃ p + 3 g̃ p²)`; multiply over the window
(`Finset.prod_le_prod₀`, `Real.exp_sum`), bound the exponent by `∑ p^{-ε} g̃ p ≤ ∑ g̃ p`, plus
`hwin`, plus `∑_{window} 3 g̃ p² ≤ 3 ∑_{p<Δ} g̃ p² ≤ 3 Cs`, and finish with
`log log z' − log log w = log (log z' / log w)` (both logs positive since `w ≥ 2`) and
`Real.exp_nat_mul`, `Real.exp_log`, `Real.rpow_natCast`. -/
theorem prod_inv_le_of_window_bounds
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (w z' : ℝ) (hw : 2 ≤ w) (hwz : w < z') (hzΔ : z' ≤ (Δ : ℝ))
    {Cw Cs : ℝ}
    (hwin : (∑ p ∈ (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
        Submission.ASP.FIgtil p) ≤ Real.log (Real.log z') - Real.log (Real.log w) + Cw)
    (hsq : (∑ p ∈ Nat.primesBelow Δ, (Submission.ASP.FIgtil p) ^ 2) ≤ Cs) :
    (∏ p ∈ (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'),
        (1 - Submission.ASP.FIgtil p
          * Work.FIChain.hSieveC Submission.ASP.FIgtil (1 / Real.log (Δ : ℝ)) p)⁻¹)
      ≤ Real.exp (2 * Cw + 3 * Cs) * (Real.log z' / Real.log w) ^ (2 : ℝ) := by
  set S : Finset ℕ :=
    (Nat.primesBelow Δ).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z') with hS
  set ε : ℝ := 1 / Real.log (Δ : ℝ) with hεdef
  have hε : 0 ≤ ε := by
    rw [hεdef]
    exact div_nonneg (by norm_num)
      (le_of_lt (Real.log_pos (by exact_mod_cast (show 1 < Δ by omega))))
  have hprime : ∀ p ∈ S, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  -- pointwise bound
  have hpoint : ∀ p ∈ S,
      (1 - Submission.ASP.FIgtil p * hSieveC Submission.ASP.FIgtil ε p)⁻¹
        ≤ Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
            + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) :=
    fun p hp => factor_inv_le_exp (hprime p hp) ε
  -- multiply
  have hprod : (∏ p ∈ S,
        (1 - Submission.ASP.FIgtil p * hSieveC Submission.ASP.FIgtil ε p)⁻¹)
      ≤ ∏ p ∈ S, Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
            + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      rw [hSieveC_inv_factor (hprime p hp) ε]
      apply le_of_lt
      apply div_pos
      · have hp' : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hprime p hp).pos
        have ht' : 0 < (p:ℝ)^(-ε) := Real.rpow_pos_of_pos hp' _
        have := mul_nonneg (le_of_lt ht') (Submission.ASP.FIgtil_nonneg p)
        linarith
      · have := sieveDens_FIgtil_prime_le_two_thirds (hprime p hp)
        linarith
    · intro p hp
      exact hpoint p hp
  -- the exponent sum
  have hsum : (∑ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
        + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2))
      ≤ (Real.log (Real.log z') - Real.log (Real.log w) + Cw)
        + (Real.log (Real.log z') - Real.log (Real.log w) + Cw) + 3 * Cs := by
    have ht_le : ∀ p ∈ S, (p:ℝ)^(-ε) ≤ 1 := by
      intro p hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hprime p hp).one_le
      have := Real.rpow_le_rpow_of_exponent_le hp1 (show -ε ≤ 0 by linarith)
      rwa [Real.rpow_zero] at this
    have hS1 : (∑ p ∈ S, (p:ℝ)^(-ε) * Submission.ASP.FIgtil p)
        ≤ Real.log (Real.log z') - Real.log (Real.log w) + Cw := by
      apply le_trans _ hwin
      apply Finset.sum_le_sum
      intro p hp
      simpa using mul_le_mul_of_nonneg_right (ht_le p hp) (Submission.ASP.FIgtil_nonneg p)
    have hS3 : (∑ p ∈ S, 3 * Submission.ASP.FIgtil p ^ 2) ≤ 3 * Cs := by
      have hsub : S ⊆ Nat.primesBelow Δ := fun p hp => (Finset.mem_filter.mp hp).1
      have hsq2 : (∑ p ∈ S, Submission.ASP.FIgtil p ^ 2)
          ≤ ∑ p ∈ Nat.primesBelow Δ, Submission.ASP.FIgtil p ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (le_trans hsq2 hsq) (by norm_num)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith [hS1, hwin, hS3]
  -- the exponential assembly
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z' := Real.log_pos (by linarith)
  have hLpos : 0 < Real.log z' / Real.log w := div_pos hlogz hlogw
  have hlogL : Real.log (Real.log z' / Real.log w)
      = Real.log (Real.log z') - Real.log (Real.log w) :=
    Real.log_div (ne_of_gt hlogz) (ne_of_gt hlogw)
  have hAexp : Real.exp ((Real.log (Real.log z') - Real.log (Real.log w) + Cw)
        + (Real.log (Real.log z') - Real.log (Real.log w) + Cw) + 3 * Cs)
      = Real.exp (2 * Cw + 3 * Cs) * (Real.log z' / Real.log w) ^ (2 : ℝ) := by
    have hAeq : (Real.log (Real.log z') - Real.log (Real.log w) + Cw)
          + (Real.log (Real.log z') - Real.log (Real.log w) + Cw) + 3 * Cs
        = (2 * Cw + 3 * Cs) + 2 * Real.log (Real.log z' / Real.log w) := by
      rw [hlogL]; ring
    have hpow : (Real.log z' / Real.log w) ^ (2:ℝ)
        = Real.exp (2 * Real.log (Real.log z' / Real.log w)) := by
      rw [Real.rpow_def_of_pos hLpos]
      congr 1
      ring
    rw [hAeq, Real.exp_add, hpow]
  calc (∏ p ∈ S, (1 - Submission.ASP.FIgtil p * hSieveC Submission.ASP.FIgtil ε p)⁻¹)
      ≤ ∏ p ∈ S, Real.exp ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
            + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2) := hprod
    _ = Real.exp (∑ p ∈ S, ((p:ℝ)^(-ε) * Submission.ASP.FIgtil p
            + Submission.ASP.FIgtil p + 3 * Submission.ASP.FIgtil p^2)) :=
        (Real.exp_sum S _).symm
    _ ≤ Real.exp ((Real.log (Real.log z') - Real.log (Real.log w) + Cw)
        + (Real.log (Real.log z') - Real.log (Real.log w) + Cw) + 3 * Cs) :=
        Real.exp_le_exp.mpr hsum
    _ = Real.exp (2 * Cw + 3 * Cs) * (Real.log z' / Real.log w) ^ (2 : ℝ) := hAexp

end

end Work.FIChain
