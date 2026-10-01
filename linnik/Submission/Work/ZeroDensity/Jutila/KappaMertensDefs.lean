/-
# Definitions for the Mertens-type inputs `KappaMertens`

The object of study is

 `Ssum x t = Σ_{r ≤ x, (r,t)=1} μ(r)/κ(r)`  and  `Tsum x t = Σ_{r ≤ x, (r,t)=1} (μ(r)/κ(r))·log(x/r)`

with `κ(n) = n·∏_{p|n}(1+1/p)` (`Work.ZeroDensity.Jutila.kappa`, Graham's `κ`) and the target's
weight `kap c = ∏_{p|c}(p+1)` (`Work.ZeroDensity.Jutila.kap`); the two agree on squarefree `r`
and the summands `μ(r)/κ(r)`, `μ(r)/kap(r)` agree for *every* `r` (both vanish when `μ r = 0`).

The errors are measured by the exponentially decaying envelope `Dc c x = exp(-(c·√(log x)))`;
this is the envelope produced by `Commons.NumberTheory.Moebius.muRecipSum_decay`
(`|Σ_{n ≤ x} μ(n)/n| ≤ C·Dc c x`), which is the analytic input of the whole development.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaAux

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- The exponentially decaying envelope `Dc c x = exp(-(c·√(log x)))` (`= 1` for `x ≤ 1`). -/
def Dc (c : ℝ) (x : ℕ) : ℝ := Real.exp (-(c * Real.sqrt (Real.log (x : ℝ))))

lemma Dc_pos (c : ℝ) (x : ℕ) : 0 < Dc c x := Real.exp_pos _

lemma Dc_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℕ) : Dc c x ≤ 1 := by
  rw [Dc, Real.exp_le_one_iff]
  have := Real.sqrt_nonneg (Real.log (x : ℝ))
  nlinarith

lemma Dc_antitone {c : ℝ} (hc : 0 ≤ c) {x y : ℕ} (h : x ≤ y) : Dc c y ≤ Dc c x := by
  rw [Dc, Dc, Real.exp_le_exp]
  have hx : Real.log (x : ℝ) ≤ Real.log (y : ℝ) := by
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · subst hx0
      rw [Nat.cast_zero, Real.log_zero]
      rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · subst hy0; rw [Nat.cast_zero, Real.log_zero]
      · exact Real.log_nonneg (by exact_mod_cast hy0)
    · exact Real.log_le_log (by positivity) (by exact_mod_cast h)
  have := Real.sqrt_le_sqrt hx
  nlinarith

lemma Dc_le_of_le_rate {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (x : ℕ) : Dc c₂ x ≤ Dc c₁ x := by
  rw [Dc, Dc, Real.exp_le_exp]
  have := Real.sqrt_nonneg (Real.log (x : ℝ))
  nlinarith

/-- `Ssum x t = Σ_{r ≤ x, (r,t)=1} μ(r)/κ(r)`. -/
def Ssum (x t : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 x).filter (fun r => Nat.Coprime r t),
    (ArithmeticFunction.moebius r : ℝ) / kappa r

/-- `Tsum x t = Σ_{r ≤ x, (r,t)=1} (μ(r)/κ(r))·log(x/r)`. -/
def Tsum (x t : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 x).filter (fun r => Nat.Coprime r t),
    (ArithmeticFunction.moebius r : ℝ) / kappa r * Real.log ((x : ℝ) / (r : ℝ))

lemma Ssum_eq_sum_if (x t : ℕ) :
    Ssum x t = ∑ r ∈ Finset.Icc 1 x,
      (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kappa r else 0) := by
  rw [Ssum, Finset.sum_filter]

lemma Tsum_eq_sum_if (x t : ℕ) :
    Tsum x t = ∑ r ∈ Finset.Icc 1 x,
      (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kappa r else 0)
        * Real.log ((x : ℝ) / (r : ℝ)) := by
  rw [Tsum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : Nat.Coprime r t <;> simp [h]

/-- `κ(n) = n·∏_{p|n}(1+1/p)`. -/
lemma kappa_def (n : ℕ) :
    kappa n = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := rfl

/-- `κ` is (coprime-)multiplicative. -/
lemma kappa_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    kappa (a * b) = kappa a * kappa b := by
  unfold kappa
  rw [Nat.cast_mul, h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  ring

/-- For squarefree `n`, `κ(n) = ∏_{p|n}(p+1) = kap n`. -/
lemma kappa_eq_kap_of_squarefree {n : ℕ} (hn : Squarefree n) : kappa n = kap n := by
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  unfold kappa kap
  rw [← hprod]
  have hmul : (∏ p ∈ n.primeFactors, (p : ℝ) * (1 + 1 / (p : ℝ)))
      = (∏ p ∈ n.primeFactors, (p : ℝ)) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_mul_distrib
  rw [← hmul]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact_mod_cast this
  field_simp

/-- The summands of the two normalisations agree for every `n` (both are `0` unless `n` is
squarefree, and on squarefree `n` the weights `κ`, `kap` coincide). -/
lemma mu_div_kappa_eq_mu_div_kap (n : ℕ) :
    (ArithmeticFunction.moebius n : ℝ) / kappa n
      = (ArithmeticFunction.moebius n : ℝ) / kap n := by
  by_cases h : Squarefree n
  · rw [kappa_eq_kap_of_squarefree h]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

end

end Work.ZeroDensity.Jutila
