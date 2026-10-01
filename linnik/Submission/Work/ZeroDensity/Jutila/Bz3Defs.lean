/-
# Definitions and elementary algebra for the `S₃` main-term computation (`Bz3MainTerm`)

This file fixes the vocabulary shared by the pieces of `Work.ZeroDensity.Jutila.Bz3MainTerm`.

* `kap c = ∏_{p | c}(p+1)` (An's `κ`, arXiv:2206.10104, in the rational case `k = ℚ`);
* `s3exact z N` is *verbatim* the triple sum of `Bz3MainTerm` (`⌊N/(q r t)⌋` inside);
* `s3cont z N` is the "continuous model" of the same sum, in which the floor `⌊N/(q r t)⌋` is
  replaced by the real value `N/(q r t)` (in the linear factor and in both logarithms);
* `KappaMertensInput` is the package of Mertens-type inputs (the rational-case forms of Graham's
  (11) and (12), used by An as Lemmas 11ing/12ing) that the analytic pieces consume.

The algebraic content is that for squarefree coprime `r`, `t`
`s3c (r*t) = ζ(2)⁻¹·(r/κ(r))·(t/κ(t))`, so that the summand of `s3exact` becomes
`ζ(2)⁻¹·μ(r)μ(t)·(r/κ(r))(t/κ(t))·⌊N/(qrt)⌋·(…)`.  With `⌊N/(qrt)⌋ ≈ N/(qrt)` this gives the
"good" weight `μ(r)/κ(r)` (the one with a Riesz-mean constant), which is exactly why the paper's
two-stage Abel summation works.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- `kap c = ∏_{p | c} (p + 1)`: An's `κ`, in the rational case. -/
def kap (c : ℕ) : ℝ := ∏ p ∈ c.primeFactors, ((p : ℝ) + 1)

lemma kap_pos (c : ℕ) : 0 < kap c := by
  unfold kap
  exact Finset.prod_pos fun p _ => by positivity

lemma kap_ne_zero (c : ℕ) : kap c ≠ 0 := (kap_pos c).ne'

lemma kap_mul_of_coprime {r t : ℕ} (h : Nat.Coprime r t) :
    kap (r * t) = kap r * kap t := by
  unfold kap
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

/-- For squarefree `c`, `s3c c = ζ(2)⁻¹ · c / κ(c)` (since `∏_{p|c} p = c`). -/
lemma s3c_eq_of_squarefree (c : ℕ) (hc : Squarefree c) :
    LinnikAreas.Density4.BzS3.s3c c = (Real.pi ^ 2 / 6)⁻¹ * (c : ℝ) / kap c := by
  have hdiv : (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
      = (∏ p ∈ c.primeFactors, (p : ℝ)) / kap c := by
    rw [Finset.prod_div_distrib]
    rfl
  have hprod : (∏ p ∈ c.primeFactors, (p : ℝ)) = (c : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hc]
  unfold LinnikAreas.Density4.BzS3.s3c
  rw [hdiv, hprod]
  ring

/-- For squarefree coprime `r, t`: `s3c (r*t) = ζ(2)⁻¹·(r/κ(r))·(t/κ(t))`. -/
lemma s3c_mul_eq_of_coprime {r t : ℕ} (hr : Squarefree r) (ht : Squarefree t)
    (h : Nat.Coprime r t) :
    LinnikAreas.Density4.BzS3.s3c (r * t)
      = (Real.pi ^ 2 / 6)⁻¹ * ((r : ℝ) / kap r) * ((t : ℝ) / kap t) := by
  rw [s3c_eq_of_squarefree (r * t) ((Nat.squarefree_mul h).mpr ⟨hr, ht⟩), kap_mul_of_coprime h]
  push_cast
  have hr0 : kap r ≠ 0 := kap_ne_zero r
  have ht0 : kap t ≠ 0 := kap_ne_zero t
  field_simp

/-- **The exact triple sum of `Bz3MainTerm`** (with the floor `⌊N/(q r t)⌋`). -/
def s3exact (z N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
    ∑ t ∈ Finset.Icc 1 (N / (q * z)),
      (if Nat.Coprime r t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
        (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N / (q * r * t) : ℕ) : ℝ) *
          ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
              (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))

/-- **The continuous model of the same sum**: `⌊N/(q r t)⌋` is replaced by the real value
`N/(q r t)` in the linear factor and in both logarithms. -/
def s3cont (z N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
    ∑ t ∈ Finset.Icc 1 (N / (q * z)),
      (if Nat.Coprime r t then
          (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
        (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
          ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
              (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1))

/-- **The Mertens-type inputs for the `S₃` main term** (rational case, no Siegel zero).

These are Graham's estimates (11) and (12) as stated for `k = ℚ` by An (Lemmas 11ing/12ing):
for squarefree `t`, `2 ≤ R ≤ Y`,

* `Σ_{r ≤ R, (r,t)=1} (μ(r)/κ(r))·(log(Y/r) − 1)`
  `= ζ(2)·κ(t)/t + log(Y/R)·Σ_{r ≤ R,(r,t)=1} μ(r)/κ(r) + O((Σ_{d|t} 1/√d)·e^{−c√log R})`
  (the middle term is the exact effect of replacing the truncation limit `R` by the real
  parameter `Y ≥ R` in the logarithm);
* `Σ_{r ≤ R, (r,t)=1} μ(r)/κ(r) = O((Σ_{d|t} 1/√d)·e^{−c√log R})`,

with absolute `C, c > 0`.  The constant `ζ(2)·κ(t)/t = ζ(2)∏_{p|t}(1+1/p)` is the density factor
of the coprime class; in the applications `t` is always squarefree (it carries a factor `μ(t)`).
The decay in `√log` is what the workspace already has for `Σ μ(n)/n`
(`Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`). -/
abbrev KappaMertensInput : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ (t R : ℕ) (Y : ℝ), Squarefree t → 2 ≤ R → (R : ℝ) ≤ Y →
        |(∑ r ∈ Finset.Icc 1 R,
            (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0) *
              (Real.log (Y / (r : ℝ)) - 1))
          - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
          - Real.log (Y / (R : ℝ)) *
              (∑ r ∈ Finset.Icc 1 R,
                if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (R : ℝ)))))
    ∧ (∀ (t R : ℕ), Squarefree t → 2 ≤ R →
        |(∑ r ∈ Finset.Icc 1 R,
            if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (R : ℝ)))))

end

end Work.ZeroDensity.Jutila
