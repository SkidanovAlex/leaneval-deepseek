/-
# Definitions for the `Σ_B + Σ_C` boundary term of the `S₃` computation

Namespace `Work.LinnikAreas2`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.mu_kappa_log_sum
import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay

namespace Work.LinnikAreas2

open Finset

noncomputable section

/-- `aWf c = ∏_{p | c} p/(p+1)`. -/
def aWf (c : ℕ) : ℝ := ∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- `invAWf c = ∏_{p | c} (p+1)/p = 1/aWf c` (for `c ≥ 1`). -/
def invAWf (c : ℕ) : ℝ := ∏ p ∈ c.primeFactors, ((p : ℝ) + 1) / (p : ℝ)

/-- `nu n = μ(n)·aWf n`. -/
def nu (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) * aWf n

/-- The full summand of the target triple sum (verbatim copy of the target expression). -/
def bcTerm (z r t : ℕ) : ℝ :=
  (if r.Coprime t then
      (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
    ((Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ (r * t).primeFactors, (p : ℝ) / ((p : ℝ) + 1))
      * ((max (z / t) (z / r) : ℕ) : ℝ)
      * ((Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ)) - 1)
          * (Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ)) - 1) + 1))

/-- `Wt z r t = ⌊max(z/t,z/r)⌋·((log(⌊max(z/t,z/r)⌋·t/z)−1)·(log(⌊max(z/t,z/r)⌋·r/z)−1)+1)`. -/
def Wt (z r t : ℕ) : ℝ :=
  ((max (z / t) (z / r) : ℕ) : ℝ) *
    ((Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ)) - 1)
      * (Real.log ((((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ)) - 1) + 1)

/-- The inner `r`-sum over `r < t` of the target (the quantity `I(t)`). -/
def wtTerm (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (t - 1),
    (if r.Coprime t then nu r * Wt z r t else 0)

/-- The smooth main term `Mterm z r t = −(z/r)·(log(t/r)−2)`. -/
def Mterm (z r t : ℕ) : ℝ :=
  -(((z : ℝ) / (r : ℝ)) * (Real.log ((t : ℝ) / (r : ℝ)) - 2))

/-- `Fterm z r t = Wt z r t − Mterm z r t`. -/
def Fterm (z r t : ℕ) : ℝ := Wt z r t - Mterm z r t

/-- The pointwise discrepancy sum (the "error" of `wtTerm + z·(the log-weighted sum)`). -/
def errTerm (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (t - 1),
    (if r.Coprime t then nu r * Fterm z r t else 0)

/-- `S11Term z t = Σ_{r ≤ t, (r,t)=1} nu r·(log(t/r)−1)/r`. -/
def S11Term (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 t,
    (if r.Coprime t then nu r * (Real.log ((t : ℝ) / (r : ℝ)) - 1) / (r : ℝ) else 0)

/-- The "main" log-weighted Möbius sum `Σ_{r ≤ t, (r,t)=1} nu r·log(t/r)/r`. -/
def ATerm (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 t,
    (if r.Coprime t then nu r * Real.log ((t : ℝ) / (r : ℝ)) / (r : ℝ) else 0)

/-- `B11Term z t = Σ_{r ≤ t, (r,t)=1} nu r / r`. -/
def B11Term (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 t,
    (if r.Coprime t then nu r / (r : ℝ) else 0)

/-- `S2Term z t = Σ_{r < t, (r,t)=1} nu r·(log(t/r)−2)/r`. -/
def S2Term (z t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (t - 1),
    (if r.Coprime t then nu r * (Real.log ((t : ℝ) / (r : ℝ)) - 2) / (r : ℝ) else 0)

end

end Work.LinnikAreas2
