/-
# Shared definitions for `Work.Pure.b4_denom`

Denominator type of the pure function `B₄` of Calegari--Dimitrov--Tang (arXiv:2408.15403).

The plan (all in the variable `x`, with `y = x²/(x-1) = sympY`, `φ = x/(x-1) = sympPhi`):

* the auxiliary hypergeometric series `S,U,W,V` and the log-series `L`, `Li₂`;
* `B₄` (defined by the paper's double sum in `Submission.CDTPlan`) equals the
  descent `Σ_k k⁻²(P_{k+1} - x·P_{k-1})` of `Θ = (x-φ)(Li₂(x) - Li₂(φ))`, whose coefficients
  are `[1..2n]²`-integral;
* the bridge is the differential equation of `B₄` (paper eq. `diffformulas`).
-/
import Mathlib
import Submission.Work.Pure.interfaces
import Submission.CDT.SympDescent
import Submission.CDT.SympH

namespace Work.Pure

open PowerSeries
open Submission.CDT

noncomputable section

/-- `S = Σₖ C(2k,k) xᵏ = (1-4x)^{-1/2}` -/
def b4S : PowerSeries ℚ := PowerSeries.mk fun k => (Nat.centralBinom k : ℚ)

/-- `U = Σₖ C(2k,k)/(2k-1) xᵏ = -(1-4x)^{1/2}` -/
def b4U : PowerSeries ℚ := PowerSeries.mk fun k => (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) - 1)

/-- `W = Σₖ C(2k,k)/(2k+1) xᵏ` -/
def b4W : PowerSeries ℚ := PowerSeries.mk fun k => (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) + 1)

/-- `V = Σₖ C(2k,k)/(2k+1)² xᵏ` -/
def b4V : PowerSeries ℚ := PowerSeries.mk fun k => (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) + 1) ^ 2

/-- `L = log(1-x) = -Σ_{n≥1} xⁿ/n` -/
def b4L : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else -(1 / (n : ℚ))

/-- `Li₂(x) = Σ_{n≥1} xⁿ/n²` -/
def b4Li2 : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else 1 / (n : ℚ) ^ 2

/-- `Θ = (x - φ)·(Li₂(x) - Li₂(φ))` -/
def b4Theta : PowerSeries ℚ := (X - sympPhi) * (b4Li2 - b4Li2.subst sympPhi)

/-- the symmetrized powers `Pₙ(y) = xⁿ + φⁿ`, as a recurrence in the *paper's* `y`
(realised as the formal variable `X` of the ambient ring) -/
def b4P : ℕ → PowerSeries ℚ
  | 0 => 2
  | 1 => X
  | (n + 2) => X * b4P (n + 1) - X * b4P n

/-- `Q_k = P_{k+1} - y·P_{k-1}` -/
def b4Q (k : ℕ) : PowerSeries ℚ := b4P (k + 1) - X * b4P (k - 1)

/-- the descent of `Θ`, written as the explicit sum `Σ_{k≥1} k⁻²·Q_k` -/
def b4F : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (2 * n + 1), (1 / (((k + 1 : ℕ) : ℚ)) ^ 2) * PowerSeries.coeff n (b4Q (k + 1))

/-! ## coefficient formulas -/

@[simp] lemma coeff_b4S (k : ℕ) : PowerSeries.coeff k b4S = (Nat.centralBinom k : ℚ) := by
  simp [b4S]

@[simp] lemma coeff_b4U (k : ℕ) :
    PowerSeries.coeff k b4U = (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) - 1) := by
  simp [b4U]

@[simp] lemma coeff_b4W (k : ℕ) :
    PowerSeries.coeff k b4W = (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) + 1) := by
  simp [b4W]

@[simp] lemma coeff_b4V (k : ℕ) :
    PowerSeries.coeff k b4V = (Nat.centralBinom k : ℚ) / (2 * (k : ℚ) + 1) ^ 2 := by
  simp [b4V]

@[simp] lemma coeff_b4L (n : ℕ) :
    PowerSeries.coeff n b4L = if n = 0 then 0 else -(1 / (n : ℚ)) := by
  simp [b4L]

@[simp] lemma coeff_b4Li2 (n : ℕ) :
    PowerSeries.coeff n b4Li2 = if n = 0 then 0 else 1 / (n : ℚ) ^ 2 := by
  simp [b4Li2]

@[simp] lemma coeff_b4F (n : ℕ) :
    PowerSeries.coeff n b4F =
      ∑ k ∈ Finset.range (2 * n + 1),
        (1 / (((k + 1 : ℕ) : ℚ)) ^ 2) * PowerSeries.coeff n (b4Q (k + 1)) := by
  simp [b4F]

lemma b4P_zero : b4P 0 = 2 := by simp [b4P]
lemma b4P_one : b4P 1 = X := by simp [b4P]
lemma b4P_succ_succ (n : ℕ) : b4P (n + 2) = X * b4P (n + 1) - X * b4P n := by
  simp [b4P]

end

end Work.Pure
