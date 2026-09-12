import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.WeightedNorm
import Submission.Notions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Squarefree.Basic

/-!
# The four deep contracts of Smith's converse — precise statements (Phase 0)

Specialized to the Serre data:  Σ = [aSerre, bSerre]  (0 < a < b, κ := (b−a)/4 > 1),
μ = serreMeasure gSerre aSerre bSerre (probability, Hölder, supported on Σ,
arithmetic — all machine-verified in the analytic layer).  The statements are
the paper's Theorem squarefree (GON.tex), Corollary adjust (Cor 3.3), the
whole of Proposition early_ints_better (Prop 4.1, clauses 1–4 of adjust.tex),
and the RSphere lemma (Lemma 2.8, prelim.tex) restricted to what the final
assembly needs (root means → first moment).
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open Filter
open scoped Real BigOperators Topology
open Polynomial

namespace Submission.Contracts

open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.Notions

/-- Capacity constant of the Serre interval:  κ = (b − a)/4  >  1. -/
noncomputable def kappa : ℝ := (bSerre - aSerre) / 4

/-- κ > 1 (b − a > 4; verified numerically). -/
lemma kappa_gt_one : 1 < kappa := by
  unfold kappa
  norm_num [aSerre, bSerre]

/-- The Serre measure of the application. -/
noncomputable def muSerre : Measure ℝ := serreMeasure gSerre aSerre bSerre

/-- Weighted k-norm of a REAL polynomial on Serre's interval with Serre's measure:
`sup_{x ∈ [aSerre,bSerre]} w(x)^k |P(x)|`,  w = WeightedNorm.weight. -/
noncomputable def wnorm (k : ℕ) (P : Polynomial ℝ) : ℝ :=
  sSup ((fun x : ℝ => (weight muSerre x) ^ k * |P.eval x|) '' Set.Icc aSerre bSerre)

/-- The integer polynomial Q, viewed over ℝ. -/
noncomputable def zmap (Q : Polynomial ℤ) : Polynomial ℝ := Q.map (algebraMap ℤ ℝ)

/-- `m(B,n) = ⌊ B·√n·log n ⌋` — the number of low coefficients adjusted in
the early-ints construction (paper writes `m = ⌊B√n log n⌋`). -/
noncomputable def mFloor (B : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ))

/-- Real power bound `n^{C·√n}` (as in Theorem squarefree). -/
noncomputable def npow (n : ℕ) (C : ℝ) : ℝ := (n : ℝ) ^ (C * Real.sqrt (n : ℝ))

/-- Upper bound on the floor: `⌊B·√n·log n⌋ ≤ B·√n·log n` for `B ≥ 0`, `n ≥ 2`. -/
lemma mFloor_le {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    (mFloor B n : ℝ) ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  unfold mFloor
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_trans (by norm_num : (1:ℕ) ≤ 2) hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hx : 0 ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) hlog
  exact Nat.floor_le hx

/-- Lower bound on the floor: `B·√n·log n − 1 ≤ ⌊B·√n·log n⌋` (real forms). -/
lemma mFloor_ge_sub_one {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) - 1 ≤ (mFloor B n : ℝ) := by
  unfold mFloor
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_trans (by norm_num : (1:ℕ) ≤ 2) hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hx : 0 ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) hlog
  have hlt : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) <
      (Nat.floor (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (B * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
  linarith

/-! ## Contract 1 — Theorem squarefree (weighted n-norm; exponent = degree)

For some `C > 0` (from μ and Σ), every degree `n ≥ 2` has a squarefree integer
polynomial of degree n with `‖Q‖_n ≤ n^{C√n}` (weighted norm at exponent n).
-/
def SquarefreeContract : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      ∃ Q : Polynomial ℤ, Squarefree Q ∧ Q.natDegree = n ∧
        wnorm n (zmap Q) ≤ npow n C

/-! ## Contract 2 — Corollary adjust (weighted n-norm; exponent = deg Q)

For some `C > 0`, whenever `n ≥ 2`, `Q` is a squarefree integer polynomial of
degree n and `P` is a real polynomial of degree ≤ n−1, there is an integer
polynomial `R` of degree ≤ n−1 with `‖P − R‖_n ≤ n^C · ‖Q‖_n`.
-/
def AdjustContract : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ Q : Polynomial ℤ, Squarefree Q → Q.natDegree = n →
    ∀ P : Polynomial ℝ, P.natDegree ≤ n - 1 →
      ∃ R : Polynomial ℤ, R.natDegree ≤ n - 1 ∧
        wnorm n (P - zmap R) ≤ (n : ℝ) ^ C * wnorm n (zmap Q)

/-! ## Contract 3b — the body of the early-ints construction (reusable) -/

/-- The data produced by Proposition early_ints_better for one index `n`
(with `m = ⌊B√n log n⌋`): a monic degree-`n` real polynomial factorizing over
strictly increasing roots in the open Serre interval, bracketed by intervals
with strong weighted endpoint lower bounds, high coefficients even integers,
and a weighted norm bound, PLUS the quantitative root-mean clause
`|(Σᵢ αᵢ)/n − ∫x∂μ| ≤ Cm·(m+1)/n` (this is the keystone's replacement for a
RSphere/Saff–Totik input). -/
abbrev EarlyPolynomialData (B C1 Cm : ℝ) (n : ℕ) : Prop :=
  let m := mFloor B n
  ∃ P : Polynomial ℝ,
    P.Monic ∧ P.natDegree = n ∧
    (∃ α x y : Fin n → ℝ,
      P = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) ∧
      (∀ i : Fin n, aSerre < α i ∧ α i < bSerre) ∧
      (∀ i : Fin n, ∀ j : Fin n, i.val < j.val → α i < α j) ∧
      (∀ i : Fin n, aSerre ≤ x i ∧ y i ≤ bSerre) ∧
      (∀ i : Fin n, x i < y i) ∧
      (∀ i : Fin n, x i < α i ∧ α i < y i) ∧
      (∀ i : Fin n, ∀ j : Fin n, i.val < j.val → y i < x j) ∧
      (∀ i : Fin n,
        (weight muSerre (x i)) ^ (n - m) * |P.eval (x i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m ∧
        (weight muSerre (y i)) ^ (n - m) * |P.eval (y i)| ≥ (n : ℝ) ^ (-C1) * kappa ^ m ∧
        P.eval (x i) ≠ 0 ∧ P.eval (y i) ≠ 0) ∧
      |((∑ i : Fin n, α i) / (n : ℝ)) - (∫ x : ℝ, x ∂muSerre)|
          ≤ Cm * ((mFloor B n : ℝ) + 1) / (n : ℝ)) ∧
    (∀ k : ℕ, n - m ≤ k → k ≤ n - 1 → ∃ z : ℤ, P.coeff k = (z : ℝ) ∧ Even z) ∧
    wnorm (n - m) P ≤ (n : ℝ) ^ C1 * kappa ^ m

/-! ## Contract 3 — Proposition early_ints_better (clauses 1–4)

For every `B > 0` there are `C > 3` and `Cm ≥ 0` such that for every integer
`n > C` with `2 ≤ n − m` (`m = ⌊B√n log n⌋`), `EarlyPolynomialData B C Cm n`
holds (see above).  The final (root-mean) clause is what the keystone uses in
place of a RSphere/Saff–Totik input.
-/
def EarlyIntsContract : Prop :=
  ∀ B : ℝ, 0 < B →
    ∃ C Cm : ℝ, 3 < C ∧ 0 ≤ Cm ∧
      ∀ n : ℕ, (C : ℝ) < n → 2 ≤ n - mFloor B n →
        EarlyPolynomialData B C Cm n

/-! ## Contract 4 — RSphere (moment form, what the assembly needs)

Any sequence of monic integer polynomials which, for all sufficiently large n,
have degree n and complex roots all lying in the OPEN Serre interval
`(aSerre, bSerre)`, and whose weighted n-norm grows subexponentially
(`‖R_n‖_n ≤ n^{C√n}` for SOME `C > 0`), has root means converging to the
first moment `∫ x dμ`.
-/
def RSphereContract : Prop :=
  ∀ R : ℕ → Polynomial ℤ,
    (∀ᶠ n : ℕ in atTop, (R n).Monic ∧ (R n).natDegree = n ∧
      ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) →
    (∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, wnorm n (zmap (R n)) ≤ npow n C) →
    Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop
      (𝓝 (∫ x : ℝ, x ∂muSerre))

/-! ## Contract 5 — the full converse output at Serre's data

The composition of Contracts 1–4 (keystone, `Submission/ConverseAssembly.lean`)
produces the exact output of `smith_converse_interval` for `μ = muSerre`,
which `Submission/FinalAssembly.lean` consumes.
-/
def ConverseOutputSerre : Prop :=
  ∃ R : ℕ → Polynomial ℤ,
    (∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree) ∧
    (∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
    Tendsto (fun n : ℕ => (R n).natDegree) atTop atTop ∧
    Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop
      (𝓝 (∫ x : ℝ, x ∂muSerre))

end Submission.Contracts
