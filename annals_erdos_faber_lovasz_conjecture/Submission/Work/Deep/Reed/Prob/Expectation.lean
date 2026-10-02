import Submission.Work.Deep.Reed.Prob.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Expectations in a finite probability space

The expectation of a real-valued random variable on a finite probability space,
with the basic calculus (linearity, monotonicity, and the relation to `prob`
for indicator variables).  This is the tool used to compute the expected
number of "repeated colours" in the naive colouring procedure.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Reed

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- **Expectation** of a real-valued random variable. -/
noncomputable def exp (μ : FinProb Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.wt ω * X ω

lemma exp_nonneg (μ : FinProb Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.exp X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.wt_nonneg ω) (h ω)

lemma exp_mono (μ : FinProb Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : μ.exp X ≤ μ.exp Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.wt_nonneg ω)

lemma exp_const (μ : FinProb Ω) (c : ℝ) : μ.exp (fun _ => c) = c := by
  rw [exp, ← Finset.sum_mul, μ.wt_sum, one_mul]

lemma exp_add (μ : FinProb Ω) (X Y : Ω → ℝ) :
    μ.exp (fun ω => X ω + Y ω) = μ.exp X + μ.exp Y := by
  rw [exp, exp, exp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma exp_mul_left (μ : FinProb Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.exp (fun ω => c * X ω) = c * μ.exp X := by
  rw [exp, exp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma exp_sum {ι : Type*} [Fintype ι] (μ : FinProb Ω) (X : ι → Ω → ℝ) :
    μ.exp (fun ω => ∑ i, X i ω) = ∑ i, μ.exp (X i) := by
  simp only [exp, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma exp_sub (μ : FinProb Ω) (X Y : Ω → ℝ) :
    μ.exp (fun ω => X ω - Y ω) = μ.exp X - μ.exp Y := by
  rw [exp, exp, exp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- A sum over a finset, written as a sum of indicators over the whole space. -/
lemma sum_finset_eq_sum_ite [DecidableEq Ω] (s : Finset Ω) (f : Ω → ℝ) :
    (∑ ω ∈ s, f ω) = ∑ ω, if ω ∈ s then f ω else 0 := by
  classical
  have h := Finset.sum_filter (s := (Finset.univ : Finset Ω)) (p := fun ω => ω ∈ s) (f := f)
  have h2 : (Finset.univ.filter (fun ω => ω ∈ s)) = s := by ext ω; simp
  rw [h2] at h
  simpa using h.symm

/-- The probability of a finite event (given as a `Finset`). -/
lemma prob_coe_finset [DecidableEq Ω] (μ : FinProb Ω) (s : Finset Ω) :
    μ.prob (s : Set Ω) = ∑ ω ∈ s, μ.wt ω := by
  classical
  rw [prob, sum_finset_eq_sum_ite s μ.wt]
  exact Finset.sum_congr rfl fun ω _ => by by_cases h : ω ∈ s <;> simp [h]

/-- The expectation of the indicator of a finite event. -/
lemma exp_indFinset [DecidableEq Ω] (μ : FinProb Ω) (s : Finset Ω) :
    μ.exp (fun ω => if ω ∈ s then (1 : ℝ) else 0) = ∑ ω ∈ s, μ.wt ω := by
  classical
  rw [exp, sum_finset_eq_sum_ite s μ.wt]
  exact Finset.sum_congr rfl fun ω _ =>
    by by_cases h : ω ∈ s <;> simp [h]

/-- Expectation of a natural-number-valued random variable. -/
noncomputable def expNat (μ : FinProb Ω) (X : Ω → ℕ) : ℝ := μ.exp fun ω => (X ω : ℝ)

lemma expNat_nonneg (μ : FinProb Ω) (X : Ω → ℕ) : 0 ≤ μ.expNat X :=
  exp_nonneg μ fun ω => Nat.cast_nonneg _

end FinProb

end Work.Deep.Reed
