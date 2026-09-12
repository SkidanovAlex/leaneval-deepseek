import Submission.Contracts
import Submission.WnormToolkit
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Complex weighted n-norm on Serre's interval

Complex-polynomial version of `Submission.Contracts.wnorm`:

    cwnorm k P = sup_{x ∈ [aSerre,bSerre]} w(x)^k · ‖P.eval (x : ℂ)‖

for `P : Polynomial ℂ` (‖·‖ = the complex norm).  Needed by the complex-root
Remez division lemma (Smith `lem:Remez` for complex roots), which is used in
`cor:adjust` and `lem:second_squeeze` (bounding `‖Q_i‖_n ≤ (2n)^C ‖Q‖_n` where
`Q_i = Q/(X − α_i)` and the roots `α_i` of the integer polynomial `Q` may be
complex).

API mirrors `Submission/WnormToolkit.lean` (real case): nonemptiness,
boundedness, pointwise bound, `sSup`-least-upper-bound, nonnegativity,
negation, sub-additivity, scalar-multiple, plus the compatibility
`cwnorm k (P.map (algebraMap ℝ ℂ)) = wnorm k P` for real polynomials.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.Cwnorm

open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.WnormToolkit

/-- The complex weighted k-norm of a complex polynomial on Serre's interval. -/
noncomputable def cwnorm (k : ℕ) (P : Polynomial ℂ) : ℝ :=
  sSup ((fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) '' Set.Icc aSerre bSerre)

/-- The defining set of `cwnorm` is nonempty. -/
lemma cwnorm_image_nonempty (k : ℕ) (P : Polynomial ℂ) :
    ((fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) '' Set.Icc aSerre bSerre).Nonempty := by
  refine ⟨(weight muSerre aSerre) ^ k * ‖P.eval (aSerre : ℂ)‖, aSerre, ?_⟩
  exact ⟨⟨le_rfl, WnormToolkit.a_le_b⟩, rfl⟩

/-- Complex polynomial evaluation is continuous on the interval. -/
lemma eval_continuousOn (P : Polynomial ℂ) :
    ContinuousOn (fun x : ℝ => P.eval (x : ℂ)) (Set.Icc aSerre bSerre) := by
  have hc : Continuous (fun z : ℂ => Polynomial.aeval z P) := Polynomial.continuous_aeval P
  have hof : Continuous (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal
  have hc2 : Continuous (fun x : ℝ => Polynomial.aeval (x : ℂ) P) := hc.comp hof
  convert hc2.continuousOn using 1
  ext x
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- The defining set of `cwnorm` is bounded above. -/
lemma cwnorm_image_bddAbove (k : ℕ) (P : Polynomial ℂ) :
    BddAbove ((fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) '' Set.Icc aSerre bSerre) := by
  have hcont : ContinuousOn
      (fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) (Set.Icc aSerre bSerre) := by
    refine (weight_continuous_on_Icc.pow k).mul ?_
    exact (eval_continuousOn P).norm
  have himg : IsCompact
      ((fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) '' Set.Icc aSerre bSerre) :=
    CompactIccSpace.isCompact_Icc.image_of_continuousOn hcont
  exact himg.bddAbove

/-- Pointwise bound: values on the interval are bounded by the norm. -/
lemma cwnorm_ge_pointwise (k : ℕ) (P : Polynomial ℂ) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖ ≤ cwnorm k P := by
  unfold cwnorm
  exact le_csSup (cwnorm_image_bddAbove k P) ⟨x, hx, rfl⟩

/-- `cwnorm` is the least upper bound of its defining values. -/
lemma cwnorm_sSup_le (k : ℕ) (P : Polynomial ℂ) {a : ℝ}
    (ha : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖ ≤ a) :
    cwnorm k P ≤ a := by
  unfold cwnorm
  exact csSup_le (cwnorm_image_nonempty k P) (by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ha x hx)

/-- Nonnegativity. -/
lemma cwnorm_nonneg (k : ℕ) (P : Polynomial ℂ) : 0 ≤ cwnorm k P := by
  have hmem : ((weight muSerre aSerre) ^ k * ‖P.eval (aSerre : ℂ)‖) ∈
      ((fun x : ℝ => (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) '' Set.Icc aSerre bSerre) := by
    refine ⟨aSerre, ⟨⟨le_rfl, WnormToolkit.a_le_b⟩, rfl⟩⟩
  have hval : 0 ≤ (weight muSerre aSerre) ^ k * ‖P.eval (aSerre : ℂ)‖ :=
    mul_nonneg (pow_nonneg (le_of_lt (weight_pos muSerre aSerre)) k) (norm_nonneg _)
  exact le_trans hval (le_csSup (cwnorm_image_bddAbove k P) hmem)

/-- Negation does not change the norm. -/
lemma cwnorm_neg (k : ℕ) (P : Polynomial ℂ) : cwnorm k (-P) = cwnorm k P := by
  apply le_antisymm
  · apply cwnorm_sSup_le
    intro x hx
    simpa [norm_neg] using (cwnorm_ge_pointwise k P hx)
  · apply cwnorm_sSup_le
    intro x hx
    have h := cwnorm_ge_pointwise k (-P) hx
    simpa [norm_neg] using h

/-- Sub-additivity. -/
lemma cwnorm_add_le (k : ℕ) (P Q : Polynomial ℂ) :
    cwnorm k (P + Q) ≤ cwnorm k P + cwnorm k Q := by
  apply cwnorm_sSup_le
  intro x hx
  calc
    (weight muSerre x) ^ k * ‖(P + Q).eval (x : ℂ)‖
        = (weight muSerre x) ^ k * ‖P.eval (x : ℂ) + Q.eval (x : ℂ)‖ := by simp
    _ ≤ (weight muSerre x) ^ k * (‖P.eval (x : ℂ)‖ + ‖Q.eval (x : ℂ)‖) := by
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg (le_of_lt (weight_pos muSerre x)) k)
    _ = (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖ + (weight muSerre x) ^ k * ‖Q.eval (x : ℂ)‖ := by ring
    _ ≤ cwnorm k P + cwnorm k Q := by
        exact add_le_add (cwnorm_ge_pointwise k P hx) (cwnorm_ge_pointwise k Q hx)

/-- Sub-additivity of the difference. -/
lemma cwnorm_sub_le (k : ℕ) (P Q : Polynomial ℂ) :
    cwnorm k (P - Q) ≤ cwnorm k P + cwnorm k Q := by
  have h1 : cwnorm k (P - Q) ≤ cwnorm k P + cwnorm k (-Q) := by
    simpa [sub_eq_add_neg] using cwnorm_add_le k P (-Q)
  rw [cwnorm_neg] at h1
  exact h1

/-- Norm of a scalar multiple: `‖β • P‖_k = ‖β‖·‖P‖_k`. -/
lemma cwnorm_smul (k : ℕ) (β : ℂ) (P : Polynomial ℂ) :
    cwnorm k (β • P) = ‖β‖ * cwnorm k P := by
  apply le_antisymm
  · apply cwnorm_sSup_le
    intro x hx
    calc
      (weight muSerre x) ^ k * ‖(β • P).eval (x : ℂ)‖
          = (weight muSerre x) ^ k * (‖β‖ * ‖P.eval (x : ℂ)‖) := by
              simp [smul_eq_mul, norm_mul]
      _ = ‖β‖ * ((weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖) := by ring
      _ ≤ ‖β‖ * cwnorm k P := by
          exact mul_le_mul_of_nonneg_left (cwnorm_ge_pointwise k P hx) (norm_nonneg β)
  · by_cases hβ0 : β = 0
    · subst β
      simpa using (cwnorm_nonneg k (0 : Polynomial ℂ))
    · have hpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
      have hdiv : cwnorm k P ≤ (1 / ‖β‖) * cwnorm k (β • P) := by
        apply cwnorm_sSup_le
        intro x hx
        calc
          (weight muSerre x) ^ k * ‖P.eval (x : ℂ)‖
              = (1 / ‖β‖) * ((weight muSerre x) ^ k * (‖β‖ * ‖P.eval (x : ℂ)‖)) := by
                  field_simp [ne_of_gt hpos]
          _ = (1 / ‖β‖) * ((weight muSerre x) ^ k * ‖(β • P).eval (x : ℂ)‖) := by
                  have habs : ‖β‖ * ‖P.eval (x : ℂ)‖ = ‖(β • P).eval (x : ℂ)‖ := by
                    rw [Polynomial.eval_smul]
                    simp [smul_eq_mul, norm_mul]
                  rw [habs]
          _ ≤ (1 / ‖β‖) * cwnorm k (β • P) := by
                  exact mul_le_mul_of_nonneg_left (cwnorm_ge_pointwise k (β • P) hx) (by positivity)
      calc
        ‖β‖ * cwnorm k P ≤ ‖β‖ * ((1 / ‖β‖) * cwnorm k (β • P)) := by
            exact mul_le_mul_of_nonneg_left hdiv (le_of_lt hpos)
        _ = cwnorm k (β • P) := by
            field_simp [ne_of_gt hpos]

/-- The zero polynomial has zero norm. -/
lemma cwnorm_zero (k : ℕ) : cwnorm k (0 : Polynomial ℂ) = 0 := by
  apply le_antisymm
  · apply cwnorm_sSup_le
    intro x hx
    simp
  · exact cwnorm_nonneg k 0

/-- A sum of normed terms is bounded by the sum of their individual bounds. -/
lemma cwnorm_sum_le (k : ℕ) {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) :
    cwnorm k (∑ i ∈ s, P i) ≤ ∑ i ∈ s, cwnorm k (P i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [cwnorm_zero]
  · intro a s has ih
    rw [Finset.sum_insert has]
    calc
      cwnorm k (P a + ∑ i ∈ s, P i) ≤ cwnorm k (P a) + cwnorm k (∑ i ∈ s, P i) :=
        cwnorm_add_le k (P a) (∑ i ∈ s, P i)
      _ ≤ cwnorm k (P a) + ∑ i ∈ s, cwnorm k (P i) := by
          exact add_le_add le_rfl ih
      _ = ∑ i ∈ insert a s, cwnorm k (P i) := by
          rw [Finset.sum_insert has]

/-- Complex norm of a real point equals the absolute value. -/
lemma norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simp

/-- Evaluation of a mapped real polynomial at a real-coerced point. -/
lemma eval_map_ofReal (P : Polynomial ℝ) (x : ℝ) :
    (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp [hP, hQ, Polynomial.eval_add]
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      rw [Polynomial.eval_monomial]
      norm_num

/-- Compatibility: the complex norm of the embedding of a real polynomial
equals its real norm. -/
lemma cwnorm_map_eq_wnorm (k : ℕ) (P : Polynomial ℝ) :
    cwnorm k (P.map (algebraMap ℝ ℂ)) = wnorm k P := by
  unfold cwnorm wnorm
  apply le_antisymm
  · apply cwnorm_sSup_le
    intro x hx
    rw [eval_map_ofReal, norm_ofReal]
    exact wnorm_ge_pointwise k P hx
  · apply wnorm_sSup_le
    intro x hx
    rw [← norm_ofReal, ← eval_map_ofReal]
    exact cwnorm_ge_pointwise k (P.map (algebraMap ℝ ℂ)) hx

end Submission.Cwnorm
