import ChallengeDeps
import Mathlib.FieldTheory.Minpoly.Basic

open AlgebraicIntegers
open ComplexOrder

set_option autoImplicit false

namespace Submission.Reduction

/-!
This module proves the reduction: an infinite family of totally positive algebraic
integers, all satisfying `trace < c * degree` (for a real constant `c`), implies
`lambda_SSS ≤ c`.

Here `trace α < (c : ℂ) * degree α` is a comparison in the complex order (all real).
-/

/-- The finiteness condition from the definition of `lambda_SSS`, at `lam, ε`. -/
def Fam (lam : ℝ) (ε : ℝ) : Set ℂ :=
  { α : ℂ | IsIntegral ℤ α ∧ IsTotallyPositive α ∧ trace α < (lam - ε) * degree α }

/-- If every element of a multiset of complex numbers is real, so is the sum. -/
private lemma multiset_im_sum {m : Multiset ℂ} (hm : ∀ z ∈ m, z.im = 0) :
    (m.sum).im = 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a.im = 0 := hm a (by simp)
      have hs : (s.sum).im = 0 := ih (fun z hz => hm z (by simp [hz]))
      simp [ha, hs]

/-- If every element of a multiset of complex numbers has nonnegative real part,
so does the sum. -/
private lemma multiset_re_sum_nonneg {m : Multiset ℂ} (hm : ∀ z ∈ m, 0 ≤ z.re) :
    0 ≤ (m.sum).re := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 0 ≤ a.re := hm a (by simp)
      have hs : 0 ≤ (s.sum).re := ih (fun z hz => hm z (by simp [hz]))
      rw [Multiset.sum_cons, Complex.add_re]
      exact add_nonneg ha hs

/-- The trace of a totally positive algebraic number is real. -/
lemma trace_im_eq_zero_of_isTotallyPositive {α : ℂ} (hα : IsTotallyPositive α) :
    (trace α).im = 0 := by
  unfold trace at ⊢
  unfold IsTotallyPositive at hα
  rcases hα with ⟨_halg, hall⟩
  exact multiset_im_sum (fun β hβ => by
    exact (Complex.pos_iff.mp (hall β hβ)).2.symm)

/-- The trace of a totally positive algebraic number has nonnegative real part. -/
lemma trace_re_nonneg_of_isTotallyPositive {α : ℂ} (hα : IsTotallyPositive α) :
    0 ≤ (trace α).re := by
  unfold trace at ⊢
  unfold IsTotallyPositive at hα
  rcases hα with ⟨_halg, hall⟩
  exact multiset_re_sum_nonneg (fun β hβ => by
    exact le_of_lt (Complex.pos_iff.mp (hall β hβ)).1)

/-- The trace of a totally positive algebraic number is a nonnegative real. -/
lemma trace_nonneg_of_isTotallyPositive {α : ℂ} (hα : IsTotallyPositive α) :
    0 ≤ trace α := by
  rw [Complex.nonneg_iff]
  exact ⟨trace_re_nonneg_of_isTotallyPositive hα, by
    simpa [eq_comm] using (trace_im_eq_zero_of_isTotallyPositive hα)⟩

/-- For an algebraic number whose trace is real, comparing `trace α < (x : ℂ) * degree α`
in the complex order is the same as comparing real numbers. -/
lemma trace_lt_mul_degree_iff {α : ℂ} {x : ℝ} (him : (trace α).im = 0) :
    trace α < (x : ℂ) * degree α ↔ (trace α).re < x * (degree α : ℝ) := by
  rw [Complex.lt_def]
  simp [him]

/-- If an injective family `f` consists of totally positive algebraic integers with
`trace (f n) < c * degree (f n)` for all `n`, then `lambda_SSS ≤ c`. -/
theorem lambda_SSS_le_of_family (c : ℝ) (f : ℕ → ℂ) (hinj : Function.Injective f)
    (h : ∀ n, IsIntegral ℤ (f n) ∧ IsTotallyPositive (f n) ∧ trace (f n) < (c : ℂ) * degree (f n)) :
    lambda_SSS ≤ c := by
  let T : Set ℝ := { lam : ℝ | ∀ ε > (0 : ℝ), (Fam lam ε).Finite }
  have hT : lambda_SSS = sSup T := by
    unfold lambda_SSS
    rfl
  -- `0` belongs to `T`: with `lam = 0` and `ε > 0`, no totally positive algebraic
  -- integer can satisfy `trace α < -ε * degree α`, because traces are nonnegative.
  have h0T : (0 : ℝ) ∈ T := by
    change ∀ ε > (0 : ℝ), (Fam 0 ε).Finite
    intro ε hε
    have hFam_empty : Fam 0 ε = (∅ : Set ℂ) := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro α hmem
      rcases hmem with ⟨hint, htp, htr⟩
      have hnonneg : 0 ≤ trace α := trace_nonneg_of_isTotallyPositive htp
      have hneg : (0 - ε) * degree α ≤ (0 : ℂ) := by
        rw [Complex.le_def]
        constructor
        · have h1 : -ε ≤ (0 : ℝ) := by linarith
          have hr : (0 - ε) * (degree α : ℝ) ≤ (0 : ℝ) := by
            simpa [sub_eq_add_neg] using
              (mul_nonpos_of_nonpos_of_nonneg h1 (Nat.cast_nonneg (degree α)))
          simpa using hr
        · simp
      have hlt : trace α < 0 := lt_of_lt_of_le htr hneg
      exact (not_lt_of_ge hnonneg) hlt
    simp [hFam_empty]
  -- Any `lam` with `c < lam` fails to lie in `T`: the injective family `f` is an
  -- infinite subset of `Fam lam ε₀` with `ε₀ = (lam - c) / 2 > 0`.
  have hT_sub : T ⊆ { lam : ℝ | lam ≤ c } := by
    intro lam hlam
    by_contra hnotle
    have hcl : c < lam := lt_of_not_ge hnotle
    let ε0 : ℝ := (lam - c) / 2
    have hε0 : 0 < ε0 := by
      dsimp [ε0]
      linarith
    have hlamε : (Fam lam ε0).Finite := by
      change ∀ ε > (0 : ℝ), (Fam lam ε).Finite at hlam
      exact hlam ε0 hε0
    have hrange_sub : Set.range f ⊆ Fam lam ε0 := by
      rw [Set.range_subset_iff]
      intro n
      rcases h n with ⟨hint, htp, htrc⟩
      refine ⟨hint, htp, ?_⟩
      -- from the complex-order inequality extract real inequalities
      have htrre : (trace (f n)).re < c * (degree (f n) : ℝ) := by
        have hlt : (trace (f n)).re < ((c : ℂ) * degree (f n)).re :=
          (Complex.lt_def.mp htrc).1
        simpa using hlt
      have htrim : (trace (f n)).im = 0 := by
        have him : (trace (f n)).im = ((c : ℂ) * degree (f n)).im :=
          (Complex.lt_def.mp htrc).2
        simpa using him
      -- the degree is positive: otherwise `trace (f n) < 0`, contradicting
      -- the nonnegativity of the trace of a totally positive element.
      have hdeg_pos : 0 < degree (f n) := by
        by_contra hdeg0
        have hd : degree (f n) = 0 := Nat.eq_zero_of_not_pos hdeg0
        have htr0 : trace (f n) < 0 := by
          simpa [hd] using htrc
        exact (not_lt_of_ge (trace_nonneg_of_isTotallyPositive htp)) htr0
      have hclambda : c < lam - ε0 := by
        dsimp [ε0]
        linarith
      have hprod : c * (degree (f n) : ℝ) < (lam - ε0) * (degree (f n) : ℝ) := by
        exact mul_lt_mul_of_pos_right hclambda (by exact_mod_cast hdeg_pos)
      have hlt1 : (trace (f n)).re < (lam - ε0) * (degree (f n) : ℝ) :=
        lt_trans htrre hprod
      have hlt2 : trace (f n) < ((lam - ε0 : ℝ) : ℂ) * degree (f n) :=
        (trace_lt_mul_degree_iff htrim).mpr hlt1
      simpa [← Complex.ofReal_sub] using hlt2
    have hfinRange : (Set.range f).Finite := hlamε.subset hrange_sub
    exact (Set.infinite_range_of_injective hinj) hfinRange
  rw [hT]
  exact csSup_le ⟨0, h0T⟩ (by
    intro lam hlam
    exact (by simpa using hT_sub hlam))

end Submission.Reduction
