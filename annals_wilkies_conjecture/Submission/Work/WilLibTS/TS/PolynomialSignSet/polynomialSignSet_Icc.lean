import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite

namespace Work.WilLibTS.TS.PolynomialSignSet

open Set

variable {X ι : Type*} {c : X → ι → ℝ}

/-- The set `{x | 0 ≤ eval (c x) p}` is a polynomial sign set: it is the union of the
positivity set of `p` and the zero set of `p`. -/
lemma nonneg (p : MvPolynomial ι ℝ) :
    Work.WilLibTS.TS.PolynomialSignSet c {x | 0 ≤ MvPolynomial.eval (c x) p} := by
  have h : {x | 0 ≤ MvPolynomial.eval (c x) p}
      = {x | 0 < MvPolynomial.eval (c x) p} ∪ {x | MvPolynomial.eval (c x) p = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact ⟨fun hx => (lt_or_eq_of_le hx).imp id Eq.symm,
      fun hx => hx.elim le_of_lt (fun h => h.ge)⟩
  rw [h]
  exact (Work.WilLibTS.TS.PolynomialSignSet.positive p).union
    (Work.WilLibTS.TS.PolynomialSignSet.zero p)

theorem polynomialSignSet_Icc {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  refine PolynomialSignSet.forall_finite (c := (id : (ι → ℝ) → ι → ℝ))
    (α := ι) (fun i x => a i ≤ x i ∧ x i ≤ b i) ?_
  intro i
  have hlower : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | a i ≤ x i} := by
    have h := nonneg (c := (id : (ι → ℝ) → ι → ℝ))
      (MvPolynomial.X i - MvPolynomial.C (a i))
    convert h using 1
    ext x
    simp [sub_nonneg]
  have hupper : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | x i ≤ b i} := by
    have h := nonneg (c := (id : (ι → ℝ) → ι → ℝ))
      (MvPolynomial.C (b i) - MvPolynomial.X i)
    convert h using 1
    ext x
    simp [sub_nonneg]
  convert hlower.inter hupper using 1
  ext x
  simp

end Work.WilLibTS.TS.PolynomialSignSet
