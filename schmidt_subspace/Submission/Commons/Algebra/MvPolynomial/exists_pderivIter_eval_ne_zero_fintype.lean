import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_pderivIter_eval_ne_zero
import Submission.Commons.Algebra.MvPolynomial.pderivIter_rename

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- **Non-vanishing lemma for an arbitrary finite set of variables.**

Let `K` be a field of characteristic zero, `f ∈ K[x_j : j ∈ τ]` a nonzero polynomial whose
degree in each variable is at most `e j` (in the sense that every monomial in the support of `f`
has `j`-th exponent at most `e j`), and let `B ≥ 1`.  Then there are integers `z j` with
`|z j| ≤ B` and a multi-index `i` with `i j ≤ e j / B` for all `j`, such that the iterated
partial derivative `∂^i f` does not vanish at `z`.

This is deduced from the `Fin N` version `exists_pderivIter_eval_ne_zero` by relabelling the
variables along the equivalence `τ ≃ Fin (Fintype.card τ)`. -/
theorem exists_pderivIter_eval_ne_zero_fintype {K : Type*} [Field K] [CharZero K] {τ : Type*}
    [Fintype τ] [DecidableEq τ] (e : τ → ℕ) (f : MvPolynomial τ K) (hf : f ≠ 0)
    (hdeg : ∀ m ∈ f.support, ∀ j : τ, m j ≤ e j) (B : ℕ) (hB : 1 ≤ B) :
    ∃ (z : τ → ℤ) (i : τ →₀ ℕ),
      (∀ j : τ, |z j| ≤ (B : ℤ)) ∧ (∀ j : τ, i j ≤ e j / B) ∧
      MvPolynomial.eval (fun j : τ => (z j : K)) (Commons.Algebra.MvPolynomial.pderivIter i f) ≠ 0 := by
  classical
  let ee : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  let f' : MvPolynomial (Fin (Fintype.card τ)) K :=
    MvPolynomial.rename (ee : τ → Fin (Fintype.card τ)) f
  let d' : Fin (Fintype.card τ) → ℕ := fun j => e (ee.symm j)
  have hf' : f' ≠ 0 := by
    intro h
    exact hf ((MvPolynomial.rename_eq_zero_iff_of_injective f ee.injective).mp h)
  have hdeg' : ∀ m ∈ f'.support, ∀ j : Fin (Fintype.card τ), m j ≤ d' j := by
    intro m hm j
    have h1 : m j ≤ f'.degreeOf j := MvPolynomial.monomial_le_degreeOf j hm
    have h2 : f'.degreeOf j = f.degreeOf (ee.symm j) := by
      have h := MvPolynomial.degreeOf_rename_of_injective (p := f)
        (f := (ee : τ → Fin (Fintype.card τ))) ee.injective (ee.symm j)
      simpa [f', Equiv.apply_symm_apply] using h
    have h3 : f.degreeOf (ee.symm j) ≤ e (ee.symm j) :=
      MvPolynomial.degreeOf_le_iff.mpr (fun m' hm' => hdeg m' hm' (ee.symm j))
    calc m j ≤ f'.degreeOf j := h1
      _ = f.degreeOf (ee.symm j) := h2
      _ ≤ e (ee.symm j) := h3
  obtain ⟨z', i', hz', hi', hne⟩ :=
    exists_pderivIter_eval_ne_zero (K := K) d' f' hf' hdeg' B hB
  let z : τ → ℤ := fun a => z' (ee a)
  let i : τ →₀ ℕ := Finsupp.equivMapDomain ee.symm i'
  refine ⟨z, i, ?_, ?_, ?_⟩
  · intro a
    exact hz' (ee a)
  · intro a
    have hia : i a = i' (ee a) := Finsupp.equivMapDomain_symm_apply ee i' a
    rw [hia]
    have h := hi' (ee a)
    simpa [d', Equiv.symm_apply_apply] using h
  · have hmap : i.mapDomain (ee : τ → Fin (Fintype.card τ)) = i' := by
      ext j
      rw [← Equiv.apply_symm_apply ee j]
      rw [Finsupp.mapDomain_apply ee.injective]
      exact Finsupp.equivMapDomain_symm_apply ee i' (ee.symm j)
    have hpr := pderivIter_rename (ee : τ → Fin (Fintype.card τ)) ee.injective i f
    have h1 : pderivIter i' f' =
        MvPolynomial.rename (ee : τ → Fin (Fintype.card τ)) (pderivIter i f) := by
      rw [hmap] at hpr
      exact hpr
    have hne' : MvPolynomial.eval (fun j : Fin (Fintype.card τ) => (z' j : K))
        (pderivIter i' f') ≠ 0 := hne
    rw [h1, MvPolynomial.eval_rename] at hne'
    have hcomp : (fun j : Fin (Fintype.card τ) => (z' j : K)) ∘
        (ee : τ → Fin (Fintype.card τ)) = (fun a : τ => (z a : K)) := by
      funext a; rfl
    rw [hcomp] at hne'
    exact hne'

end Commons.Algebra.MvPolynomial
