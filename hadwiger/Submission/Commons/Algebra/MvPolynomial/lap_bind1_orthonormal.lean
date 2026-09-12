import Mathlib.Data.Real.Basic
import Submission.Commons.Algebra.MvPolynomial.pderiv_bind1

open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

private lemma lapbo_double_sum_fold' {R : Type*} [CommSemiring R] {β : Type*} [Fintype β]
    (g : β → β → R) :
    (∑ x : β × β, g x.1 x.2) = ∑ i : β, ∑ i' : β, g i i' := by
  simpa using (Fintype.sum_prod_type (α₁ := β) (α₂ := β) (f := fun x : β × β => g x.1 x.2))

private lemma lapbo_sum_collapse {R : Type*} [CommSemiring R] {α β : Type*} [Fintype α] [Fintype β]
    (a : α → β → R) (b : β → β → R) :
    (∑ j : α, ∑ i : β, a j i * (∑ i' : β, a j i' * b i i'))
      = ∑ i : β, ∑ i' : β, (∑ j : α, a j i * a j i') * b i i' := by
  classical
  calc
    (∑ j : α, ∑ i : β, a j i * (∑ i' : β, a j i' * b i i'))
        = ∑ j : α, ∑ x : β × β, a j x.1 * a j x.2 * b x.1 x.2 := by
            apply Finset.sum_congr rfl
            intro j hj
            calc
              (∑ i : β, a j i * (∑ i' : β, a j i' * b i i'))
                  = ∑ i : β, ∑ i' : β, (a j i * a j i') * b i i' := by
                      simp [Finset.mul_sum, mul_assoc]
              _ = ∑ x : β × β, a j x.1 * a j x.2 * b x.1 x.2 := by
                      rw [lapbo_double_sum_fold' (g := fun i i' => (a j i * a j i') * b i i')]
    _ = ∑ x : β × β, ∑ j : α, a j x.1 * a j x.2 * b x.1 x.2 := by
            exact Finset.sum_comm
    _ = ∑ x : β × β, (∑ j : α, a j x.1 * a j x.2) * b x.1 x.2 := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [Finset.sum_mul]
    _ = ∑ i : β, ∑ i' : β, (∑ j : α, a j i * a j i') * b i i' := by
            rw [lapbo_double_sum_fold' (g := fun i i' => (∑ j : α, a j i * a j i') * b i i')]

private lemma lapbo_pderiv2_bind1 {n : ℕ} (f : Fin n → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (j : Fin n)
    (h1 : ∀ i : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (f i)) = 0) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv j (MvPolynomial.bind₁ f p)) =
      ∑ i : Fin n, (MvPolynomial.pderiv j (f i)) *
        (∑ i' : Fin n, (MvPolynomial.pderiv j (f i')) * MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p))) := by
  classical
  calc
    MvPolynomial.pderiv j (MvPolynomial.pderiv j (MvPolynomial.bind₁ f p))
        = MvPolynomial.pderiv j (∑ i : Fin n, MvPolynomial.pderiv j (f i) * MvPolynomial.bind₁ f (MvPolynomial.pderiv i p)) := by
            rw [pderiv_bind1]
    _ = ∑ i : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (f i) * MvPolynomial.bind₁ f (MvPolynomial.pderiv i p)) := by
            rw [map_sum]
    _ = ∑ i : Fin n, (MvPolynomial.pderiv j (MvPolynomial.pderiv j (f i)) * MvPolynomial.bind₁ f (MvPolynomial.pderiv i p)
            + MvPolynomial.pderiv j (f i) * MvPolynomial.pderiv j (MvPolynomial.bind₁ f (MvPolynomial.pderiv i p))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [MvPolynomial.pderiv_mul]
    _ = ∑ i : Fin n, MvPolynomial.pderiv j (f i) * MvPolynomial.pderiv j (MvPolynomial.bind₁ f (MvPolynomial.pderiv i p)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [h1 i]
            simp
    _ = ∑ i : Fin n, MvPolynomial.pderiv j (f i) *
            (∑ i' : Fin n, MvPolynomial.pderiv j (f i') * MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [pderiv_bind1]

theorem lap_bind1_orthonormal {n : ℕ}
    (f : Fin n → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    (h1 : ∀ i j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (f i)) = 0)
    (h2 : ∀ i i' : Fin n,
      (∑ j : Fin n, (MvPolynomial.pderiv j (f i)) * (MvPolynomial.pderiv j (f i'))) =
        (if i = i' then (1 : MvPolynomial (Fin n) ℝ) else 0)) :
    (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (MvPolynomial.bind₁ f p))) =
      MvPolynomial.bind₁ f (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j p)) := by
  classical
  calc
    (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (MvPolynomial.bind₁ f p)))
        = ∑ j : Fin n,
            (∑ i : Fin n, (MvPolynomial.pderiv j (f i)) *
              (∑ i' : Fin n, (MvPolynomial.pderiv j (f i')) * MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p)))) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact lapbo_pderiv2_bind1 f p j (fun i => h1 i j)
    _ = ∑ i : Fin n, ∑ i' : Fin n,
          (∑ j : Fin n, (MvPolynomial.pderiv j (f i)) * (MvPolynomial.pderiv j (f i'))) *
            MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p)) := by
            exact lapbo_sum_collapse (a := fun j i => MvPolynomial.pderiv j (f i))
              (b := fun i i' => MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p)))
    _ = ∑ i : Fin n, ∑ i' : Fin n,
          (if i = i' then (1 : MvPolynomial (Fin n) ℝ) else 0) *
            MvPolynomial.bind₁ f (MvPolynomial.pderiv i' (MvPolynomial.pderiv i p)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro i' hi'
            rw [h2 i i']
    _ = ∑ i : Fin n, MvPolynomial.bind₁ f (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp
    _ = MvPolynomial.bind₁ f (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j p)) := by
            rw [map_sum]

end Commons.Algebra.MvPolynomial