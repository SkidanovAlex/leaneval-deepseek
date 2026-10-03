import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORLyndon.Fox

/-!
# The augmentation ideal of a free group algebra is free on the generators `x - 1`

For a commutative ring `k` and a type `α`, the `k[F(α)]`-linear map

`φ : (α →₀ k[F(α)]) →ₗ k[F(α)],  c ↦ ∑_a c_a * (x_a - 1)`,

where `x_a = single (FreeGroup.of a) 1`, is injective.  Equivalently the augmentation ideal of
`k[F(α)]` is a *free* left `k[F(α)]`-module with basis `{x_a - 1}`.

The proof exhibits the left inverse: the classical Fox derivative.  For `b : α` the Fox derivative
`D_b = ∂/∂x_b` is the `k`-linear endomorphism of `k[F(α)]` sending a group element `g` to
`∂g/∂x_b`, and it satisfies the Leibniz rule

`D_b (g * h) = D_b g + of g * D_b h`   and   `D_b (of a) = δ_{a,b}`.

Writing `x * (x_a - 1) = x * of(x_a) - x` and applying the Leibniz rule along basis elements of
`k[F(α)]`, one obtains `D_b (x * (x_a - 1)) = δ_{a,b} * x`; hence `D_b (φ c) = c b` and `φ` is
injective.  The Fox derivative itself is provided by the module
`Submission.Work.ORLyndon.Fox` (`Work.ORLyndon.foxD`), which develops the Fox calculus of a free
group by recursion on words.
-/

open MonoidAlgebra

set_option autoImplicit false

namespace Work.ORFP2

variable (k : Type*) [CommRing k] (α : Type*) [DecidableEq α]

/-- The Fox derivative `∂/∂b` of a free group, extended `k`-linearly to the entire group algebra
`k[F(α)]`.  It sends a free group element `g` to `∂g/∂x_b`, viewed as an element of `k[F(α)]`. -/
private noncomputable def foxTheta (b : α) :
    MonoidAlgebra k (FreeGroup α) →ₗ[k] MonoidAlgebra k (FreeGroup α) :=
  (Finsupp.linearCombination k (fun g : FreeGroup α => Work.ORLyndon.foxD (K := k) b g)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private lemma foxTheta_of (b : α) (g : FreeGroup α) :
    foxTheta k α b (MonoidAlgebra.of k (FreeGroup α) g) =
      Work.ORLyndon.foxD (K := k) b g := by
  simp only [foxTheta, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]

/-- The key computation: the Fox derivative `∂/∂x_b` of `x * (x_a - 1)` is `x` when `a = b` and
`0` otherwise.  (Here `x` is an arbitrary element of `k[F(α)]`.) -/
private lemma foxTheta_mul_augGen (a b : α) (x : MonoidAlgebra k (FreeGroup α)) :
    foxTheta k α b (x * (MonoidAlgebra.of k (FreeGroup α) (FreeGroup.of a) - 1)) =
      if a = b then x else 0 := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
      rw [mul_sub,
        show MonoidAlgebra.of k (FreeGroup α) g *
              MonoidAlgebra.of k (FreeGroup α) (FreeGroup.of a)
            = MonoidAlgebra.of k (FreeGroup α) (g * FreeGroup.of a) from
          (map_mul (MonoidAlgebra.of k (FreeGroup α)) g (FreeGroup.of a)).symm,
        mul_one]
      rw [map_sub, foxTheta_of, foxTheta_of]
      rw [Work.ORLyndon.foxD_mul, Work.ORLyndon.foxD_of]
      by_cases hab : a = b <;> simp [hab]
  | add x y hx hy =>
      rw [add_mul, map_add, hx, hy]
      by_cases hab : a = b <;> simp [hab]
  | smul r x hx =>
      rw [Algebra.smul_mul_assoc, map_smul, hx]
      by_cases hab : a = b <;> simp [hab]

/-- The left-inverse property of the Fox derivative: the `b`-th coordinate of `c` is recovered as
`D_b (∑_a c_a (x_a - 1))`.  Hence the map `c ↦ ∑_a c_a (x_a - 1)` has trivial kernel. -/
private lemma sum_ker_eq_zero (e : α →₀ MonoidAlgebra k (FreeGroup α))
    (he : e.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) = 0) :
    e = 0 := by
  refine Finsupp.ext (fun b => ?_)
  have h1 : foxTheta k α b
      (e.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)))
      = e.sum (fun a x => if a = b then x else 0) := by
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro a _
    simp only [← MonoidAlgebra.of_apply]
    exact foxTheta_mul_augGen k α a b (e a)
  have h2 : e.sum (fun a x => if a = b then x else 0) = e b := by
    rw [Finsupp.sum_eq_single b]
    · simp
    · intro a _ hne; exact if_neg hne
    · intro _; simp
  have h3 := h1.trans h2
  rw [he, map_zero] at h3
  exact h3.symm

theorem augIdeal_freeGroup_injective (k : Type*) [CommRing k] (α : Type*) [DecidableEq α] :
    Function.Injective fun c : α →₀ MonoidAlgebra k (FreeGroup α) =>
      c.sum fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1) := by
  intro c d hcd
  have hcd' : c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1))
      = d.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) := hcd
  have hsub : (c - d).sum
      (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) = 0 := by
    rw [Finsupp.sum_sub_index (fun a b₁ b₂ => by rw [sub_mul]), hcd', sub_self]
  exact sub_eq_zero.mp (sum_ker_eq_zero k α (c - d) hsub)

end Work.ORFP2
