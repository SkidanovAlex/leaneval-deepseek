import Mathlib
import Submission.Work.HP.Vero.MulDefs

/-!
# `formEval` is multiplicative with respect to `mulVec`

The coefficient vector `mulVec a b d A B` (`Work.HP.Vero.mulVec`, zero unless `d = a + b`) is
the coefficient vector of the product of the forms with coefficient vectors `A` and `B`.  This
file proves the corresponding evaluation identity, over an arbitrary commutative ring `R`:

`formEval (a + b) n (mulVec a b (a + b) A B) x = formEval a n A x * formEval b n B x`.

The proof is the primitive computation, in three steps.

* `addMon_eq_iff` : the componentwise condition appearing in the definition of `mulVec` is
  exactly the equation `addMon p q = M`; consequently, for fixed `(p,q)` the sum over `M` of the
  indicator of `addMon p q = M` times a function picks out the single value at `addMon p q`.
* `sum_ite_prod_mul` : the abstract rearrangement implementing that step
  (`∑_M (∑_{p,q} [g p q = M] · c p q) · h M = ∑_{p,q} c p q · h (g p q)`).
* `veronese_addMon` : `ν(x)` is multiplicative: `ν(p + q) = ν(p) · ν(q)`.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

/-! ## Elementary exchange lemma -/

/-- Sums of the form `∑_M (∑_{p,q} [g p q = M] · c p q) · h M` collapse to
`∑_{p,q} c p q · h (g p q)`: the conjugate of `c p q` against `h` is picked out at the unique
index `g p q`. -/
lemma sum_ite_prod_mul {α₁ α₂ γ M : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ]
    [DecidableEq γ] [NonUnitalNonAssocSemiring M] (g : α₁ → α₂ → γ)
    (c : α₁ → α₂ → M) (h : γ → M) :
    (∑ y : γ, (∑ a₁, ∑ a₂, if g a₁ a₂ = y then c a₁ a₂ else 0) * h y)
      = ∑ a₁, ∑ a₂, c a₁ a₂ * h (g a₁ a₂) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-! ## `addMon` -/

/-- The exponent-equality condition used in `mulVec` characterises `addMon`: the components of
`M` are the componentwise sums of those of `p` and `q` exactly when `M = addMon p q`. -/
lemma addMon_eq_iff {a b n : ℕ} (p : Mon a n) (q : Mon b n) (M : Mon (a + b) n) :
    addMon p q = M ↔ ∀ i, (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ) := by
  constructor
  · intro h i
    rw [← h]
    exact addMon_val p q i
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact h i

/-- The Veronese monomial of a product of monomials is the product of the Veronese
monomials. -/
lemma veronese_addMon {a b n : ℕ} {R : Type*} [CommSemiring R]
    (x : Fin (n + 1) → R) (p : Mon a n) (q : Mon b n) :
    veronese (a + b) n x (addMon p q) = veronese a n x p * veronese b n x q := by
  simp only [veronese, addMon_val, pow_add, Finset.prod_mul_distrib]

/-! ## The main identity -/

/-- `formEval` is multiplicative with respect to `mulVec`: the form whose coefficient vector is
`mulVec a b (a + b) A B` is the product of the forms with coefficient vectors `A` and `B`. -/
theorem mulVec_formEval {a b n : ℕ} {R : Type*} [CommRing R]
    (A : Mon a n → ℤ) (B : Mon b n → ℤ) (x : Fin (n + 1) → R) :
    formEval (a + b) n (mulVec a b (a + b) A B) x
      = formEval a n A x * formEval b n B x := by
  rw [formEval, formEval, formEval]
  rw [Finset.sum_mul_sum]
  -- Expand `mulVec` and push the ring cast `ℤ → R` through the finite sums and products.
  simp only [mulVec]
  push_cast
  -- Replace the componentwise condition by the equation `addMon p q = M`.
  simp only [← addMon_eq_iff]
  rw [sum_ite_prod_mul (fun p (q : Mon b n) => addMon p q)
      (fun p q => (A p : R) * (B q : R)) (fun M => veronese (a + b) n x M)]
  -- Now both sides are double sums over monomial pairs; match the terms.
  simp only [veronese_addMon]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

end Work.HP.Vero
