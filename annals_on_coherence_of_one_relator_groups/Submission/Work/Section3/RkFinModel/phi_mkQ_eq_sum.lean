import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.Epic.LiDim.RowSpaceToolkit

namespace Work.Section3.RkFinModel

/-!
# Decomposing an element of `R^n` in its standard basis, and a twisted additivity rule

This file collects the two elementary facts underlying `phi_mkQ_eq_sum`:

* `pi_eq_sum_smul_single` : every `x : Fin n → R` is the sum `∑ j, x j • e_j` of its coordinates
  against the standard basis vectors `e_j = Pi.single j 1`;
* `addHom_sum_smul` : an additive map `φ : L →+ S` that is "*`f`-semilinear*", i.e.
  `φ (a • l) = f a * φ l` for a ring homomorphism `f : R →+* S`, satisfies the corresponding rule
  on an arbitrary `R`-linear combination `∑ i, a i • l i`.

Since the quotient map `Submodule.mkQ _` and any linear equivalence are additive and `R`-linear,
composing them with such a `φ` immediately gives `phi_mkQ_eq_sum`: the value of `φ ∘ e` on the
class of `x` in `R^n / R^m A` is the `f`-linear combination of the values on the classes of the
standard basis vectors.
-/

universe u

variable {R : Type u} [Ring R]

/-- Every vector of `Fin n → R` is the sum of its coordinates against the standard basis
vectors `Pi.single j 1`. -/
theorem pi_eq_sum_smul_single {n : ℕ} (x : Fin n → R) :
    x = ∑ j, x j • (Pi.single j (1 : R) : Fin n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]

/-- An `R`-linear map out of `Fin n → R` is determined by its values on the standard basis
vectors: `g x = ∑ j, x j • g (Pi.single j 1)`. -/
theorem linearMap_eq_sum_smul_single {n : ℕ} {N : Type u} [AddCommGroup N] [Module R N]
    (g : (Fin n → R) →ₗ[R] N) (x : Fin n → R) :
    g x = ∑ j, x j • g (Pi.single j (1 : R)) := by
  conv_lhs => rw [pi_eq_sum_smul_single x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul g (x j) _

/-- The `f`-semilinearity rule `φ (a • l) = f a * φ l` extends to finite `R`-linear
combinations: `φ (∑ i, a i • l i) = ∑ i, f (a i) * φ (l i)`. -/
theorem addHom_sum_smul {N : Type u} [AddCommGroup N] [Module R N]
    {S : Type u} [Semiring S] (f : R →+* S) (φ : N →+ S)
    (hφ : ∀ (a : R) (l : N), φ (a • l) = f a * φ l)
    {ι : Type*} [Fintype ι] (a : ι → R) (l : ι → N) :
    φ (∑ i, a i • l i) = ∑ i, f (a i) * φ (l i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => hφ _ _

theorem phi_mkQ_eq_sum {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {L : Type u} [AddCommGroup L] [Module R L] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Work.ORHughesFree.Epic.cokerMat A ≃ₗ[R] L) (φ : L →+ S)
    (hφ : ∀ (a : R) (l : L), φ (a • l) = f a * φ l) (x : Fin n → R) :
    φ (e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)) x))
      = ∑ j, f (x j) *
          φ (e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A))
            (Pi.single j 1))) := by
  have hx := linearMap_eq_sum_smul_single
    (e.toLinearMap.comp (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)))) x
  rw [show e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A)) x)
      = ∑ j, x j • e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A))
          (Pi.single j (1 : R) : Fin n → R))
      from hx]
  exact addHom_sum_smul f φ hφ x
    (fun j : Fin n =>
      e (Submodule.mkQ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A))
        (Pi.single j (1 : R) : Fin n → R)))

end Work.Section3.RkFinModel
