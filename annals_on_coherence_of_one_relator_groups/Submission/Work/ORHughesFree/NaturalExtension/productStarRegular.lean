import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.StarRegular.isPositiveDefiniteStarRegular_matrix
import Submission.Work.ORHughesFree.StarRegular.isStarRegular_of_ringEquiv

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## ∗-regularity of products

`W U = ∏_{n ≥ 1} M_n(U)` is a product of matrix rings over `U`. Since `U` is positive definite
∗-regular, each factor `M_{n+1}(U)` is ∗-regular, and both the ∗-regularity of `W U` and the
positive definiteness of `W U` follow because forming a product commutes with forming matrix
rings: `M_k(∏_n R_n) ≃ ∏_n M_k(R_n)`, and a product of ∗-regular rings is ∗-regular
(the weak inverse and the properness of the involution are checked componentwise). -/

/-- A product of ∗-regular rings is ∗-regular: weak inverses are taken componentwise and the
involution is proper componentwise. -/
private theorem isStarRegular_forall {ι : Type*} {R : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, StarRing (R i)] (h : ∀ i, IsStarRegular (R i)) :
    IsStarRegular (∀ i, R i) := by
  refine ⟨⟨fun f => ?_⟩, fun f hf => ?_⟩
  · choose g hg using fun i => (h i).vonNeumannRegular.exists_mul_inverse (f i)
    exact ⟨g, funext fun i => hg i⟩
  · funext i
    exact (h i).proper (f i) (by
      have := congr_fun hf i
      simpa using this)

/-- The product of the matrix rings over the factors of a dependent product of rings is the
matrix ring over the product: `∏_n M_k(R_n) ≃+* M_k(∏_n R_n)`, componentwise and entrywise. -/
private noncomputable def matrixForallEquiv {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]
    (m : Type*) [Fintype m] [DecidableEq m] :
    (∀ i, Matrix m m (R i)) ≃+* Matrix m m (∀ i, R i) where
  toFun B := Matrix.of fun j k => fun i => B i j k
  invFun A := fun i => Matrix.of fun j k => A j k i
  left_inv B := by funext i j k; rfl
  right_inv A := by funext j k i; rfl
  map_add' A B := by ext j k i; rfl
  map_mul' A B := by
    ext j k i
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]

/-- The equivalence `∏_n M_k(R_n) ≃+* M_k(∏_n R_n)` is compatible with the
conjugate-transpose involutions on both sides. -/
private theorem matrixForallEquiv_star {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]
    [∀ i, StarRing (R i)] (m : Type*) [Fintype m] [DecidableEq m]
    (B : ∀ i, Matrix m m (R i)) :
    matrixForallEquiv (R := R) m (star B) = star (matrixForallEquiv (R := R) m B) := by
  ext j k i
  rfl

theorem productStarRegular {U : Type} [Ring U] [StarRing U] (hpos : IsPositiveDefiniteStarRegular U) :
    IsStarRegular (W U) ∧ IsPositiveDefiniteStarRegular (W U) := by
  constructor
  · exact isStarRegular_forall (R := fun n => Matrix (Fin (n+1)) (Fin (n+1)) U) fun n => hpos (n + 1)
  · intro k
    refine Work.ORHughesFree.StarRegular.isStarRegular_of_ringEquiv
      (matrixForallEquiv (R := fun n => Matrix (Fin (n+1)) (Fin (n+1)) U) (Fin k)) (fun B => ?_) ?_
    · exact matrixForallEquiv_star _ B
    · exact isStarRegular_forall fun n =>
        Work.ORHughesFree.StarRegular.isPositiveDefiniteStarRegular_matrix hpos (n + 1) k

end Work.ORHughesFree.NaturalExtension
