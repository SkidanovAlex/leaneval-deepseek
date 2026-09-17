import Mathlib.LinearAlgebra.TensorAlgebra.Basis

namespace Commons.LinearAlgebra.TensorAlgebra

universe u

open TensorAlgebra

/-! Helpers on the free algebra of a word (list) of generators. -/

namespace word_eq_basis_helpers

section free_algebra

variable {R : Type u} [CommSemiring R]
variable {X : Type u}

/-- The equivalence `FreeAlgebra.equivMonoidAlgebraFreeMonoid` sends each generator
to the corresponding monomial of the free monoid algebra. -/
lemma psi_ι (x : X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι R x) =
      MonoidAlgebra.single (FreeMonoid.of x) (1 : R) := by
  unfold FreeAlgebra.equivMonoidAlgebraFreeMonoid
  simp [FreeAlgebra.lift_ι_apply]

/-- The basis vector of `FreeAlgebra.basisFreeMonoid` at a word is the preimage under
`FreeAlgebra.equivMonoidAlgebraFreeMonoid` of the corresponding monomial. -/
lemma basisFreeMonoid_eq (w : FreeMonoid X) :
    FreeAlgebra.basisFreeMonoid R X w =
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        (MonoidAlgebra.single w (1 : R)) := by
  unfold FreeAlgebra.basisFreeMonoid
  simp [Finsupp.basisSingleOne]

/-- Under `FreeAlgebra.equivMonoidAlgebraFreeMonoid`, the product of the generators
indexed by a word is the corresponding monomial. -/
lemma psi_word (w : List X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid ((w.map (FreeAlgebra.ι R)).prod) =
      MonoidAlgebra.single (FreeMonoid.ofList w) (1 : R) := by
  induction w with
  | nil =>
      simp [MonoidAlgebra.one_def]
  | cons x l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [map_mul]
      simp [psi_ι, ih]

/-- The basis vector of `FreeAlgebra.basisFreeMonoid` at a word is the product of the
generators indexed by that word. -/
lemma freeAlgebra_word (w : List X) :
    (w.map (FreeAlgebra.ι R)).prod = FreeAlgebra.basisFreeMonoid R X w := by
  apply AlgEquiv.injective FreeAlgebra.equivMonoidAlgebraFreeMonoid
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid ((w.map (FreeAlgebra.ι R)).prod) =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.basisFreeMonoid R X (FreeMonoid.ofList w))
  rw [psi_word]
  rw [basisFreeMonoid_eq]
  simp

end free_algebra

section tensor_algebra

variable {R : Type u} [CommRing R]
variable {M : Type u} {ι : Type u} [AddCommGroup M] [Module R M]

/-- Under the free-algebra equivalence induced by a basis, the tensor word in basis
vectors maps to the free-algebra word. -/
lemma equivFreeAlgebra_word (e : Module.Basis ι R M) (w : List ι) :
    TensorAlgebra.equivFreeAlgebra e ((w.map (fun i => TensorAlgebra.ι R (e i))).prod) =
      (w.map (FreeAlgebra.ι R)).prod := by
  induction w with
  | nil =>
      simp
  | cons x l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [map_mul]
      rw [TensorAlgebra.equivFreeAlgebra_ι_apply]
      rw [ih]

end tensor_algebra

end word_eq_basis_helpers

open word_eq_basis_helpers

/-- The tensor word `(w.map (TensorAlgebra.ι R ∘ e)).prod` equals the basis vector
`e.tensorAlgebra w` of the tensor algebra over a free module. -/
theorem word_eq_basis {R : Type u} {M : Type u} {ι : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] (e : Module.Basis ι R M) (w : List ι) :
    (w.map (fun i => TensorAlgebra.ι R (e i))).prod = e.tensorAlgebra w := by
  apply AlgEquiv.injective (TensorAlgebra.equivFreeAlgebra e)
  change TensorAlgebra.equivFreeAlgebra e ((w.map (fun i => TensorAlgebra.ι R (e i))).prod) =
    TensorAlgebra.equivFreeAlgebra e (e.tensorAlgebra (FreeMonoid.ofList w))
  rw [equivFreeAlgebra_word]
  rw [Module.Basis.tensorAlgebra]
  rw [Module.Basis.map_apply]
  simp
  rw [freeAlgebra_word]
  rfl

end Commons.LinearAlgebra.TensorAlgebra