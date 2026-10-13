import Mathlib

/-!
# The rank of a base change of a free module

If `M` is a free `A`-module and `A → B` is a ring homomorphism (here an algebra structure),
then the extension of scalars `B ⊗[A] M` is a `B`-module of the same rank: for a free module the
rank is the cardinality of a basis, and base change of a basis is a basis.  Concretely this is
Mathlib's `Module.finrank_baseChange`, `Module.finrank B (B ⊗[A] M) = Module.finrank A M`,
applied to the "algebra" tensor product, together with the fact that the tensor product used in
the definition of `ModuleCat.extendScalars` and the algebra tensor product agree definitionally
once the algebra structure is the one induced by `algebraMap`.

The `letI` below is what makes the two agree.  Replacing the (a priori arbitrary, but
propositionally equal to this one) algebra structure by `(algebraMap A B).toAlgebra` inlines its
value, so that the `Module A B` structure induced by the algebra instance reduces definitionally
to the `Module.compHom` structure that is used in the definition of `ModuleCat.extendScalars`.
The same device is used in `Work.DSEQ0.finite_extendScalars_obj`.

The hypothesis `[Nontrivial B]` is needed only to be able to use `Module.finrank_baseChange`,
which requires `StrongRankCondition` on both rings; for a nontrivial commutative ring this is
automatic, and `B` nontrivial forces `A` nontrivial.
-/

namespace Work.DSEQ0

set_option linter.style.haveILetI false

universe u

/-- The base ring of a nontrivial algebra is nontrivial: if `A` were the zero ring then `1 = 0`
in `A`, hence `1 = 0` in `B`. -/
theorem nontrivial_of_nontrivial_algebra {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Nontrivial B] : Nontrivial A := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 : (1 : A) = 0 := Subsingleton.elim 1 0
  have h2 : (1 : B) = 0 := by
    rw [← map_one (algebraMap A B), ← map_zero (algebraMap A B), h1]
  exact one_ne_zero h2

theorem finrank_extendScalars_obj {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Nontrivial B] (M : ModuleCat.{u} A) [Module.Free A ↥M] :
    Module.finrank B ↥((ModuleCat.extendScalars (algebraMap A B)).obj M) = Module.finrank A ↥M := by
  haveI : Nontrivial A := nontrivial_of_nontrivial_algebra (A := A) (B := B)
  letI : Algebra A B := (algebraMap A B).toAlgebra
  exact Module.finrank_baseChange

end Work.DSEQ0
