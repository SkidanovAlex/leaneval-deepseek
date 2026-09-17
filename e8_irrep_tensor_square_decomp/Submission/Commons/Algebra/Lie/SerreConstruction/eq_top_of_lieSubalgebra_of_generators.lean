import Mathlib.Algebra.Lie.SerreConstruction

namespace Commons.Algebra.Lie.SerreConstruction

/-- A Lie subalgebra of the Serre-constructed Lie algebra (quotient of the free Lie algebra by the
Serre relations) containing the images of the generators `H i`, `E i`, `F i` is everything.

Suggested proof: build the quotient map `q : FreeLieAlgebra R _ →ₗ⁅R⁆ (FreeLieAlgebra R _ ⧸ J)`
with `toLinearMap := (LieSubmodule.Quotient.mk' J).toLinearMap` and
`map_lie' := LieSubmodule.Quotient.mk_bracket`, note it is surjective
(`LieSubmodule.Quotient.surjective_mk'`); build the lift
`ψ : FreeLieAlgebra R _ →ₗ⁅R⁆ N` of the generators into `N` with `FreeLieAlgebra.lift`; show
`N.incl.comp ψ = q` using `FreeLieAlgebra.hom_ext` (both send `of g` to `mk (of g)`), and conclude
that every element of the quotient is in `N`. -/
theorem eq_top_of_lieSubalgebra_of_generators {R B : Type*} [CommRing R] [DecidableEq B]
    (CM : Matrix B B ℤ)
    (N : LieSubalgebra R (FreeLieAlgebra R (CartanMatrix.Generators B) ⧸
      CartanMatrix.Relations.toIdeal R CM))
    (hgen : ∀ g : CartanMatrix.Generators B,
      LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM) (FreeLieAlgebra.of R g) ∈ N) :
    N = ⊤ := by
  let q : FreeLieAlgebra R (CartanMatrix.Generators B) →ₗ⁅R⁆
      (FreeLieAlgebra R (CartanMatrix.Generators B) ⧸
        CartanMatrix.Relations.toIdeal R CM) :=
    { toLinearMap := (LieSubmodule.Quotient.mk' (CartanMatrix.Relations.toIdeal R CM)).toLinearMap
      map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket _ x y }
  have hq : Function.Surjective q :=
    LieSubmodule.Quotient.surjective_mk' (CartanMatrix.Relations.toIdeal R CM)
  let ψ : FreeLieAlgebra R (CartanMatrix.Generators B) →ₗ⁅R⁆ N :=
    FreeLieAlgebra.lift R fun g =>
      ⟨LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal R CM) (FreeLieAlgebra.of R g),
        hgen g⟩
  have hcomp : N.incl.comp ψ = q := by
    apply FreeLieAlgebra.hom_ext
    intro g
    simp only [ψ, q, LieHom.comp_apply, FreeLieAlgebra.lift_of_apply, LieSubalgebra.coe_incl]
    rfl
  have hsurj : Function.Surjective N.incl := by
    intro x
    obtain ⟨y, hy⟩ := hq x
    refine ⟨ψ y, ?_⟩
    have h1 : N.incl (ψ y) = q y := by
      rw [← LieHom.comp_apply, hcomp]
    rw [h1, hy]
  refine le_antisymm le_top ?_
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy]
  exact y.2

end Commons.Algebra.Lie.SerreConstruction