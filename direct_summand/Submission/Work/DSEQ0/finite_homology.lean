import Mathlib

/-!
# Finiteness of the homology of a cochain complex of finitely generated modules

Over a Noetherian ring `R`, the homology of a cochain complex of finitely generated `R`-modules
is finitely generated in every degree.  The point is that `H^i(C)` is the quotient of the
`i`-cycles of `C` (the kernel of `C.d i (i+1)`, a submodule of the finitely generated module
`C.X i`) by the `i`-boundaries (the image of `C.d (i-1) i`): a submodule of a finitely generated
module over a Noetherian ring is finitely generated, and a quotient of a finitely generated
module is finitely generated.
-/

open CategoryTheory

namespace Work.DSEQ0

universe u

/-- A short complex of `R`-modules over a Noetherian ring `R` whose middle term is finitely
generated has finitely generated homology: `S.homology` is the quotient of the kernel of `S.g`
by the image of `S.f`. -/
theorem shortComplex_finite_homology {R : Type u} [CommRing R] [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R ↥S.X₂] :
    Module.Finite R ↥S.homology := by
  -- The kernel of `S.g` is a submodule of the finitely generated module `S.X₂`, hence finitely
  -- generated, and so is its quotient by the image of `S.f`.
  have hK : Module.Finite R ↥(LinearMap.ker S.g.hom) := inferInstance
  have hH : Module.Finite R ↥S.moduleCatLeftHomologyData.H := by
    change Module.Finite R ↥(ModuleCat.of R (LinearMap.ker S.g.hom ⧸ S.moduleCatToCycles.range))
    infer_instance
  -- `S.homology` is the left homology of `S`, i.e. isomorphic to the explicit quotient above.
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

theorem finite_homology {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) [∀ i : ℤ, Module.Finite R ↥(C.X i)] (i : ℤ) :
    Module.Finite R ↥(C.homology i) := by
  -- The homology in degree `i` of `C` is the homology of the short complex
  -- `C.X (i-1) ⟶ C.X i ⟶ C.X (i+1)`, whose middle term is the finitely generated `C.X i`.
  have : Module.Finite R ↥((C.sc i).X₂) :=
    (inferInstance : Module.Finite R ↥(C.X i))
  exact shortComplex_finite_homology (S := C.sc i)

end Work.DSEQ0
