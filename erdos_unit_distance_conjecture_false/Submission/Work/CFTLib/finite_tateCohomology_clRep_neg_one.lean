import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient

/-!
# Finiteness of `Ĥ⁻¹(Gal(K/F), Cl(𝓞 K))`

For a finite Galois extension `K/F` of number fields, `G = Gal(K/F)` and `M = Cl(𝓞 K)` with its
canonical `G`-action (`Work.CFTLib.clRep F K`), the `(-1)`-st Tate cohomology `Ĥ⁻¹(G, M)` is
finite.

`Cl(𝓞 K)` is finite (the class group of a number field is finite), hence so is the coefficient
module of `clRep F K`.  By `Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient`, the group
`Ĥ⁻¹(G, M)` is the quotient `ker N_M ⧸ I_G M` of the kernel of the norm, so it is a quotient of a
subset of the finite set `M`; being finite as a type it is also finitely generated over `ℤ`.

## Main result

* `Work.CFTLib.finite_tateCohomology_clRep_neg_one`
-/

set_option linter.style.haveILetI false

open NumberField CategoryTheory

namespace Work.CFTLib

/-- `Ĥ⁻¹(Gal(K/F), Cl(𝓞 K))` is finite (and hence a finitely generated `ℤ`-module). -/
theorem finite_tateCohomology_clRep_neg_one {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] :
    Finite ↥(tateCohomology (Work.CFTLib.clRep F K) (-1)) ∧
      Module.Finite ℤ ↥(tateCohomology (Work.CFTLib.clRep F K) (-1)) := by
  -- the class group of `K`, and so the coefficient module of `clRep F K`, is finite
  haveI hV : Finite ↥(Work.CFTLib.clRep F K) :=
    (inferInstance : Finite (Additive (ClassGroup (𝓞 K))))
  -- `Ĥ⁻¹(G, Cl_K) ≅ ker N ⧸ I_G Cl_K` is a quotient of the finite group `ker N`
  haveI hQ : Finite (Work.CFT.Ledger.Hm1Quotient (Work.CFTLib.clRep F K)) := inferInstance
  obtain ⟨e⟩ :=
    Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient (Work.CFTLib.clRep F K)
  haveI hfin : Finite ↥(tateCohomology (Work.CFTLib.clRep F K) (-1)) :=
    Finite.of_equiv _ e.toEquiv.symm
  exact ⟨hfin, Module.Finite.of_finite⟩

end Work.CFTLib
