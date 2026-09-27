import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.exists_iter_small
import Submission.Work.Cohomology.exists_small_homotopy
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.mono_homologyMap_of_cycles
import Submission.Work.Cohomology.epi_homologyMap_of_cycles

/-!
# The small-simplices theorem

Let `X` be a topological space and `U, V ⊆ X` subsets covering `X`.  A singular simplex is *small*
if its image lies in `U` or in `V`, and the small chains `C^{U,V}_*(X)` are the chains spanned by
the small simplices (`Submission/Work/Cohomology/SmallChains.lean`).  **The small-simplices
theorem** — the classical input to the Mayer–Vietoris sequence — says that the inclusion
`smallToSing U V : C^{U,V}_*(X) ⟶ C_*(X)` induces an isomorphism on homology.

The proof has two halves, both proved in `Submission/Work/Cohomology/SmallChainsIsoAux.lean` from
the metric refinement properties of the barycentric subdivision:

* `exists_smallToSing_add_d` (surjectivity): every cycle `z` of `C_*(X)` satisfies
  `i c = z + ∂b` for a small cycle `c` and some chain `b`; one takes `c` to be a sufficiently
  high subdivision of `z`, which is small by `exists_iter_small_chain`, and uses the chain
  homotopy `Sd^N ~ id` (`exists_small_homotopy`) to compare the classes;
* `exists_d_eq_of_smallToSing_eq` (injectivity): a small cycle `z` with `i z = ∂a` is itself a
  boundary; here one subdivides `a` until it is small, and the homotopy formula turns the
  identity `∂ Sd^N a = Sd^N ∂ a = Sd^N (i z)` into an explicit expression for `z` as a boundary.

The passage from these elementwise statements to the statement on homology (and the harmless
"up to refinement" bookkeeping over an arbitrary test object) is
`mono_homologyMap_of_cycles` and `epi_homologyMap_of_cycles`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The small-simplices theorem.**  For an open cover `X = U ∪ V`, the inclusion of the small
chains into the singular chains of `X` induces an isomorphism on homology. -/
theorem smallChains_homology_iso {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (smallToSing U V) n) := by
  haveI hmono : CategoryTheory.Mono (HomologicalComplex.homologyMap (smallToSing U V) n) :=
    mono_homologyMap_of_cycles (smallToSing U V) n (fun z hz a ha =>
      exists_d_eq_of_smallToSing_eq U V hU hV hcov n hz ha)
  haveI hepi : CategoryTheory.Epi (HomologicalComplex.homologyMap (smallToSing U V) n) :=
    epi_homologyMap_of_cycles (smallToSing U V) n (fun z hz =>
      exists_smallToSing_add_d U V hU hV hcov n hz)
  exact (ConcreteCategory.isIso_iff_bijective
      (HomologicalComplex.homologyMap (smallToSing U V) n)).mpr
    ⟨(ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap (smallToSing U V) n)).mp hmono,
      (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap (smallToSing U V) n)).mp hepi⟩

end

end Work.Cohomology
