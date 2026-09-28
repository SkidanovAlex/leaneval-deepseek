import Mathlib
import Submission.Work.SSS.HomologySigmaAux
import Submission.Work.SSS.coprodComplex_iso
import Submission.Work.SSS.coprodShortComplex_homology

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

/-- **The homology of a coproduct of chain complexes of `ℤ`-modules is the coproduct of the
homologies.**  This is the exactness of coproducts in `ModuleCat ℤ` (the category of abelian groups
is AB5): the homology functor `H_n` commutes with arbitrary coproducts of chain complexes.

Used in the assembly of `Work.SSS.serreE1` to pass from the Eilenberg–Zilber decomposition
`grF ξ.F d ≅ ∐_σ piece_σ` (`Work.SSS.serreE1Graded`) to the degreewise description
`E¹_{d,t} = H_{d+t}(grF ξ.F d) ≅ ∐_σ H_{d+t}(piece_σ)`.

No finiteness or smallness hypothesis on the index type `ι` is needed.  Mathlib has no such result
and no `PreservesColimits` instance for `HomologicalComplex.homologyFunctor`, so this is a genuine
(albeit elementary) proof: coproducts of complexes are degreewise
(`HomologicalComplexLimits.lean`), coproducts in `ModuleCat ℤ` are exact, hence kernels and
cokernels distribute over them.

Do NOT use `sorry`, `axiom` or `admit`. -/
theorem homology_sigma {ι : Type} (F : ι → ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Nonempty ((∐ F).homology n ≅ ∐ (fun i => (F i).homology n)) := by
  obtain ⟨e⟩ := coprodComplex_iso F
  obtain ⟨e'⟩ := coprodShortComplex_homology (fun i => (F i).sc n)
  exact ⟨(HomologicalComplex.homologyMapIso e n).trans e'⟩

end Work.SSS
