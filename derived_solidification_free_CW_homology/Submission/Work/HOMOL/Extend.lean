import Mathlib
import ChallengeDeps
import Submission.Work.HOMOL.Basic

/-!
# AREA HOMOL — homology is invariant under extension by zero

`ComplexShape.embeddingDownNat : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ)` sends the
chain degree `n` to the cohomological degree `-n`. Extending a chain complex of light condensed
abelian groups by zero along this embedding does not change homology, it only shifts the index:
this is `HomologicalComplex.extendHomologyIso`. Here we package that result as a natural
isomorphism of functors, using `HomologicalComplex.extendHomologyIso_hom_naturality`; this is the
first ingredient of `H^{-n}(Q C(X)) ≅ discrete(H_n^{sing}(X))` (`REFS/05 §4`).

We prove the result for an arbitrary embedding of complex shapes (`extendFunctorHomologyIsoOfEmbedding`),
which is the form in which it is useful elsewhere, and specialise it to `embeddingDownNat`.
-/

noncomputable section

open CategoryTheory Limits LightProfinite LightCondensed

open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.HOMOL

/-- **Extension by zero preserves homology, naturally (general embedding).**
For an embedding of complex shapes `e : c.Embedding c'`, the extended complex `K.extend e` has the
same homology in degree `e.f j` as `K` has in degree `j`, naturally in the complex `K`. -/
noncomputable def extendFunctorHomologyIsoOfEmbedding {C : Type*} [Category* C] [Abelian C]
    {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι') (e : c.Embedding c') (j : ι) :
    (e.extendFunctor C) ⋙ HomologicalComplex.homologyFunctor C c' (e.f j) ≅
      HomologicalComplex.homologyFunctor C c j :=
  NatIso.ofComponents
    (fun K => K.extendHomologyIso e rfl)
    (fun {K L} φ => by
      dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map,
        ComplexShape.Embedding.extendFunctor_map]
      exact HomologicalComplex.extendHomologyIso_hom_naturality (hj' := rfl) φ)

/-- **Extension by zero preserves homology, naturally.** The functor
`ComplexShape.embeddingDownNat.extendFunctor LightCondAb` does not change homology, it only
shifts the index from `n : ℕ` to `-(n : ℤ)`. -/
noncomputable def extendFunctorHomologyIso (n : ℕ) :
    (ComplexShape.embeddingDownNat.extendFunctor LightCondAb) ⋙
        HomologicalComplex.homologyFunctor LightCondAb (ComplexShape.up ℤ) (-(n : ℤ)) ≅
      HomologicalComplex.homologyFunctor LightCondAb (ComplexShape.down ℕ) n :=
  extendFunctorHomologyIsoOfEmbedding (ComplexShape.down ℕ) (ComplexShape.up ℤ)
    ComplexShape.embeddingDownNat n

/-- Pointwise form of `extendFunctorHomologyIso`. -/
noncomputable def extendHomologyIso (K : HomologicalComplex LightCondAb (ComplexShape.down ℕ))
    (n : ℕ) :
    (K.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅ K.homology n :=
  (extendFunctorHomologyIso n).app K

end Work.HOMOL
