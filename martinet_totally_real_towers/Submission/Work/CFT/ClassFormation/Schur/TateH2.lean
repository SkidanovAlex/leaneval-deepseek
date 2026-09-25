import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# `H_2(G, ℤ) ≅ Ĥ^{-3}(G, ℤ)`

For a finite group `G`, Mathlib's `TateCohomology.isoGroupHomology` identifies the `m`-th Tate
cohomology with the `n`-th group homology whenever `m = -(n+1)`.  With `n = 2`, `m = -3`, this is
the identification `H_2(G, ℤ) ≅ Ĥ^{-3}(G, ℤ)` used by the Tate–Nakayama theorem: cup product with
the fundamental class turns `Ĥ^{-3}(G, ℤ) ≅ H_2(G, ℤ)` into `Ĥ^{-1}(G, A)`.
-/

namespace Work.CFT.ClassFormation.Schur

open Work.CFT.ClassFormation

/-- The `ℤ`-linear isomorphism `H_2(G, ℤ) ≅ Ĥ^{-3}(G, ℤ)` for a finite group `G`, obtained from
Mathlib's identification of the `-(n+1)`-th Tate cohomology with the `n`-th group homology. -/
noncomputable def HnZ_two_iso_tate (G : Type) [Group G] [Fintype G] :
    (HnZ G 2 : Type) ≃ₗ[ℤ] (tateCohomology (Rep.trivial ℤ G ℤ) (-3) : Type) :=
  CategoryTheory.Iso.toLinearEquiv <|
    ((TateCohomology.isoGroupHomology (-3) 2 (by norm_num) :
        tateCohomologyFunctor (-3) ≅ groupHomology.functor ℤ G 2)).app
      (Rep.trivial ℤ G ℤ) |>.symm

/-- The composite `H_2(G,ℤ) ≅ Ĥ^{-3}(G,ℤ)` with the `AddEquiv` shadow, for callers who only
need the additive isomorphism. -/
noncomputable def HnZ_two_addEquiv_tate (G : Type) [Group G] [Fintype G] :
    (HnZ G 2 : Type) ≃+ (tateCohomology (Rep.trivial ℤ G ℤ) (-3) : Type) :=
  (HnZ_two_iso_tate G).toAddEquiv

end Work.CFT.ClassFormation.Schur
