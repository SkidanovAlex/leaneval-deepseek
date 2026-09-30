import Mathlib
import Submission.Work.Cohomology.Mesh
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.Sd_toChain_pushLC
import Submission.Work.Cohomology.SubdivisionHomotopyData

/-!
# The `N`-fold subdivision of a singular simplex

`Work.Cohomology.sdChainMapIter X N : C_*(X) ⟶ C_*(X)` is the `N`-fold iterate of the barycentric
subdivision chain map (`Submission/Work/Cohomology/SdIter.lean`).  This file computes it on a
generator: on a singular `n`-simplex `σ` of `X` it is the push-forward along `σ` of the `N`-fold
subdivided identity simplex of `Δⁿ` (`Work.Cohomology.sdIterLC n N`),

`(sdChainMapIter X N).f n (gen X n σ) = pushChain (Δⁿ) X (sdMap n σ) n (toChain n n (sdIterLC n N))`.

The proof is the naturality of `Sd` (`Sd_natural`) together with the affine computation
`Sd_toChain_pushLC`, iterated.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The degree-`n` component of the `N`-fold subdivision chain map, as a linear map, is the
`N`-th iterate of `Sd X n`. -/
lemma sdChainMapIter_f_hom (X : TopCat) (n N : ℕ) :
    ((sdChainMapIter X N).f n).hom = (Sd X n)^[N] := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sdChainMapIter_succ, HomologicalComplex.comp_f, ModuleCat.hom_comp]
    funext c
    show ((sdChainMap X).f n).hom (((sdChainMapIter X N).f n).hom c) = (Sd X n)^[N + 1] c
    rw [ih, Function.iterate_succ_apply']
    rfl

/-- The `N`-fold subdivision of a singular simplex is the push-forward along it of the `N`-fold
subdivision of the identity simplex. -/
lemma Sd_iter_gen (X : TopCat) (n N : ℕ) (σ : Simplex X n) :
    (Sd X n)^[N] (gen X n σ)
      = pushChain (Delta n) X (sdMap n σ) n (toChain n n (sdIterLC n N)) := by
  induction N with
  | zero =>
    show gen X n σ = pushChain (Delta n) X (sdMap n σ) n (toChain n n (sdIterLC n 0))
    rw [show sdIterLC n 0 = iotaLC n from rfl]
    exact (push_id_simplex X n σ).symm
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Sd_natural, Sd_toChain_pushLC]
    rfl

theorem sdChainMapIter_gen (X : TopCat) (n N : ℕ) (σ : Simplex X n) :
    (sdChainMapIter X N).f n (gen X n σ)
      = pushChain (Delta n) X (sdMap n σ) n (toChain n n (sdIterLC n N)) := by
  have h := Sd_iter_gen X n N σ
  change ((sdChainMapIter X N).f n).hom (gen X n σ)
      = pushChain (Delta n) X (sdMap n σ) n (toChain n n (sdIterLC n N))
  rw [sdChainMapIter_f_hom X n N]
  exact h

end

end Work.Cohomology
