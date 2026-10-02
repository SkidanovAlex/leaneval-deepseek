import Mathlib
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Thom.stepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `B` (Route 1): the boundary of a pushed-forward generator is carried by the sphere part

`Work.Whitney.exists_ballChain` (notes `NOTES_tcmRankOneSusp.md` §6/§7) asks for a chain `B` of
`Y × MBall n` whose boundary lies in the sphere part `DiscB Y n`.  Route 1 takes `B` to be the
push-forward of the top generator of `Δⁿ` along a map of pairs
`f : (Δⁿ, ∂Δⁿ) → (Y × MBall n, DiscB Y n)`.

This file proves the **combinatorial half** of that, with no topology at all: if every face of `σ`
is pushed by `f` into `DiscB`, then the boundary of `f_* (gen σ)` is carried by `DiscB`.  The
remaining (topological) half — producing such an `f` — is a separate lemma; for `n = 1` the affine
map `t ↦ 2t - 1` already works, and for `n ≥ 2` one needs a map of pairs `Δⁿ → Dⁿ` (an affine one
is impossible: a face of an affine simplex is a straight segment, which cannot lie on `S^{n-1}`).

The proof is the template of `RankOne/Faces.lean`: push the generator, differentiate on the target
(`Work.Cohomology.pushChain_gen`, `Work.Cohomology.d_gen`), and observe that each summand is a
generator of a pushed face, small by hypothesis (`Work.Cohomology.isSmallChain_gen`).

The hypothesis `hfac` is the "faces of the pushed simplex" form of the map-of-pairs condition
`f(∂Δⁿ) ⊆ DiscB Y (m+1)`: the two are related by the simplicial naturality of
`TopCat.toSSet.map f` (`φ.app (op ⦋m⦌) (X.δ i σ) = Y.δ i (φ.app (op ⦋m+1⦌) σ)`), which is the
only bookkeeping left to the lemma that *produces* `f`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Cohomology
open Work.Thom

noncomputable section

/-- **The face computation of Route 1.**  For a map `f : Δ^{m+1} → Y × MBall (m+1)` all of whose
faces of `σ` land in `DiscB Y (m+1)`, the boundary of the pushed-forward generator
`f_* (gen (Δ^{m+1}) (m+1) σ)` is a chain carried by `DiscB Y (m+1)`. -/
theorem ballChain_boundary_isSmall {Y : Type} [TopologicalSpace Y] (m : ℕ)
    (f : (Delta (m + 1) : TopCat) ⟶ TopCat.of (Y × MBall (m + 1)))
    (σ : Simplex (Delta (m + 1)) (m + 1))
    (hfac : ∀ i : Fin (m + 2),
      IsSmall (DiscB Y (m + 1)) ∅
        (((TopCat.toSSet.obj (TopCat.of (Y × MBall (m + 1)))).δ i)
          ((TopCat.toSSet.map f).app (Opposite.op ⦋m + 1⦌) σ))) :
    IsSmallChain (DiscB Y (m + 1)) ∅
      (((singularChains ℤ (TopCat.of (Y × MBall (m + 1)))).d (m + 1) m).hom
        (pushChain (Delta (m + 1)) (TopCat.of (Y × MBall (m + 1))) f (m + 1)
          (gen (Delta (m + 1)) (m + 1) σ))) := by
  -- push the generator first, then differentiate on the target
  rw [pushChain_gen (Delta (m + 1)) (TopCat.of (Y × MBall (m + 1))) f (m + 1) σ]
  rw [d_gen (TopCat.of (Y × MBall (m + 1))) m
    ((TopCat.toSSet.map f).app (Opposite.op ⦋m + 1⦌) σ)]
  refine IsSmallChain.sum _ _ (fun i _ => ?_)
  refine IsSmallChain.smul _ ?_
  exact isSmallChain_gen (hfac i)

end

end Work.Whitney
