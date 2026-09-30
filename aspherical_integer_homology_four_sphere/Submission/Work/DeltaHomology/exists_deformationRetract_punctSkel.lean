import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.PunctSkelContinuous
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.barycenter_not_mem_skelSet_of_lt
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial unitInterval

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K : DeltaCx} {X : TopCat}

/-- The `k`-skeleton, viewed as a subset of the collar of the `(k+1)`-skeleton. -/
def skelPiece (R : DeltaRealization K X) (k : ℕ) : Set ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) :=
  {z | (z : X) ∈ R.toDeltaSimplexMap.skelSet k}

theorem mem_skelPiece_iff (R : DeltaRealization K X) (k : ℕ)
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    z ∈ skelPiece R k ↔ (z : X) ∈ R.toDeltaSimplexMap.skelSet k := Iff.rfl

/-- The retraction of the collar onto the `k`-skeleton: the time-`1` value of the radial
homotopy `homotopyFun R k`. -/
def retractFun (R : DeltaRealization K X) (k : ℕ) :
    ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) → ↥(skelPiece R k) :=
  fun z => ⟨⟨homotopyVal R k (1, z), homotopyVal_mem R k (1, z)⟩,
    homotopyVal_one_mem_skelSet R k z⟩

theorem retractFun_val (R : DeltaRealization K X) (k : ℕ)
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    ((retractFun R k z : ↥(skelPiece R k)) : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) =
      homotopyFun R k (1, z) := rfl

theorem continuous_retractFun (R : DeltaRealization K X) (k : ℕ) :
    Continuous (retractFun R k) := by
  have h1 : Continuous (fun z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) =>
      homotopyFun R k (1, z)) :=
    (continuous_homotopyFun R k).comp (by fun_prop)
  have h2 : Continuous (fun z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) =>
      (⟨homotopyVal R k (1, z), homotopyVal_mem R k (1, z)⟩ :
        ↥(R.toDeltaSimplexMap.punctSkel (k + 1)))) :=
    Continuous.subtype_mk (continuous_subtype_val.comp h1) (fun z => homotopyVal_mem R k (1, z))
  exact Continuous.subtype_mk h2 (fun z => homotopyVal_one_mem_skelSet R k z)

/-- **The collar of the `k`-skeleton in the `(k+1)`-skeleton.**  The `(k+1)`-skeleton
with the barycentres of its `(k+1)`-simplices removed,
`R.toDeltaSimplexMap.punctSkel (k+1) = X^{k+1} ∖ {barycentres}`, is an open
neighbourhood of the `k`-skeleton inside `X^{k+1}` which deformation retracts onto
it: the retraction pushes each point of an open `(k+1)`-cell radially away from the
barycentre of that cell onto the boundary of the cell (the single-simplex case is
the proved `exists_collar_deformationRetract`), and leaves the `k`-skeleton
pointwise fixed.

Route: every point of `punctSkel (k+1)` lies in exactly one closed `(k+1)`-simplex
of `K` (or in the `k`-skeleton, where the retraction is the identity); in the first
case it is `χ.cls (k+1) τ y` for an interior point `y ≠ barycentre` of `Δ^{k+1}`
and the retraction acts on `y` by the radial map of
`exists_collar_deformationRetract`.  Continuity of the resulting map
`punctSkel (k+1) → punctSkel (k+1)` uses the weak topology of the realization.

This is the geometric input for the computation of `H_n(X^{k+1}, X^k)` (free of
rank `K.card (k+1)` in degree `k+1`, zero otherwise) via the long exact sequence of
the pair, the five-lemma, and `Work.Homology.relHomology_excision` applied with
`Z = X^k` and `A = punctSkel (k+1)` (legitimate because `closure X^k = X^k` is
contained in the interior of `punctSkel (k+1)`). -/
theorem exists_deformationRetract_punctSkel {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ) :
    Nonempty (DeformationRetract (TopCat.of (R.toDeltaSimplexMap.punctSkel (k + 1)))
      {x | (x : X) ∈ R.toDeltaSimplexMap.skelSet k}) := by
  refine ⟨{ retract := TopCat.ofHom ⟨retractFun R k, continuous_retractFun R k⟩,
            retract_incl := ?_, homotopy := ?_ }⟩
  · ext z
    show ((homotopyFun R k (1, (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))))) : X) = (z : X)
    exact congrArg Subtype.val (homotopyFun_fixes R k 1 z.2)
  · refine ⟨ContinuousMap.Homotopy.symm ?_⟩
    exact ContinuousMap.Homotopy.mk ⟨homotopyFun R k, continuous_homotopyFun R k⟩
      (fun z => homotopyFun_zero R k z)
      (fun z => (retractFun_val R k z).symm)

end

end Work.DeltaHomology
