import Mathlib
import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.nondegenerate_midForm_of_good
import Submission.Work.ThomBordism.sigmaInterForm
import Submission.Work.Bordism.sigma_disj
import Submission.Work.Bordism.Invariance
import Submission.Work.ThomBordism.nondegenerateOfIso
import Submission.Work.ThomBordism.nondegenerateSigmaSum
import Submission.Work.ThomBordism.man8MidFormNondegenerate

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Middle-degree Poincaré duality for the boundary of a null-bordism

For a `NullBordismFamily` `W` (a compact oriented smooth `9`-manifold with boundary whose boundary
is identified with the closed oriented `8`-manifolds `F i`, with relative fundamental class `w`),
the closed oriented `8`-manifold `∂W = (bdryClosed W)` has **non-degenerate** middle intersection
form:

`Work.ThomBordism.bdryMidFormNondegenerate`.

This is a theorem of topology — the boundary of a compact oriented manifold is a closed oriented
manifold, so its middle intersection form is non-degenerate by Poincaré duality — and it is one of
the two Poincaré-duality inputs of middle-degree Lefschetz duality for the pair `(W, ∂W)`
(`Work.ThomBordism.boundaryHalfDimension`).

## The proof, and why it goes through the disjoint union of the pieces

The calculus of the boundary chart of `W` is only available in the workspace for `C^∞` manifolds
(`Work.Surgery.bnd_isManifold`), while the model `NullBordismFamily` asks only for a `C¹` bounding
manifold; so rather than build the `ChartedSpace` structure of `∂W` and apply the closed Poincaré
duality theorem `Work.ThomBordism.nondegenerate_midForm_of_good` to it, the proof *transports* the
result from the pieces, where the closed Poincaré duality theorem **is** available:

* `Work.ThomBordism.man8MidFormNondegenerate` — each piece `F i` has non-degenerate middle form
  (this is `Good` for the piece, from `Man8.c_fund`, plus finiteness of its homology);
* `Work.ThomBordism.nondegenerateSigmaSum` — the disjoint union `Z = Σ i, (F i).pt` against the sum
  `c_Z = ∑ i (incl i)_* (F i).c` has non-degenerate middle form (the form is the orthogonal sum of
  the forms of the pieces, and the pullbacks along the inclusions present `H⁴(Z;ℚ)` as the product
  of the `H⁴(F i;ℚ)`);
* `W.bdry : ∂W ≃ₜ Z` is a homeomorphism and `W.hw` computes the push-forward of the boundary class:
  `(W.bdry)_* ∂w = c_Z`.  Non-degeneracy of the middle form transports along a homeomorphism
  (`Work.ThomBordism.nondegenerateOfIso`, from the naturality of the intersection form under
  pullback and the invariance of non-degeneracy under a linear equivalence).
-/

set_option maxHeartbeats 400000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff TensorProduct

namespace Work.ThomBordism

noncomputable section

theorem bdryMidFormNondegenerate {ι : Type} [Fintype ι] (F : ι → Work.ThomBordism.Man8)
    (W : Work.ThomBordism.NullBordismFamily ι F) :
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (Work.ThomBordism.bdryClosed W)) := by
  classical
  -- The disjoint union of the pieces and its fundamental class (the sum of the pieces' classes).
  let α : ι → TopCat := fun i => (F i).X
  let Z : TopCat := TopCat.of (Σ i, α i)
  let cZ : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj Z)).homology 8 :=
    ∑ i, HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (α i) Z (TopCat.sigmaι α i)) 8 ((F i).c)
  -- **(1)** The disjoint union has non-degenerate middle intersection form.
  have hZ : Work.Bordism.Nondegenerate (Work.SignatureBordism.quadOfBilin
      (Work.SignatureBordism.ratInterForm 4 (TopCat.toSSet.obj Z) cZ)) :=
    nondegenerateSigmaSum (k := 4) α (fun i => (F i).c)
      (fun i => man8MidFormNondegenerate (F i))
  -- The homeomorphism between the boundary and the disjoint union of the pieces.
  let e : (bdryClosed W).X ≅ Z := TopCat.isoOfHomeo W.bdry
  -- **(2)** The push-forward of the boundary class is the class of the disjoint union.
  have hc : HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (bdryClosed W).X Z e.hom) 8 (bdryClosed W).c = cZ := by
    -- the inclusion of a piece into the boundary
    let gf : (i : ι) → (α i ⟶ (bdryClosed W).X) :=
      fun i => TopCat.ofHom ⟨fun y => W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt),
        W.bdry.continuous_invFun.comp continuous_sigmaMk⟩
    -- ... which, followed by the homeomorphism `W.bdry`, is the inclusion into the disjoint union
    have hmor : ∀ i, CategoryTheory.CategoryStruct.comp (gf i) (e.hom) = TopCat.sigmaι α i := by
      intro i
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro y
      show e.hom (W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt)) = (TopCat.sigmaι α i) y
      show W.bdry (W.bdry.symm (⟨i, y⟩ : Σ i, (F i).pt)) = (⟨i, y⟩ : ↑Z)
      simp
    -- the boundary class is the sum of the pieces' classes (`W.hw`) ...
    have hdelta : (bdryClosed W).c = ∑ i, HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (α i) (bdryClosed W).X (gf i)) 8 ((F i).c) := W.hw
    -- ... and pushing it forward along `W.bdry` gives the class of the disjoint union.
    rw [hdelta, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (homologyMap_chainMap_comp_apply (gf i) e.hom 8 ((F i).c)).trans
      (by rw [hmor i])
  -- **(3)** Transport non-degeneracy along the homeomorphism `W.bdry`.
  exact nondegenerateOfIso (k := 4) (bdryClosed W).X Z e (bdryClosed W).c cZ hc hZ

end

end Work.ThomBordism
