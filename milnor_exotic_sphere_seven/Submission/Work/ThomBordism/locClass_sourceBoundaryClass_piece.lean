import Mathlib
import Submission.Work.ThomBordism.sourceCoord
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.ThomBordism.Transversality.OrientBridge.isFundClass_sum_push

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-- **The local class of a pushed class along an injective map.**

For an injective continuous map `f : X → Y`, a point `x : X` and a class `c ∈ H_n(X;ℤ)`, the local
class at `f x` of the pushforward `f_* c` is the image of the local class of `c` at `x` under the
map of pairs `(X, X∖{x}) → (Y, Y∖{f x})` — i.e. the map `RelHmapOf n f {x} {f x} …`.  This is the
naturality of the local classes (`Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair`)
combined with the definition of `RelHmapOf`. -/
theorem relHmapOf_locClass_singleton {X Y : TopCat} {n : ℕ} (f : X ⟶ Y) (x : X) (y : Y)
    (hxy : f x = y) (hinj : Function.Injective f)
    (c : (Work.Cohomology.singularChains ℤ X).homology n) :
    Work.PTGeometric.HOF.RelHmapOf n f {x} {y} (fun z hz hzy => hz (hinj (hzy.trans hxy.symm)))
        (Work.Orient.locClass X n c x)
      = Work.Orient.locClass Y n
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n c) y := by
  rw [Work.Orient.locClass_eq_relClass, Work.Orient.locClass_eq_relClass]
  rw [Work.PTGeometric.HOF.RelHmapOf_eq]
  exact Work.ThomBordism.Transversality.OrientBridge.relLocClass_map_pair (M := X) (M' := Y)
    (n := n) f (K := {x}) (K' := {y}) _ _ c

theorem locClass_sourceBoundaryClass_piece {k mU m : ℕ} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (D0 : Work.PTGeometric.RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    (a : Fin m × ι) (y : (Fam a.2).pt) :
    Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)) 8
        (Work.ThomBordism.sourceBoundaryClass D0) (Work.ThomBordism.piecePush D0 a y)
      = Work.PTGeometric.HOF.RelHmapOf 8 (TopCat.ofHom (Work.ThomBordism.piecePush D0 a))
          ({y} : Set (Fam a.2).pt)
          ({Work.ThomBordism.piecePush D0 a y} : Set ↥(Work.ThomBordism.sourceLevelBdry D0))
          (fun z hz hzy => hz (by
            have h : (D0.hend.symm ⟨a, z⟩ : ↥(D0.S ∩ {x : D0.M | D0.v x = 0})) =
                D0.hend.symm ⟨a, y⟩ := by
              apply Subtype.ext
              exact congrArg (fun t : ↥(Work.ThomBordism.sourceLevelBdry D0) =>
                (t.1.1 : D0.M)) hzy
            have h2 := D0.hend.symm.injective h
            exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2))
          (Work.Orient.locClass (Fam a.2).X 8 (Fam a.2).c y) := by
  classical
  -- the piece push is injective
  have hinj : Function.Injective (fun z : (Fam a.2).pt => Work.ThomBordism.piecePush D0 a z) := by
    intro z z' hzz'
    have h : (D0.hend.symm ⟨a, z⟩ : ↥(D0.S ∩ {x : D0.M | D0.v x = 0})) =
        D0.hend.symm ⟨a, z'⟩ := by
      apply Subtype.ext
      exact congrArg (fun t : ↥(Work.ThomBordism.sourceLevelBdry D0) => (t.1.1 : D0.M)) hzz'
    exact eq_of_heq (Sigma.mk.inj_iff.mp (D0.hend.symm.injective h)).2
  -- the local class of the sum of the pushed classes is the sum of the local classes
  have hsum : Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)) 8
      (Work.ThomBordism.sourceBoundaryClass D0) (Work.ThomBordism.piecePush D0 a y)
      = ∑ j : Fin m × ι, Work.Orient.locClass
          (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)) 8
          (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Fam j.2).X
            (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
            (TopCat.ofHom (Work.ThomBordism.piecePush D0 j))) 8 (Fam j.2).c)
          (Work.ThomBordism.piecePush D0 a y) := by
    rw [Work.ThomBordism.sourceBoundaryClass]
    rw [Work.ThomBordism.Transversality.OrientBridge.locClass_sum]
  -- all the summands other than the `a`-th vanish
  have hother : ∀ j : Fin m × ι, j ≠ a →
      Work.Orient.locClass (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)) 8
        (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (Fam j.2).X
          (TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0))
          (TopCat.ofHom (Work.ThomBordism.piecePush D0 j))) 8 (Fam j.2).c)
        (Work.ThomBordism.piecePush D0 a y) = 0 := by
    intro j hj
    refine Work.ThomBordism.localClassAt_homologyMap_eq_zero_of_ne
      (TopCat.ofHom (Work.ThomBordism.piecePush D0 j)) (Work.ThomBordism.piecePush D0 a y)
      (fun z hz => ?_) 8 (Fam j.2).c
    have h : (D0.hend.symm ⟨j, z⟩ : ↥(D0.S ∩ {x : D0.M | D0.v x = 0})) =
        D0.hend.symm ⟨a, y⟩ := by
      apply Subtype.ext
      exact congrArg (fun t : ↥(Work.ThomBordism.sourceLevelBdry D0) => (t.1.1 : D0.M)) hz
    exact hj (Sigma.mk.inj_iff.mp (D0.hend.symm.injective h)).1
  rw [hsum]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (fun j _ hj => hother j hj)]
  -- the surviving summand is the pushforward of the local class of the piece
  exact (relHmapOf_locClass_singleton (X := (Fam a.2).X)
    (Y := TopCat.of ↥(Work.ThomBordism.sourceLevelBdry D0)) (n := 8)
    (TopCat.ofHom (Work.ThomBordism.piecePush D0 a)) y (Work.ThomBordism.piecePush D0 a y)
    rfl hinj (Fam a.2).c).symm

end

end Work.ThomBordism
