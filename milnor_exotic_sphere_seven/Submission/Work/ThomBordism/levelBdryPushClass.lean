import Mathlib
import Submission.Work.ThomBordism.sourceBoundaryCoord_assembly
import Submission.Work.ThomBordism.locClass_sourceBoundaryClass_piece

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the local class of the pieces' boundary class at a collapse-identified point

`Work.ThomBordism.sourceBoundaryClass D0` is the class of the pieces in the homology of the *boundary
part of the level set* of a raw datum `D0`; on the level model's boundary the same class is written as
the sum `∑ i, pushClass e.symm i` of the pieces pushed along the collapse identification `e`
(`Work.ThomBordism.sum_pushClass_eq_sourceBoundaryClass`).  This file proves that its *local class* at
the image `e.symm ⟨a,y⟩` of a piece point is the `RelHmapOf` of the piece's own local fundamental
class along the collapse identification — i.e. the `ῆ`-side localisation of the last mile (step G1 of
`LeadChapter/ASSEMBLY.md`).

Everything is functoriality of the local class; no geometry and no orientation enters.

## Main results

* `Work.ThomBordism.locClass_sum_pushClass_eq_relHmapOf`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- **The local class of the pieces' class at the collapse image of a piece point.**

For a raw datum `D0`, an identification `e` of the boundary part of the level model with the pieces
(whose inverse composed with the `a`-th summand is `piecePush D0 a`, hypothesis `he`), a piece `a` and
a point `y` of it, the local class of `ῆ = ∑ i, pushClass e.symm i` at `e.symm ⟨a, y⟩` is the
`RelHmapOf` of the `a`-th piece's local fundamental class along the collapse identification
`z ↦ e.symm ⟨a, z⟩`. -/
theorem locClass_sum_pushClass_eq_relHmapOf
    (hk : 11 ≤ k) (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (hm : 0 < m)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (D0 : Work.PTGeometric.RawAmbientData (k + G.mU) k (Fin m × ι) (fun a => Fam a.2))
    {hWcl : IsClosed (Work.ThomBordism.sourceLevelSet D0)}
    {L : Work.PTGeometric.LocalLevelData k D0.M (Work.ThomBordism.sourceLevelSet D0)}
    (e : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))
      ≃ₜ (Σ a : Fin m × ι, (Fam a.2).pt))
    (he : ∀ (a : Fin m × ι) (y : (Fam a.2).pt),
        ((e.symm ⟨a, y⟩ : ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))).1 :
            ↥(Work.ThomBordism.sourceLevelSet D0))
          = ((Work.ThomBordism.piecePush D0 a y : ↥(Work.ThomBordism.sourceLevelBdry D0)) :
              ↥(Work.ThomBordism.sourceLevelSet D0)))
    (a : Fin m × ι) (y : (Fam a.2).pt) :
    Work.Orient.locClass (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary
        (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))) 8
      (∑ i : Fin m × ι, Work.ThomBordism.Transversality.OrientBridge.pushClass
        (Fam := fun a : Fin m × ι => Fam a.2) e.symm i)
      (e.symm ⟨a, y⟩)
    = Work.PTGeometric.HOF.RelHmapOf 8
        (TopCat.ofHom ⟨fun z : (Fam a.2).pt => e.symm ⟨a, z⟩,
          e.symm.continuous.comp continuous_sigmaMk⟩)
        ({y} : Set (Fam a.2).pt)
        ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
          (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))
        (fun z hz hzy => hz (by
          have h : (⟨a, z⟩ : Σ b : Fin m × ι, (Fam b.2).pt) = ⟨a, y⟩ :=
            e.symm.injective hzy
          exact eq_of_heq (Sigma.mk.inj_iff.mp h).2))
        (Work.Orient.locClass (Fam a.2).X 8 (Fam a.2).c y) := by
  classical
  -- the piece push is injective
  have hinjPush : Function.Injective
      (⇑(Work.ThomBordism.piecePush D0 a)) := by
    intro z z' hzz'
    have h : (D0.hend.symm ⟨a, z⟩ : ↥(D0.S ∩ {x : D0.M | D0.v x = 0})) =
        D0.hend.symm ⟨a, z'⟩ := by
      apply Subtype.ext
      exact congrArg (fun t : ↥(Work.ThomBordism.sourceLevelBdry D0) => (t.1.1 : D0.M)) hzz'
    exact eq_of_heq (Sigma.mk.inj_iff.mp (D0.hend.symm.injective h)).2
  -- the transfer homeomorphism is injective and its value at a piece push is the collapse image
  have hinjF : Function.Injective (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0) :=
    fun x z h => (Work.ThomBordism.boundaryTransferHomeo (hWcl := hWcl) (L := L) D0).symm.injective h
  have hxy : Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0 (Work.ThomBordism.piecePush D0 a y)
      = e.symm ⟨a, y⟩ := Subtype.ext (he a y).symm
  rw [Work.ThomBordism.sum_pushClass_eq_sourceBoundaryClass hk G m hm hpow D0 e he]
  rw [← Work.ThomBordism.relHmapOf_locClass_singleton
    (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0) (Work.ThomBordism.piecePush D0 a y)
    (e.symm ⟨a, y⟩) hxy hinjF (Work.ThomBordism.sourceBoundaryClass D0)]
  rw [Work.ThomBordism.locClass_sourceBoundaryClass_piece D0 a y]
  have hmorph : (TopCat.ofHom (Work.ThomBordism.piecePush D0 a)) ≫
      (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0)
      = TopCat.ofHom ⟨fun z : (Fam a.2).pt => e.symm ⟨a, z⟩,
          e.symm.continuous.comp continuous_sigmaMk⟩ := by
    ext z : 1
    exact Subtype.ext (he a z).symm
  have hR := Work.PTGeometric.HOF.RelHmapOf_congr (n := 8)
    (K := ({y} : Set (Fam a.2).pt))
    (K' := ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))))
    hmorph
    (fun (z : (Fam a.2).pt) (hz : z ∉ ({y} : Set (Fam a.2).pt))
        (hzy : (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0)
            ((Work.ThomBordism.piecePush D0 a) z) ∈
          ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))) =>
      hz (hinjPush (hinjF (hzy.trans hxy.symm))))
    (fun (z : (Fam a.2).pt) (hz : z ∉ ({y} : Set (Fam a.2).pt))
        (hzy : e.symm ⟨a, z⟩ ∈
          ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))) =>
      hz (eq_of_heq (Sigma.mk.inj_iff.mp (e.symm.injective hzy)).2))
  have hcomp := (Work.PTGeometric.HOF.RelHmapOf_comp
    (n := 8)
    (K := ({y} : Set (Fam a.2).pt))
    (K' := ({(Work.ThomBordism.piecePush D0 a) y} : Set ↥(Work.ThomBordism.sourceLevelBdry D0)))
    (K'' := ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
      (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L))))
    (TopCat.ofHom (Work.ThomBordism.piecePush D0 a))
    (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0)
    (fun (z : (Fam a.2).pt) (hz : z ∉ ({y} : Set (Fam a.2).pt))
        (hzy : (Work.ThomBordism.piecePush D0 a) z ∈
          ({(Work.ThomBordism.piecePush D0 a) y} : Set ↥(Work.ThomBordism.sourceLevelBdry D0))) =>
      hz (hinjPush hzy))
    (fun (z : ↥(Work.ThomBordism.sourceLevelBdry D0))
        (hz : z ∉ ({(Work.ThomBordism.piecePush D0 a) y} : Set ↥(Work.ThomBordism.sourceLevelBdry D0)))
        (hzy : (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0) z ∈
          ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))) =>
      hz (hinjF (hzy.trans hxy.symm)))
    (fun (z : (Fam a.2).pt) (hz : z ∉ ({y} : Set (Fam a.2).pt))
        (hzy : (Work.ThomBordism.boundaryTransferTopSymm (hWcl := hWcl) (L := L) D0)
            ((Work.ThomBordism.piecePush D0 a) z) ∈
          ({e.symm ⟨a, y⟩} : Set ↥((modelWithCornersEuclideanHalfSpace 9).boundary
            (Work.PTGeometric.levelModel (Work.ThomBordism.sourceLevelSet D0) hWcl L)))) =>
      hz (hinjPush (hinjF (hzy.trans hxy.symm))))).trans hR
  exact DFunLike.congr_fun hcomp (Work.Orient.locClass (Fam a.2).X 8 (Fam a.2).c y)

end

#print axioms Work.ThomBordism.locClass_sum_pushClass_eq_relHmapOf

end Work.ThomBordism
