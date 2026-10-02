import Submission.Work.ThomBordism.PontryaginThom.Family

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Reindexing null-bordisms, and the single/family transversality inputs

Two consequences of the interface `Work.ThomBordism.Interface`:

* `nullBordismFamilyOfEquivConst` — a null-bordism of a **constant** family is invariant under a
  bijection of the index type: the pieces are the same manifold, so the boundary reindexes by the
  sigma-homeomorphism over the common fibre and the boundary sum reindexes along `e`.  Since a
  family with one piece is a single manifold, this gives
* `transversalityCoreOfFamily` — `TransversalityCore` from `TransversalityCoreFamily`, and
* `transversalityOfTransversalityFamily` — the *single-manifold* transversality input is a
  consequence of the family one (the `Fin 1`-family rep of `V` has the same class as the single rep:
  `ptFamilyRepOfRep`, `Family.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- The canonical equivalence `Fin N × Fin 1 ≃ Fin N`. -/
def finProdOneEquiv (N : ℕ) : Fin N × Fin 1 ≃ Fin N where
  toFun x := x.1
  invFun i := (i, 0)
  left_inv := fun x => Prod.ext rfl (Subsingleton.elim 0 x.2)
  right_inv := fun _ => rfl

/-- **Sigma types over equivalent index types with a common fibre are homeomorphic** (the sigma
topology sees only the fibres, so no continuity of `e` is needed). -/
def homeomorphSigmaConst {ι ι' : Type} (e : ι ≃ ι') (X : Type) [TopologicalSpace X] :
    (Σ _ : ι, X) ≃ₜ (Σ _ : ι', X) where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, y.2⟩
  left_inv x := Sigma.ext (e.symm_apply_apply x.1) (HEq.refl x.2)
  right_inv y := Sigma.ext (e.apply_symm_apply y.1) (HEq.refl y.2)
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact continuous_sigmaMk (σ := fun _ => X) (i := e i)
  continuous_invFun := by
    apply continuous_sigma
    intro j
    exact continuous_sigmaMk (σ := fun _ => X) (i := e.symm j)

/-- The `i`-th summand of the boundary equation of a null-bordism family: the push-forward of the
fundamental class of the `i`-th piece along `∂W → (F i).pt`, viewed in the homology of the
boundary.  (`NullBordismFamily.hw` is the statement that `hPairδ` is the sum of these summands.) -/
def bdrySummand {ι : Type} (V : Man8) {W : Type} [TopologicalSpace W] (b : Set W)
    (bdry : b ≃ₜ (Σ _ : ι, V.pt)) (i : ι) :
    (chainC ℤ (TopCat.toSSet.obj (TopCat.of b))).homology 8 :=
  HomologicalComplex.homologyMap
    (chainMap ℤ V.X (TopCat.of b)
      (TopCat.ofHom ⟨fun y => bdry.symm ⟨i, y⟩,
        bdry.continuous_invFun.comp continuous_sigmaMk⟩)) 8 V.c

/-- **Reindexing a null-bordism of a constant family.**  The bounding manifold, its relative
fundamental class and the local-generator condition are untouched; only the identification of the
boundary with `Σ i' : ι', V.pt` changes, and the boundary sum is reindexed along `e`. -/
theorem nullBordismFamilyOfEquivConst {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (V : Man8) (hW : NullBordismFamily ι (fun _ => V)) :
    Nonempty (NullBordismFamily ι' (fun _ => V)) := by
  let : TopologicalSpace hW.W := hW.topologicalSpace
  let : ChartedSpace (EuclideanHalfSpace 9) hW.W := hW.chartedSpace
  let : IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 hW.W := hW.isManifold
  let : CompactSpace hW.W := hW.compactSpace
  let : T2Space hW.W := hW.t2Space
  let bdry' : ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) ≃ₜ (Σ _ : ι', V.pt) :=
    { toFun := fun x => ⟨e (hW.bdry x).1, (hW.bdry x).2⟩
      invFun := fun y => hW.bdry.symm ⟨e.symm y.1, y.2⟩
      left_inv := by
        intro x
        show hW.bdry.symm ⟨e.symm (e (hW.bdry x).1), (hW.bdry x).2⟩ = x
        rw [e.symm_apply_apply]
        exact hW.bdry.symm_apply_apply x
      right_inv := by
        rintro ⟨j, y⟩
        show (⟨e (hW.bdry (hW.bdry.symm ⟨e.symm j, y⟩)).1,
          (hW.bdry (hW.bdry.symm ⟨e.symm j, y⟩)).2⟩ : Σ _ : ι', V.pt) = ⟨j, y⟩
        rw [hW.bdry.apply_symm_apply]
        exact Sigma.ext (e.apply_symm_apply j) (HEq.refl y)
      continuous_toFun :=
        (homeomorphSigmaConst e V.pt).continuous_toFun.comp hW.bdry.continuous_toFun
      continuous_invFun :=
        hW.bdry.continuous_invFun.comp (homeomorphSigmaConst e.symm V.pt).continuous_toFun }
  refine ⟨{ W := hW.W, bdry := bdry', w := hW.w, hw := ?_, w_fund := hW.w_fund }⟩
  show hPairδ (TopCat.of hW.W) ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) 8 hW.w
    = ∑ i' : ι', bdrySummand V ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) bdry' i'
  have h1 : hPairδ (TopCat.of hW.W) ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) 8 hW.w
      = ∑ i : ι,
        bdrySummand V ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) hW.bdry i :=
    hW.hw
  rw [h1]
  rw [Fintype.sum_equiv e.symm
    (fun i' => bdrySummand V ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) bdry' i')
    (fun i => bdrySummand V ((modelWithCornersEuclideanHalfSpace 9).boundary hW.W) hW.bdry i)
    (fun _ => rfl)]

/-- **`TransversalityCore` from `TransversalityCoreFamily`**: a family with one piece is a single
manifold, and the null-bordism reindexes along `Fin N × Fin 1 ≃ Fin N`. -/
theorem transversalityCoreOfFamily (h : TransversalityCoreFamily) : TransversalityCore := by
  intro V h1 h2
  obtain ⟨N, hN, hW⟩ := h (Fin 1) (fun _ => V) (by simpa using h1) (by simpa using h2)
  exact ⟨N, hN, nullBordismFamilyOfEquivConst (finProdOneEquiv N) V hW.some⟩

/-- **The single-manifold transversality input follows from the family one** (the `Fin 1`-family rep
of `V` is a single rep of `V`, with the same class). -/
theorem transversalityOfTransversalityFamily {k : ℕ} {D : ThomTarget k}
    (h : TransversalityFamily k D) : Transversality k D := by
  intro V r hpow
  obtain ⟨N, hN, hW⟩ := h (Fin 1) (fun _ => V) (ptFamilyRepOfRep r) hpow
  exact ⟨N, hN, nullBordismFamilyOfEquivConst (finProdOneEquiv N) V hW.some⟩

end

end Work.ThomBordism.PontryaginThom
