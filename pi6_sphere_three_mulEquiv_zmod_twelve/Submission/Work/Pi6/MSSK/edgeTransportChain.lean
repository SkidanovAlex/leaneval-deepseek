import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.VertexBridges
import Submission.Work.Pi6.MSSK.edgePieceToPullback
import Submission.Work.Pi6.MSSK.mono_edgeIncl
import Submission.Work.SSSR.transportIsoPathChain
import Submission.Work.SSSR.edgeTransport
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- **Pointwise functoriality of `sCCMap` along an identity of simplicial maps.**  If two
composites of simplicial maps agree, then the corresponding composites of chain maps agree on
every chain. -/
lemma sCCMap_apply_comp (R : Type) [CommRing R] [Nontrivial R] {X Y Z A : SSet} (f : X ⟶ Y)
    (g : Y ⟶ Z) (b : X ⟶ A) (a : A ⟶ Z) (h : f ≫ g = b ≫ a) (K : ℕ)
    (x : (Work.SSSR.sCC R X).X K) :
    (Work.SSSR.sCCMap R g).f K ((Work.SSSR.sCCMap R f).f K x)
      = (Work.SSSR.sCCMap R a).f K ((Work.SSSR.sCCMap R b).f K x) := by
  have hh := congrArg (fun (ζ : X ⟶ Z) => (Work.SSSR.sCCMap R ζ).f K) h
  simp only [Work.SSSR.sCCMap, Functor.map_comp, HomologicalComplex.comp_f] at hh
  have h3 := congrArg (fun (φ : (Work.SSSR.sCC R X).X K ⟶ (Work.SSSR.sCC R Z).X K) =>
    (ModuleCat.Hom.hom φ) x) hh
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h3

/-- **Naturality of `chainClass` under a chain map.**  The image of the homology class of a cycle
is the class of the image of the cycle. -/
lemma homologyMap_chainClass (R : Type) [CommRing R] [Nontrivial R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (n : ℕ) (x : K.X n)
    (hx : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) x = 0)
    (hy : (ModuleCat.Hom.hom (L.d n ((ComplexShape.down ℕ).next n)))
        ((ModuleCat.Hom.hom (φ.f n)) x) = 0) :
    (ConcreteCategory.hom (HomologicalComplex.homologyMap φ n)) (chainClass R K n x hx)
      = chainClass R L n ((ModuleCat.Hom.hom (φ.f n)) x) hy := by
  rw [chainClass, chainClass, Work.SSSR.homologyMap_homologypi_C, Work.SSSR.cyclesMap_cyclesMk_C]

theorem edgeTransportChain (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) {t K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))
        (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ)
    (z0 : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))).X K)
    (hz0 : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))).d K
            ((ComplexShape.down ℕ).next K))) z0 = 0)
    (z1 : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))).X K)
    (hz1 : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))).d K
            ((ComplexShape.down ℕ).next K))) z1 = 0)
    (W0 : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))).X (K+1))
    (hW : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))).d (K+1) K)) W0
        = (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx1Incl p σ)).f K z1
          - (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx0Incl p σ)).f K z0) :
    (Work.SSSR.transportIsoPath p hfib γ K).hom
        (CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
          (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.firstV 1) (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastEdge t) σ))).hom) K)
          (Work.Pi6.MSSK.chainClass R (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))) K z0 hz0))
      = CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
          (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV 1) (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastEdge t) σ))).hom) K)
          (Work.Pi6.MSSK.chainClass R (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))) K z1 hz1) := by
  obtain ⟨Φ, h0, h1⟩ := edgePieceToPullback p hfib σ γ hγ
  -- Abbreviations for the edge and for its two vertices.
  let τ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSSR.sSing B :=
    CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ
  let σ0 : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B :=
    CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1) τ
  let σ1 : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B :=
    CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1) τ
  have h0' : Work.Pi6.MSSK.vtx0Incl p σ ≫ Φ
      = (Work.Pi6.MSSK.vertexIso p σ0).hom ≫ Work.SSSR.sSingP (Work.SSSR.inclSource p γ) := h0
  have h1' : Work.Pi6.MSSK.vtx1Incl p σ ≫ Φ
      = (Work.Pi6.MSSK.vertexIso p σ1).hom ≫ Work.SSSR.sSingP (Work.SSSR.inclTarget p γ) := h1
  -- The two cycles, pushed forward through the vertex identifications, are cycles.
  have hz0' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ0)))).d K
          ((ComplexShape.down ℕ).next K)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ0).hom).f K)) z0) = 0 := by
    rw [Work.SSSR.chainMap_comm_apply_C]
    rw [hz0, map_zero]
  have hz1' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ1)))).d K
          ((ComplexShape.down ℕ).next K)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ1).hom).f K)) z1) = 0 := by
    rw [Work.SSSR.chainMap_comm_apply_C]
    rw [hz1, map_zero]
  -- The chain-level identities: pushing a chain of a vertex piece into the edge piece and then
  -- into the pullback along the path is the same as first taking the vertex identification and
  -- then the inclusion of the fibre.
  have key0 : ∀ x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ0)).X K,
      (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R Φ).f K))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx0Incl p σ)).f K)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.sourceChainMap (R := R) p γ).f K))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ0).hom).f K)) x) :=
    fun x => sCCMap_apply_comp R (Work.Pi6.MSSK.vtx0Incl p σ) Φ (Work.Pi6.MSSK.vertexIso p σ0).hom
      (Work.SSSR.sSingP (Work.SSSR.inclSource p γ)) h0' K x
  have key1 : ∀ x : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ1)).X K,
      (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R Φ).f K))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx1Incl p σ)).f K)) x)
      = (ModuleCat.Hom.hom ((Work.SSSR.targetChainMap (R := R) p γ).f K))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ1).hom).f K)) x) :=
    fun x => sCCMap_apply_comp R (Work.Pi6.MSSK.vtx1Incl p σ) Φ (Work.Pi6.MSSK.vertexIso p σ1).hom
      (Work.SSSR.sSingP (Work.SSSR.inclTarget p γ)) h1' K x
  rw [homologyMap_chainClass R (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ0).hom) K z0 hz0 hz0',
    homologyMap_chainClass R (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ1).hom) K z1 hz1 hz1']
  refine Work.SSSR.transportIsoPathChain (R := R) p hfib γ K
    ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ0).hom).f K)) z0) hz0'
    ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p σ1).hom).f K)) z1) hz1'
    (- (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R Φ).f (K+1))) W0) ?_
  rw [map_neg, Work.SSSR.chainMap_comm_apply_C, hW, map_sub, key1, key0, neg_sub]

end

end Work.Pi6.MSSK
