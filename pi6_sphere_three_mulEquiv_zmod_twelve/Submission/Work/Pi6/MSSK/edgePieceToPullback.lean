import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.SSSR.edgeTransport
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.vertRestrEZDefs
import Submission.Work.SSSR.singPullbackIso_exists
import Submission.Work.Pi6.MSSK.lastPathExists
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The vertices of `Δ[1]` and the interval

The `0`-th and `1`-st vertices of `Δ[1]`, read as `0`-simplices, and the composites of the
inclusions of the two vertices into `Δ[1]` with the canonical `1`-simplex of the interval. -/

lemma vtx0S1_eq_obj : Work.SSSR.vtx0S1 = SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
  rw [Work.SSSR.vtx0S1, Work.SSSR.idS1, Work.SSSR.stdIdSimplex]
  rw [SSet.stdSimplex.δ_objEquiv_symm_apply, Category.comp_id]
  rw [SimplexCategory.δ_one_eq_const]
  rfl

lemma vtx1S1_eq_obj : Work.SSSR.vtx1S1 = SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
  rw [Work.SSSR.vtx1S1, Work.SSSR.idS1, Work.SSSR.stdIdSimplex]
  rw [SSet.stdSimplex.δ_objEquiv_symm_apply, Category.comp_id]
  rw [SimplexCategory.δ_zero_eq_const]
  rfl

lemma firstV_one_eq_const : Work.Pi6.MSSK.firstV 1 = SSet.const Work.SSSR.vtx0S1 := by
  rw [vtx0S1_eq_obj, Work.Pi6.MSSK.firstV]
  rw [show SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)
      = SSet.stdSimplex.δ (n := 0) (1 : Fin 2) from by
    rw [← SimplexCategory.δ_one_eq_const]; rfl]
  exact SSet.stdSimplex.δ_one_eq_const

lemma lastV_one_eq_const : Work.Pi6.MSSK.lastV 1 = SSet.const Work.SSSR.vtx1S1 := by
  rw [vtx1S1_eq_obj, Work.Pi6.MSSK.lastV]
  rw [show (Fin.last 1 : Fin 2) = 1 from by decide]
  rw [show SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 1)
      = SSet.stdSimplex.δ (n := 0) (0 : Fin 2) from by
    rw [← SimplexCategory.δ_zero_eq_const]; rfl]
  exact SSet.stdSimplex.δ_zero_eq_const

lemma firstV_comp_vertLiftI : Work.Pi6.MSSK.firstV 1 ≫ Work.SSSR.vertLiftI
    = SSet.const (TopCat.toSSetObj₀Equiv.symm (0 : unitInterval)) := by
  rw [firstV_one_eq_const, SSet.const_comp]
  rw [show ((ConcreteCategory.hom (Work.SSSR.vertLiftI.app (op ⦋0⦌))) Work.SSSR.vtx0S1)
      = TopCat.toSSetObj₀Equiv.symm (0 : unitInterval) from by
    rw [Equiv.eq_symm_apply, Work.SSSR.toSSetObj₀Equiv_vertLiftI_vtx0]]

lemma lastV_comp_vertLiftI : Work.Pi6.MSSK.lastV 1 ≫ Work.SSSR.vertLiftI
    = SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)) := by
  rw [lastV_one_eq_const, SSet.const_comp]
  rw [show ((ConcreteCategory.hom (Work.SSSR.vertLiftI.app (op ⦋0⦌))) Work.SSSR.vtx1S1)
      = TopCat.toSSetObj₀Equiv.symm (1 : unitInterval) from by
    rw [Equiv.eq_symm_apply, Work.SSSR.toSSetObj₀Equiv_vertLiftI_vtx1]]

/-! ## The projections of the vertex identification

`vertexIso p σ'` is the identification of the vertex piece `T_{σ'}` with the singular simplicial
set of the fibre of `p` over `σ'`.  Its inverse is `phiAlong`, so the two projections of `T_{σ'}`
are computed from those of `phiAlong` (`phiAlong_fst`, `phiAlong_snd`). -/

lemma vertexIso_inv (p : C(E, B)) (σ' : Δ[0] ⟶ Work.SSSR.sSing B) :
    (vertexIso p σ').inv = Work.SSSR.phiAlong p σ' := by
  rw [vertexIso, Work.SSSR.pullAlongVertexIsoIso]
  rfl

lemma vertexIso_hom_comp_fst (p : C(E, B)) (σ' : Δ[0] ⟶ Work.SSSR.sSing B) :
    (vertexIso p σ').hom ≫ Work.SSSR.phiAlongFst p σ'
      = pullback.fst σ' (Work.SSSR.sSingP p) := by
  rw [← Work.SSSR.phiAlong_fst p σ']
  rw [show Work.SSSR.phiAlong p σ' = (vertexIso p σ').inv from (vertexIso_inv p σ').symm]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma vertexIso_hom_comp_snd (p : C(E, B)) (σ' : Δ[0] ⟶ Work.SSSR.sSing B) :
    (vertexIso p σ').hom ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p (Work.SSSR.sigmaVert σ'))
      = pullback.snd σ' (Work.SSSR.sSingP p) := by
  rw [← Work.SSSR.phiAlong_snd p σ']
  rw [show Work.SSSR.phiAlong p σ' = (vertexIso p σ').inv from (vertexIso_inv p σ').symm]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-! ## The projections of the two vertex inclusions of the edge piece -/

lemma vtx0Incl_comp_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx0Incl p σ ≫ pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
      = pullback.fst (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1 :=
  pullback.lift_fst _ _ _

lemma vtx0Incl_comp_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx0Incl p σ ≫ pullback.snd (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
      = pullback.snd (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) :=
  pullback.lift_snd _ _ _

lemma vtx1Incl_comp_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx1Incl p σ ≫ pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
      = pullback.fst (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV 1 :=
  pullback.lift_fst _ _ _

lemma vtx1Incl_comp_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx1Incl p σ ≫ pullback.snd (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
      = pullback.snd (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) :=
  pullback.lift_snd _ _ _

/-! ## The canonical comparison map -/

/-- The composite of the pullback projections is the same map in both factors: this is where the
path `γ` enters, through `hγ`. -/
lemma liftI_comp_sSingP {B : Type} [TopologicalSpace B] {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    Work.SSSR.vertLiftI ≫ Work.SSSR.sSingP γ.toContinuousMap
      = Work.Pi6.MSSK.lastEdge t ≫ σ := by
  refine Equiv.injective SSet.yonedaEquiv ?_
  rw [SSet.yonedaEquiv_comp]
  rw [show SSet.yonedaEquiv Work.SSSR.vertLiftI = Work.SSSR.lambda1 from
    Equiv.apply_symm_apply SSet.yonedaEquiv Work.SSSR.lambda1]
  rw [hγ]
  rfl

/-- The composite of the vertex inclusion with the `Δ[1]`-projection of the comparison map is the
`Δ[1]`-projection of the vertex piece, followed by the canonical `1`-simplex of the interval. -/
lemma vtx0Incl_comp_snd_vertLiftI (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx0Incl p σ ≫ (pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
        ≫ Work.SSSR.vertLiftI)
      = pullback.fst (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) ≫ SSet.const (TopCat.toSSetObj₀Equiv.symm (0 : unitInterval)) := by
  conv_lhs => rw [← Category.assoc, vtx0Incl_comp_fst, Category.assoc, firstV_comp_vertLiftI]

/-- The same for the last vertex of `Δ[1]`. -/
lemma vtx1Incl_comp_snd_vertLiftI (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    vtx1Incl p σ ≫ (pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
        ≫ Work.SSSR.vertLiftI)
      = pullback.fst (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)
          (Work.SSSR.sSingP p) ≫ SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)) := by
  conv_lhs => rw [← Category.assoc, vtx1Incl_comp_fst, Category.assoc, lastV_comp_vertLiftI]

/-- The compatibility of the two components of the comparison map: the `Δ[1]`-projection followed
by the canonical `1`-simplex of the interval and the `E`-projection are equal after projecting to
the base, by `liftI_comp_sSingP`. -/
lemma edgePieceMap_condition (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    (pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
        ≫ Work.SSSR.vertLiftI) ≫ Work.SSSR.sSingP γ.toContinuousMap
      = pullback.snd (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
        ≫ Work.SSSR.sSingP p := by
  rw [Category.assoc, liftI_comp_sSingP σ γ hγ]
  exact pullback.condition

/-- **The edge piece maps to the pullback of `p` along the path `γ`.**  The `Δ[1]`-coordinate is
the first projection `a : T_τ ⟶ Δ[1]` composed with the canonical `1`-simplex of the interval,
and the `E`-coordinate is the second projection `b : T_τ ⟶ Sing E`.  The compatibility of the two
is exactly `hγ` (via `liftI_comp_sSingP`). -/
noncomputable def edgePieceMap (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p) (Work.Pi6.MSSK.lastEdge t ≫ σ) ⟶
      pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap) :=
  pullback.lift (pullback.snd (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p))
    (pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p) ≫ Work.SSSR.vertLiftI)
    (edgePieceMap_condition p σ γ hγ).symm

lemma edgePieceMap_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    edgePieceMap p σ γ hγ ≫ pullback.fst (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = pullback.snd (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p) :=
  pullback.lift_fst _ _ _

lemma edgePieceMap_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    edgePieceMap p σ γ hγ ≫ pullback.snd (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = pullback.fst (Work.Pi6.MSSK.lastEdge t ≫ σ) (Work.SSSR.sSingP p)
          ≫ Work.SSSR.vertLiftI :=
  pullback.lift_snd _ _ _

/-! ## The vertex conditions -/

lemma edgePieceMap_vtx0 (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ)
    (e : Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap))
    (he₁ : e.hom ≫ pullback.fst (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap))
    (he₂ : e.hom ≫ pullback.snd (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackSnd p γ.toContinuousMap)) :
    vtx0Incl p σ ≫ edgePieceMap p σ γ hγ
      = (vertexIso p (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)).hom
          ≫ Work.SSSR.sSingP (Work.SSSR.inclSource p γ) ≫ e.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [edgePieceMap_fst, vtx0Incl_comp_snd]
    rw [he₁]
    simp only [Work.SSSR.sSingP]
    rw [← Functor.map_comp, Work.SSSR.inclSource_comp_pullbackFst]
    exact (vertexIso_hom_comp_snd p
      (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)).symm
  · simp only [Category.assoc]
    conv_lhs => rw [edgePieceMap_snd]
    rw [vtx0Incl_comp_snd_vertLiftI p σ]
    conv_lhs =>
      rw [← vertexIso_hom_comp_fst p (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ),
        Category.assoc, SSet.comp_const]
    rw [he₂]
    simp only [Work.SSSR.sSingP]
    rw [← Functor.map_comp, Work.SSSR.inclSource_comp_pullbackSnd, TopCat.toSSet_map_const]

lemma edgePieceMap_vtx1 (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ))
        (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ)
    (e : Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap))
    (he₁ : e.hom ≫ pullback.fst (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackFst p γ.toContinuousMap))
    (he₂ : e.hom ≫ pullback.snd (Work.SSSR.sSingP p) (Work.SSSR.sSingP γ.toContinuousMap)
      = Work.SSSR.sSingP (Work.SSSR.StemsB.pullbackSnd p γ.toContinuousMap)) :
    vtx1Incl p σ ≫ edgePieceMap p σ γ hγ
      = (vertexIso p (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)).hom
          ≫ Work.SSSR.sSingP (Work.SSSR.inclTarget p γ) ≫ e.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [edgePieceMap_fst, vtx1Incl_comp_snd]
    rw [he₁]
    simp only [Work.SSSR.sSingP]
    rw [← Functor.map_comp, Work.SSSR.inclTarget_comp_pullbackFst]
    exact (vertexIso_hom_comp_snd p
      (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ)).symm
  · simp only [Category.assoc]
    conv_lhs => rw [edgePieceMap_snd]
    rw [vtx1Incl_comp_snd_vertLiftI p σ]
    conv_lhs =>
      rw [← vertexIso_hom_comp_fst p (Work.Pi6.MSSK.lastV 1 ≫ Work.Pi6.MSSK.lastEdge t ≫ σ),
        Category.assoc, SSet.comp_const]
    rw [he₂]
    simp only [Work.SSSR.sSingP]
    rw [← Functor.map_comp, Work.SSSR.inclTarget_comp_pullbackSnd, TopCat.toSSet_map_const]

theorem edgePieceToPullback {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (γ : Path (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.firstV 1) (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastEdge t) σ)))
        (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastV 1) (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastEdge t) σ))))
    (hγ : (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1))
        Work.SSSR.lambda1 = Work.Pi6.MSSK.lastEdgeSimplex t σ) :
    ∃ Φ : Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ) ⟶
        Work.SSSR.sSing (Work.SSSR.StemsB.Pullback p γ.toContinuousMap),
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.vtx0Incl p σ) Φ
        = CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.firstV 1) (CategoryTheory.CategoryStruct.comp
                (Work.Pi6.MSSK.lastEdge t) σ))).hom
            (Work.SSSR.sSingP (Work.SSSR.inclSource p γ)))
      ∧ (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.vtx1Incl p σ) Φ
        = CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastV 1) (CategoryTheory.CategoryStruct.comp
                (Work.Pi6.MSSK.lastEdge t) σ))).hom
            (Work.SSSR.sSingP (Work.SSSR.inclTarget p γ))) := by
  obtain ⟨e, he₁, he₂⟩ := Work.SSSR.singPullbackIso_exists p γ.toContinuousMap
  refine ⟨edgePieceMap p σ γ hγ ≫ e.inv, ?_, ?_⟩
  · rw [show vtx0Incl p σ ≫ edgePieceMap p σ γ hγ ≫ e.inv
          = (vtx0Incl p σ ≫ edgePieceMap p σ γ hγ) ≫ e.inv from (Category.assoc _ _ _).symm]
    rw [edgePieceMap_vtx0 p σ γ hγ e he₁ he₂]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [show vtx1Incl p σ ≫ edgePieceMap p σ γ hγ ≫ e.inv
          = (vtx1Incl p σ ≫ edgePieceMap p σ γ hγ) ≫ e.inv from (Category.assoc _ _ _).symm]
    rw [edgePieceMap_vtx1 p σ γ hγ e he₁ he₂]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end Work.Pi6.MSSK
