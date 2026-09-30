import Mathlib
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.VertexBridges
import Submission.Work.Pi6.MSSK.CapThetaLift
import Submission.Work.Pi6.MSSK.TransportAux
import Submission.Work.Pi6.MSSK.capEdgeIdentity
import Submission.Work.Pi6.MSSK.capLastFaceTop_edgeIncl
import Submission.Work.Pi6.MSSK.edgePieceToPullback
import Submission.Work.Pi6.MSSK.edgeTransportChain
import Submission.Work.Pi6.MSSK.mono_edgeIncl
import Submission.Work.Pi6.MSSK.fibreIncCapThetaLift
import Submission.Work.Pi6.MSSK.capThetaLift_isCycle
import Submission.Work.Pi6.MSSK.exists_bdry_lift_of_pieceAlong_cycle
import Submission.Work.Pi6.MSSK.lastPathExists
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.pieceIso_peel
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.Pi6.MSSK.peel_aux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Transport of morphisms along the two spellings of the vertices of the last edge -/

/-- The two spellings of the target vertex of the last edge. -/
lemma hmap_edge1 {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
      = CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ := by
  rw [← Category.assoc, lastEdgeVertexBridges_fst]

/-- The two spellings of the source vertex of the last edge. -/
lemma hmap_edge0 {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
      = CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) := by
  rw [← Category.assoc, lastEdgeVertexBridges_snd, Category.assoc]

/-- Transport of a dependent morphism along an equality of indices. -/
lemma eqToHom_congr_mor {α : Type} {C : Type*} [Category C] (F G : α → C)
    (φ : ∀ a, F a ⟶ G a) {a b : α} (h : a = b) :
    eqToHom (congrArg F h) ≫ φ b = φ a ≫ eqToHom (congrArg G h) := by
  cases h; simp

/-- The first projection of a pullback, transported along an equality of the two maps. -/
lemma eqToHom_pullback_fst {A X Y : SSet.{0}} {σ σ' : A ⟶ Y} (f : X ⟶ Y) (h : σ = σ') :
    eqToHom (congrArg (fun g => pullback g f) h) ≫ pullback.fst σ' f = pullback.fst σ f := by
  cases h; simp

/-- The second projection of a pullback, transported along an equality of the two maps. -/
lemma eqToHom_pullback_snd {A X Y : SSet.{0}} {σ σ' : A ⟶ Y} (f : X ⟶ Y) (h : σ = σ') :
    eqToHom (congrArg (fun g => pullback g f) h) ≫ pullback.snd σ' f = pullback.snd σ f := by
  cases h; simp

/-! ## The two vertex inclusions of the edge piece -/

/-- The inclusion into the edge piece of the part over the vertex `1` of `Δ[1]` (i.e. over the
vertex `t+1` of `Δ[t+1]`), in the `lastV (t+1)` spelling. -/
def edgeVertex1Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ) :=
  show pullback (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
      (Work.SSSR.sSingP p) ⟶ pullback (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) from
  pullback.lift
    (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
        (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV 1)
    (pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
        (Work.SSSR.sSingP p))
    (by rw [Category.assoc, hmap_edge1]; exact pullback.condition)

/-- The inclusion into the edge piece of the part over the vertex `0` of `Δ[1]` (i.e. over the
vertex `t` of `Δ[t+1]`, the last vertex of the last face), in the `lastV t ≫ δ` spelling. -/
def edgeVertex0Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ) :=
  show pullback (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
      (Work.SSSR.sSingP p) ⟶ pullback (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) from
  pullback.lift
    (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
        (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1)
    (pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
        (Work.SSSR.sSingP p))
    (by rw [Category.assoc, hmap_edge0]; exact pullback.condition)

lemma edgeVertex1Incl_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex1Incl p σ ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)
      = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV 1 := pullback.lift_fst _ _ _

lemma edgeVertex1Incl_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex1Incl p σ ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)
      = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
          (Work.SSSR.sSingP p) := pullback.lift_snd _ _ _

lemma edgeVertex0Incl_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex0Incl p σ ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)
      = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1 := pullback.lift_fst _ _ _

lemma edgeVertex0Incl_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex0Incl p σ ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
        (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)
      = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
          (Work.SSSR.sSingP p) := pullback.lift_snd _ _ _

lemma edgeIncl_fst (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.edgeIncl p σ ≫ pullback.fst σ (Work.SSSR.sSingP p)
      = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastEdge t := pullback.lift_fst _ _ _

lemma edgeIncl_snd (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.edgeIncl p σ ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
          (Work.SSSR.sSingP p) := pullback.lift_snd _ _ _

lemma fibreInc_fst_edge (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.fibreInc p σ ≫ pullback.fst σ (Work.SSSR.sSingP p)
      = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV (t+1) := pullback.lift_fst _ _ _

lemma fibreInc_snd_edge (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.fibreInc p σ ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
          (Work.SSSR.sSingP p) := pullback.lift_snd _ _ _

/-! ## The projection lemmas of the fibre inclusion in general degree -/

lemma fibreInc_fst_gen (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.fibreInc p σ ≫ pullback.fst σ (Work.SSSR.sSingP p)
      = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)
          (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV s := pullback.lift_fst _ _ _

lemma fibreInc_snd_gen (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Pi6.MSSK.fibreInc p σ ≫ pullback.snd σ (Work.SSSR.sSingP p)
      = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV s) σ)
          (Work.SSSR.sSingP p) := pullback.lift_snd _ _ _

/-- **The vertex-`1` inclusion of the edge piece, followed by the edge inclusion, is the fibre
inclusion over the last vertex.** -/
theorem edgeVertex1Incl_edgeIncl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex1Incl p σ ≫ Work.Pi6.MSSK.edgeIncl p σ = Work.Pi6.MSSK.fibreInc p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, edgeIncl_fst, ← Category.assoc, edgeVertex1Incl_fst, Category.assoc,
      lastEdgeVertexBridges_fst, ← fibreInc_fst_edge]
  · rw [Category.assoc, edgeIncl_snd, edgeVertex1Incl_snd, fibreInc_snd_edge]

/-- **The vertex-`0` inclusion of the edge piece, followed by the edge inclusion, is the fibre
inclusion over the last vertex of the last face, followed by the pasting map.** -/
theorem edgeVertex0Incl_edgeIncl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    edgeVertex0Incl p σ ≫ Work.Pi6.MSSK.edgeIncl p σ
      = Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
        ≫ Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ := by
  apply pullback.hom_ext
  · calc (edgeVertex0Incl p σ ≫ Work.Pi6.MSSK.edgeIncl p σ) ≫ pullback.fst σ (Work.SSSR.sSingP p)
        = edgeVertex0Incl p σ ≫ (Work.Pi6.MSSK.edgeIncl p σ ≫ pullback.fst σ (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = edgeVertex0Incl p σ ≫ (pullback.fst (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)
              ≫ Work.Pi6.MSSK.lastEdge t) :=
          congrArg (fun g => edgeVertex0Incl p σ ≫ g) (edgeIncl_fst p σ)
      _ = (edgeVertex0Incl p σ ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p)) ≫ Work.Pi6.MSSK.lastEdge t :=
          (Category.assoc _ _ _).symm
      _ = (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1) ≫ Work.Pi6.MSSK.lastEdge t :=
          congrArg (fun g => g ≫ Work.Pi6.MSSK.lastEdge t) (edgeVertex0Incl_fst p σ)
      _ = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) ≫ (Work.Pi6.MSSK.firstV 1 ≫ Work.Pi6.MSSK.lastEdge t) :=
          Category.assoc _ _ _
      _ = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p)
            ≫ (Work.Pi6.MSSK.lastV t ≫ SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) :=
          congrArg (fun g => pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) ≫ g) (lastEdgeVertexBridges_snd t)
      _ = (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV t)
            ≫ SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) :=
          (Category.assoc _ _ _).symm
      _ = (Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
              ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) (Work.SSSR.sSingP p))
            ≫ SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) :=
          congrArg (fun g => g ≫ SSet.stdSimplex.δ (n := t) (Fin.last (t+1)))
            (fibreInc_fst_gen p (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).symm
      _ = Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
            ≫ (pullback.fst (CategoryTheory.CategoryStruct.comp
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) (Work.SSSR.sSingP p)
              ≫ SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) :=
          Category.assoc _ _ _
      _ = Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
            ≫ (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ
                ≫ pullback.fst σ (Work.SSSR.sSingP p)) :=
          congrArg (fun g => Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) ≫ g)
            (Work.SSSR.lastFaceMap_fst (Work.SSSR.sSingP p) t σ).symm
      _ = (Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
              ≫ Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ) ≫ pullback.fst σ (Work.SSSR.sSingP p) :=
          (Category.assoc _ _ _).symm
  · calc (edgeVertex0Incl p σ ≫ Work.Pi6.MSSK.edgeIncl p σ) ≫ pullback.snd σ (Work.SSSR.sSingP p)
        = edgeVertex0Incl p σ ≫ (Work.Pi6.MSSK.edgeIncl p σ ≫ pullback.snd σ (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = edgeVertex0Incl p σ ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) :=
          congrArg (fun g => edgeVertex0Incl p σ ≫ g) (edgeIncl_snd p σ)
      _ = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) :=
          edgeVertex0Incl_snd p σ
      _ = Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
            ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) (Work.SSSR.sSingP p) :=
          (fibreInc_snd_gen p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).symm
      _ = Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
            ≫ (Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ
                ≫ pullback.snd σ (Work.SSSR.sSingP p)) :=
          congrArg (fun g => Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ) ≫ g)
            (Work.SSSR.lastFaceMap_snd (Work.SSSR.sSingP p) t σ).symm
      _ = (Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)
              ≫ Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ) ≫ pullback.snd σ (Work.SSSR.sSingP p) :=
          (Category.assoc _ _ _).symm
/-! ## The comparison of the two spellings of the vertex inclusions -/

/-- `congrArg` commutes with `Eq.symm`. -/
lemma congrArg_symm {α : Type} {β : Sort*} (F : α → β) {a b : α} (h : a = b) :
    (congrArg F h).symm = congrArg F h.symm := by
  cases h; rfl

/-- The `lastV 1`-spelling of the vertex-`1` inclusion of the edge piece is `edgeVertex1Incl`,
after transporting the source along the spelling equality of the vertices. -/
theorem vtx1Incl_eq_edgeVertex1Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm)
        ≫ Work.Pi6.MSSK.vtx1Incl p σ
      = edgeVertex1Incl p σ := by
  apply pullback.hom_ext
  · calc (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm) ≫ Work.Pi6.MSSK.vtx1Incl p σ)
          ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
              (Work.SSSR.sSingP p)
        = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm)
            ≫ (Work.Pi6.MSSK.vtx1Incl p σ
                ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
                    (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm)
            ≫ (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV 1) :=
          congrArg (fun g => eqToHom (congrArg (fun g =>
              Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm) ≫ g)
            (Work.Pi6.MSSK.vtx1Incl_comp_fst p σ)
      _ = (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm)
            ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p))
          ≫ Work.Pi6.MSSK.lastV 1 :=
          (Category.assoc _ _ _).symm
      _ = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
              (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.lastV 1 :=
          congrArg (fun g => g ≫ Work.Pi6.MSSK.lastV 1)
            (eqToHom_pullback_fst (Work.SSSR.sSingP p) (hmap_edge1 σ).symm)
      _ = edgeVertex1Incl p σ ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) :=
          (edgeVertex1Incl_fst p σ).symm
  · calc (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm) ≫ Work.Pi6.MSSK.vtx1Incl p σ)
          ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
              (Work.SSSR.sSingP p)
        = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm)
            ≫ (Work.Pi6.MSSK.vtx1Incl p σ
                ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
                    (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge1 σ).symm)
            ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p) :=
          congrArg (fun g => eqToHom (congrArg (fun g =>
              Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm) ≫ g)
            (Work.Pi6.MSSK.vtx1Incl_comp_snd p σ)
      _ = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ)
              (Work.SSSR.sSingP p) :=
          eqToHom_pullback_snd (Work.SSSR.sSingP p) (hmap_edge1 σ).symm
      _ = edgeVertex1Incl p σ ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) :=
          (edgeVertex1Incl_snd p σ).symm

/-- The `firstV 1`-spelling of the vertex-`0` inclusion of the edge piece is `edgeVertex0Incl`,
after transporting the source along the spelling equality of the vertices. -/
theorem vtx0Incl_eq_edgeVertex0Incl (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm)
        ≫ Work.Pi6.MSSK.vtx0Incl p σ
      = edgeVertex0Incl p σ := by
  apply pullback.hom_ext
  · calc (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm) ≫ Work.Pi6.MSSK.vtx0Incl p σ)
          ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
              (Work.SSSR.sSingP p)
        = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm)
            ≫ (Work.Pi6.MSSK.vtx0Incl p σ
                ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
                    (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm)
            ≫ (pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1) :=
          congrArg (fun g => eqToHom (congrArg (fun g =>
              Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm) ≫ g)
            (Work.Pi6.MSSK.vtx0Incl_comp_fst p σ)
      _ = (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm)
            ≫ pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p))
          ≫ Work.Pi6.MSSK.firstV 1 :=
          (Category.assoc _ _ _).symm
      _ = pullback.fst (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) ≫ Work.Pi6.MSSK.firstV 1 :=
          congrArg (fun g => g ≫ Work.Pi6.MSSK.firstV 1)
            (eqToHom_pullback_fst (Work.SSSR.sSingP p) (hmap_edge0 σ).symm)
      _ = edgeVertex0Incl p σ ≫ pullback.fst (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) :=
          (edgeVertex0Incl_fst p σ).symm
  · calc (eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm) ≫ Work.Pi6.MSSK.vtx0Incl p σ)
          ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
              (Work.SSSR.sSingP p)
        = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm)
            ≫ (Work.Pi6.MSSK.vtx0Incl p σ
                ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)
                    (Work.SSSR.sSingP p)) :=
          Category.assoc _ _ _
      _ = eqToHom (congrArg (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g)
              (hmap_edge0 σ).symm)
            ≫ pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
                  (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))
                (Work.SSSR.sSingP p) :=
          congrArg (fun g => eqToHom (congrArg (fun g =>
              Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm) ≫ g)
            (Work.Pi6.MSSK.vtx0Incl_comp_snd p σ)
      _ = pullback.snd (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
              (Work.SSSR.sSingP p) :=
          eqToHom_pullback_snd (Work.SSSR.sSingP p) (hmap_edge0 σ).symm
      _ = edgeVertex0Incl p σ ≫ pullback.snd (CategoryTheory.CategoryStruct.comp
            (Work.Pi6.MSSK.lastEdge t) σ) (Work.SSSR.sSingP p) :=
          (edgeVertex0Incl_snd p σ).symm

/-! ## Abbreviations for the chain complexes attached to a simplex -/

/-- The chains of the piece `T_σ = Δ[s] ×_{Sing B} Sing E`. -/
abbrev TCC (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)

/-- The chains of the boundary `∂T_σ`. -/
abbrev BCC (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.sCC R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ)

/-- The chains of the horn `Λ_σ`. -/
abbrev HCC (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.sCC R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)

/-! ## Degree bookkeeping for `castElem` -/

/-- The differential commutes with the transport along equalities of both degrees. -/
lemma castElem_d_gen {R : Type} [CommRing R] [Nontrivial R] (K : ChainComplex (ModuleCat R) ℕ)
    {i j i' j' : ℕ} (hi : i = i') (hj : j = j') (x : K.X i) :
    (K.d i' j').hom (Work.SSSR.castElem K hi x)
      = Work.SSSR.castElem K hj ((K.d i j).hom x) := by
  subst hi; subst hj; simp [Work.SSSR.castElem]

lemma castElem_add {R : Type} [CommRing R] [Nontrivial R] (K : ChainComplex (ModuleCat R) ℕ)
    {i j : ℕ} (h : i = j) (x y : K.X i) :
    Work.SSSR.castElem K h (x + y)
      = Work.SSSR.castElem K h x + Work.SSSR.castElem K h y := by
  subst h; simp [Work.SSSR.castElem]

lemma castElem_smul {R : Type} [CommRing R] [Nontrivial R] (K : ChainComplex (ModuleCat R) ℕ)
    {i j : ℕ} (h : i = j) (r : R) (x : K.X i) :
    Work.SSSR.castElem K h (r • x) = r • Work.SSSR.castElem K h x := by
  subst h; simp [Work.SSSR.castElem]

/-- Two successive transports along mutually inverse degree equalities cancel. -/
lemma castElem_castElem_self {R : Type} [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j) (h' : j = i) (x : K.X i) :
    Work.SSSR.castElem K h' (Work.SSSR.castElem K h x) = x := by
  rw [Work.SSSR.StepAux.castElem_trans, Work.SSSR.StepAux.castElem_irrel (h.trans h') rfl x]
  simp [Work.SSSR.castElem]

/-- The naturality of the degree transport for a chain map, in the `ModuleCat.Hom.hom` spelling. -/
lemma castElem_map_hom {R : Type} [CommRing R] [Nontrivial R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {i j : ℕ} (h : i = j) (x : K.X i) :
    Work.SSSR.castElem L h ((ModuleCat.Hom.hom (φ.f i)) x)
      = (ModuleCat.Hom.hom (φ.f j)) (Work.SSSR.castElem K h x) :=
  Work.SSSR.StepAux.castElem_map φ h x

/-- The integer multiple `(-1)^n • x` is the `R`-multiple `(-1)^n • x`. -/
lemma zsmul_neg_one_pow_eq (R : Type) [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) : ((-1 : ℤ)^n) • x = ((-1 : R)^n) • x := by
  rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ)^n) x, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-! ## Cycles and homology classes -/

/-- The inclusion of the cycles, postcomposed with the differential, is zero. -/
lemma iCycles_d_eq_zero {R : Type} [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : K.cycles n) :
    (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) (K.iCycles n z) = 0 := by
  have h := congrArg (fun (g : K.cycles n ⟶ K.X ((ComplexShape.down ℕ).next n)) =>
    (ModuleCat.Hom.hom g) z)
    (HomologicalComplex.iCycles_d (K := K) n ((ComplexShape.down ℕ).next n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  exact h

/-- The class of the underlying element of a cycle is the class of the cycle. -/
lemma chainClass_eq_homologypi {R : Type} [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : K.cycles n)
    (hz : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) (K.iCycles n z) = 0) :
    Work.Pi6.MSSK.chainClass R K n (K.iCycles n z) hz = K.homologyπ n z := by
  rw [Work.Pi6.MSSK.chainClass]
  congr 1
  exact (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles K n)).mp inferInstance
    (Work.SSSR.iCycles_cyclesMk_C K (K.iCycles n z) rfl hz)

/-! ## The peel datum -/

/-- The degree equalities used when transporting the peel datum. -/
lemma castC (t k : ℕ) : (t+1) + k = t + (k+1) := by omega
lemma castD (t k : ℕ) : t + k = (t+1) + k - 1 := by omega
lemma castE (t k : ℕ) : (t+1) + k - 1 = t + k := by omega

/-- The value of the last-face chain on the peeling chain. -/
abbrev LFval (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) {t k : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w' : (TCC R p (CategoryTheory.CategoryStruct.comp
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).X (t + k)) :
    (BCC R p σ).X (t + k) :=
  (ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f (t + k))) w'

/-- **The peel datum**: the relative-cycle hypothesis and the horn-quotient peeling identity produce
an explicit horn correction at degree `t+k`, in the shape consumed by `capEdgeIdentity`. -/
lemma peelDatum_local (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B))
    {t k : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (TCC R p σ).X ((t+1) + k))
    (hrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d ((t+1) + k)
        ((t+1) + k - 1)))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1) + k))) c) = 0)
    (w' : (TCC R p (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)).X (t + k))
    (hpeel : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)))
        (((TCC R p σ).d ((t+1) + k) ((t+1) + k - 1)).hom c)
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f
                ((t+1) + k - 1)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f
                  ((t+1) + k - 1)))
                (Work.SSSR.castElem (TCC R p
                    (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
                  (by omega : t + k = (t+1) + k - 1) w')))) :
    ∃ yy : (HCC R p σ).X (t + k),
      (ModuleCat.Hom.hom ((TCC R p σ).d (t + (k+1)) (t + k)))
          (Work.SSSR.castElem (TCC R p σ) (castC t k) c)
        = (-1 : R)^(t+1) •
            (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f (t + k))
              (ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f (t + k)) w'))
          + (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f (t + k)) yy) := by
  classical
  dsimp only [TCC, BCC, HCC] at *
  have h1 : t + k = (t+1) + k - 1 := castD t k
  have hD : (t+1) + k - 1 = t + k := castE t k
  have hc : (t+1) + k = t + (k+1) := castC t k
  -- the boundary lift of `∂c`
  obtain ⟨y, hy⟩ := Peel.exists_lift_of_cokernel_cycle_K R
    (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ) ((t+1) + k) c hrel
  -- the element of `C(∂T_σ)` whose horn class vanishes
  have hzx : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f
      ((t+1) + k - 1)))
      ((Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)
        (y - ((-1 : ℤ)^(t+1)) • Work.SSSR.castElem (BCC R p σ) h1 (LFval R p σ w'))) = 0 := by
    simp only [map_sub, map_zsmul]
    rw [hy, hpeel]
    rw [← castElem_map_hom
      (Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ) h1 w']
    rw [zsmul_neg_one_pow_eq R]
    abel
  -- lift through the horn inclusion
  have hmem : (ModuleCat.Hom.hom ((cokernel.π (Work.SSSR.sCCMap R
      (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι)).f ((t+1) + k - 1)))
      ((Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)
        (y - ((-1 : ℤ)^(t+1)) • Work.SSSR.castElem (BCC R p σ) h1 (LFval R p σ w'))) = 0 := by
    rw [Work.SSSR.sCCMap_pieceHorn_ι_eq (R := R) (Work.SSSR.sSingP p) σ]
    exact hzx
  obtain ⟨yyC, hyyC⟩ := Work.Pi6.MSSK.exists_lift_of_cokernel_π_f_eq_zero
    (Work.SSSR.sCCMap R (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι) hmem
  -- the peeled identity at degree `(t+1)+k-1`
  have hpeelD : (TCC R p σ).d ((t+1) + k) ((t+1) + k - 1) c
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
            (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f ((t+1) + k - 1))) yyC
        + ((-1 : ℤ)^(t+1)) • (ModuleCat.Hom.hom
            ((Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1))
            (Work.SSSR.castElem (BCC R p σ) h1 (LFval R p σ w'))) := by
    rw [← hy, hyyC]
    have hZ : y = (y - ((-1 : ℤ)^(t+1)) • Work.SSSR.castElem (BCC R p σ) h1 (LFval R p σ w'))
        + ((-1 : ℤ)^(t+1)) • Work.SSSR.castElem (BCC R p σ) h1 (LFval R p σ w') := by abel
    nth_rewrite 1 [hZ]
    rw [map_add, map_zsmul]
  -- assemble at degree `t+k`
  refine ⟨Work.SSSR.castElem (HCC R p σ) hD yyC, ?_⟩
  have hcast := congrArg (Work.SSSR.castElem (TCC R p σ) hD) hpeelD
  rw [castElem_add, Work.SSSR.StepAux.castElem_zsmul] at hcast
  rw [← castElem_d_gen (TCC R p σ) hc hD c] at hcast
  rw [castElem_map_hom (Work.SSSR.sCCMap R
      (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι) hD yyC] at hcast
  rw [← castElem_map_hom (Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ) h1
      (LFval R p σ w')] at hcast
  rw [castElem_castElem_self (TCC R p σ) h1 hD
      (ModuleCat.Hom.hom ((Work.SSSR.TIncl (R := R) (Work.SSSR.sSingP p) σ).f (t + k))
        (LFval R p σ w'))] at hcast
  have hAA : (ModuleCat.Hom.hom ((TCC R p σ).d (t + (k+1)) (t + k)))
        (Work.SSSR.castElem (TCC R p σ) (by omega : (t+1) + k = t + (k+1)) c)
      = (ModuleCat.Hom.hom ((TCC R p σ).d (t + (k+1)) (t + k)))
        (Work.SSSR.castElem (TCC R p σ) hc c) := by
    congr 1
  exact hAA.trans (hcast.trans (by
    dsimp only [LFval, HCC, BCC, TCC]
    refine (add_comm _ _).trans ?_
    exact congrArg (fun z => z + _) (zsmul_neg_one_pow_eq R (t + 1) _)))


/-- The class `chainClass` only depends on the underlying element, not on the chosen cycle
certificate. -/
lemma chainClass_proof_irrel {R : Type} [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (x : K.X n)
    (hx hx' : (ModuleCat.Hom.hom (K.d n ((ComplexShape.down ℕ).next n))) x = 0) :
    Work.Pi6.MSSK.chainClass R K n x hx = Work.Pi6.MSSK.chainClass R K n x hx' := by
  have h : K.cyclesMk x ((ComplexShape.down ℕ).next n) rfl hx
      = K.cyclesMk x ((ComplexShape.down ℕ).next n) rfl hx' :=
    (ModuleCat.mono_iff_injective (HomologicalComplex.iCycles K n)).mp inferInstance
      rfl
  exact congrArg (K.homologyπ n) h

/-- The elementwise form of the defining property of `triv`. -/
lemma triv_transport_apply {R : Type} [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    (k : ℕ) {b b' : B} (γ : Path b b')
    (y : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) k) :
    (Work.SSSR.triv p e₀ hfib hsconn k b').hom.hom
        ((Work.SSSR.transportIsoPath p hfib γ k).hom y)
      = (Work.SSSR.triv p e₀ hfib hsconn k b).hom.hom y := by
  rw [← Work.SSSR.triv_transport (R := R) p e₀ hfib hsconn k γ]
  simp only [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]

/-! ## The spelling of the vertex pieces -/

/-- `triv` and `vertexIso` are insensitive to the spelling of the vertex map. -/
lemma triv_vertexIso_transport {R : Type} [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    (k : ℕ)
    {σ σ' : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : σ' = σ)
    (x : (TCC R p σ').cycles k) :
    (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
            (Work.Pi6.MSSK.vertexIso p σ).hom) k))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
              (CategoryTheory.eqToHom (congrArg
                (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) h))) k))
            ((ModuleCat.Hom.hom ((TCC R p σ').homologyπ k)) x)))
      = (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ')).hom.hom
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
            (Work.Pi6.MSSK.vertexIso p σ').hom) k))
          ((ModuleCat.Hom.hom ((TCC R p σ').homologyπ k)) x)) := by
  dsimp only [TCC] at *
  cases h
  simp

/-- The path along the last edge, in the `firstV`/`lastV 1` spelling of the two vertices. -/
lemma lastPathExists' (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∃ γ : Path (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.firstV 1)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)))
        (Work.SSSR.sigmaVert (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV 1)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))),
      (Work.SSSR.sSingP γ.toContinuousMap).app (Opposite.op (SimplexCategory.mk 1)) Work.SSSR.lambda1
        = Work.Pi6.MSSK.lastEdgeSimplex t σ := by
  obtain ⟨γ, hγ⟩ := Work.Pi6.MSSK.lastPathExists (B := B) t σ
  refine ⟨⟨γ.toContinuousMap, γ.source'.trans (Work.Pi6.MSSK.sigmaVertBridge0 σ).symm,
    γ.target'.trans (Work.Pi6.MSSK.sigmaVertBridge1 σ).symm⟩, hγ⟩

/-- The transport of a cycle of the `σ'`-piece to the `σ`-piece through an equality of the vertex
maps is again a cycle. -/
lemma sCCMap_eqToHom_cycle {R : Type} [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (k : ℕ)
    {σ σ' : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B}
    (h : σ' = σ)
    (z : (TCC R p σ').cycles k) :
    (ModuleCat.Hom.hom ((TCC R p σ).d k ((ComplexShape.down ℕ).next k)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
          (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) h))).f k))
        ((ModuleCat.Hom.hom ((TCC R p σ').iCycles k)) z)) = 0 := by
  dsimp only [TCC] at *
  rw [Work.Pi6.MSSK.sCCMap_d_apply]
  rw [Work.Pi6.MSSK.iCycles_d_eq_zero]
  simp

theorem edgePieceTransport (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    {t k : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((t+1) + k))
    (hrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d ((t+1) + k)
        ((t+1) + k - 1)))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f ((t+1) + k))) c) = 0)
    (w' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).X (t + k))
    (hpeel : (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)))
        (((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d ((t+1) + k) ((t+1) + k - 1)).hom c)
      = (-1 : ℤ)^(t+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (R := R) (Work.SSSR.sSingP p) σ).f ((t+1) + k - 1)))
            (((Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι).f ((t+1) + k - 1))
              ((Work.SSSR.lastFaceChain (R := R) (Work.SSSR.sSingP p) t σ).f ((t+1) + k - 1)
                (Work.SSSR.castElem (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                    (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))
                  (by omega : t + k = (t+1) + k - 1) w'))))
    (z'' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))).cycles k)
    (hz'' : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
        (Work.Pi6.MSSK.fibreInc p (CategoryTheory.CategoryStruct.comp
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).f k)
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))).iCycles k)) z''))
      = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
          (Work.Pi6.MSSK.thetaTop R p (CategoryTheory.CategoryStruct.comp
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) k w') :
    ∃ z' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ))).cycles k,
      (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ))).iCycles k)) z'))
        = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop R p σ) k c
      ∧ (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ))).hom.hom
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
            (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp
              (Work.Pi6.MSSK.lastV (t+1)) σ)).hom) k))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV (t+1)) σ))).homologyπ k)) z'))
        = (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert
            (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
              (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))).hom.hom
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
            (Work.Pi6.MSSK.vertexIso p (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
              (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))).hom) k))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastV t)
                (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)))).homologyπ k)) z'')) := by
  classical
  -- ## Step 1: the peeled horn correction
  obtain ⟨yy, hyy⟩ := peelDatum_local R p σ c hrel w' hpeel
  -- ## Step 2: the cap-edge identity at degree `k`
  obtain ⟨ye, hye⟩ := Work.Pi6.MSSK.capLastFaceTop_edgeIncl R p σ
      (Work.SSSR.castElem (TCC R p σ) (castC t k) c)
  have hcapEdge := Work.Pi6.MSSK.capEdgeIdentity R p σ
      (Work.SSSR.castElem (TCC R p σ) (castC t k) c) w' ⟨yy, hyy⟩
  have hcE : Work.SSSR.castElem (TCC R p σ) (by omega : t + (k+1) = (t+1) + k)
        (Work.SSSR.castElem (TCC R p σ) (castC t k) c) = c := by
    rw [Work.SSSR.StepAux.castElem_trans, Work.SSSR.StepAux.castElem_irrel _ rfl]
    simp [Work.SSSR.castElem]
  rw [hcE] at hcapEdge
  have hcap : Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.lastFaceMapAlong p σ)).f k))
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
            (CategoryTheory.CategoryStruct.comp (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ))
            (Work.Pi6.MSSK.thetaTop R p (CategoryTheory.CategoryStruct.comp
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) σ)) k w')
        + (ModuleCat.Hom.hom ((TCC R p σ).d (k+1) k))
            (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
              (Work.Pi6.MSSK.lastFaceTop R p σ) (k+1)
              (Work.SSSR.castElem (TCC R p σ) (castC t k) c)) := by
    have h1 := sub_eq_iff_eq_add.mp hcapEdge
    rw [h1]
    abel
  -- ## Step 3: the chain `Z1 = eV0_*(z'') + ∂ ye` of the edge piece
  have hZ1a : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f k))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex0Incl p σ)).f k))
          ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z''))
      = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.lastFaceMapAlong p σ)).f k))
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
            (Work.Pi6.MSSK.thetaTop R p (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) k w') := by
    rw [Work.SSSR.StepAux.sCCMap_comp_apply, Work.Pi6.MSSK.edgeVertex0Incl_edgeIncl]
    rw [show Work.Pi6.MSSK.lastFaceMapAlong p σ
        = Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ from rfl]
    rw [← Work.SSSR.StepAux.sCCMap_comp_apply]
    rw [hz'']
  have hZ1b : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f k))
        ((ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye)
      = (ModuleCat.Hom.hom ((TCC R p σ).d (k+1) k))
          (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.lastFaceTop R p σ) (k+1)
            (Work.SSSR.castElem (TCC R p σ) (castC t k) c)) := by
    rw [← Work.Pi6.MSSK.sCCMap_d_apply R (Work.Pi6.MSSK.edgeIncl p σ) (k+1) k]
    rw [hye]
  have hZ1 : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f k))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex0Incl p σ)).f k))
            ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')
          + (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye)
      = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.thetaTop R p σ) k c := by
    rw [map_add, hZ1a, hZ1b, ← hcap]
  have hZ1cyc : (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d k ((ComplexShape.down ℕ).next k)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex0Incl p σ)).f k))
          ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')
        + (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye) = 0 := by
    rw [map_add]
    rw [Work.Pi6.MSSK.sCCMap_d_apply R (edgeVertex0Incl p σ) k ((ComplexShape.down ℕ).next k)]
    rw [Work.Pi6.MSSK.iCycles_d_eq_zero, map_zero, zero_add]
    have h2 : (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d k ((ComplexShape.down ℕ).next k)))
        ((ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye) = 0 := by
      have h := HomologicalComplex.d_comp_d (TCC R p (lastEdge t ≫ σ)) (k+1) k
        ((ComplexShape.down ℕ).next k)
      exact congrArg (fun (g : (TCC R p (lastEdge t ≫ σ)).X (k+1) ⟶
        (TCC R p (lastEdge t ≫ σ)).X ((ComplexShape.down ℕ).next k)) =>
          (ModuleCat.Hom.hom g) ye) h
    rw [h2]
  -- ## Step 4: the cycles
  have hcapcyc : (ModuleCat.Hom.hom ((TCC R p σ).d k ((ComplexShape.down ℕ).next k)))
      (Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (Work.Pi6.MSSK.thetaTop R p σ) k c) = 0 := by
    rw [← hZ1]
    rw [Work.Pi6.MSSK.sCCMap_d_apply R (Work.Pi6.MSSK.edgeIncl p σ) k ((ComplexShape.down ℕ).next k)]
    rw [hZ1cyc, map_zero]
  have hz' : (ModuleCat.Hom.hom ((TCC R p (lastV (t+1) ≫ σ)).d k ((ComplexShape.down ℕ).next k)))
      (Work.Pi6.MSSK.capThetaLift' R p σ k c) = 0 := by
    refine (Work.Pi6.MSSK.sCCMap_injective R (Work.Pi6.MSSK.fibreInc p σ)
      (Work.Pi6.MSSK.mono_fibreInc p σ) ((ComplexShape.down ℕ).next k)) ?_
    rw [map_zero]
    rw [← Work.Pi6.MSSK.sCCMap_d_apply R (Work.Pi6.MSSK.fibreInc p σ) k ((ComplexShape.down ℕ).next k)]
    rw [Work.Pi6.MSSK.fibreIncCapThetaLift R p σ k c]
    exact hcapcyc
  refine ⟨(TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
      ((ComplexShape.down ℕ).next k) rfl hz', ?_, ?_⟩
  · -- condition (1)
    rw [Work.SSSR.iCycles_cyclesMk_C]
    exact Work.Pi6.MSSK.fibreIncCapThetaLift R p σ k c
  · -- condition (2): the transport along the last edge
    obtain ⟨γ, hγ⟩ := lastPathExists' (B := B) p σ
    have hz0 : (ModuleCat.Hom.hom ((TCC R p (firstV 1 ≫ (lastEdge t ≫ σ))).d k
        ((ComplexShape.down ℕ).next k)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))).f k))
          ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')) = 0 :=
      sCCMap_eqToHom_cycle p k (hmap_edge0 σ).symm z''
    have hz1 : (ModuleCat.Hom.hom ((TCC R p (lastV 1 ≫ (lastEdge t ≫ σ))).d k
        ((ComplexShape.down ℕ).next k)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
          ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
            ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
              ((ComplexShape.down ℕ).next k) rfl hz'))) = 0 :=
      sCCMap_eqToHom_cycle p k (hmap_edge1 σ).symm
        ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
          ((ComplexShape.down ℕ).next k) rfl hz')
    have hz1conv : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
          ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
            ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
              ((ComplexShape.down ℕ).next k) rfl hz'))
        = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
          (Work.Pi6.MSSK.capThetaLift' R p σ k c) := by
      rw [Work.SSSR.iCycles_cyclesMk_C]
    have heV1 : (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex1Incl p σ)).f k))
          ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
            ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
              ((ComplexShape.down ℕ).next k) rfl hz'))
        = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex0Incl p σ)).f k))
              ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')
            + (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye := by
      refine (Work.Pi6.MSSK.sCCMap_injective R (Work.Pi6.MSSK.edgeIncl p σ)
        (Work.Pi6.MSSK.mono_edgeIncl p σ) k) ?_
      rw [Work.SSSR.StepAux.sCCMap_comp_apply, Work.Pi6.MSSK.edgeVertex1Incl_edgeIncl]
      rw [show (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k))
            ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
              ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
                ((ComplexShape.down ℕ).next k) rfl hz'))
          = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k))
            (Work.Pi6.MSSK.capThetaLift' R p σ k c) from by
        rw [Work.SSSR.iCycles_cyclesMk_C]]
      rw [Work.Pi6.MSSK.fibreIncCapThetaLift R p σ k c]
      exact hZ1.symm
    have hW0 : (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye
        = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx1Incl p σ)).f k))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
                (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
              ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
                ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
                  ((ComplexShape.down ℕ).next k) rfl hz')))
          - (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.vtx0Incl p σ)).f k))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
                (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))).f k))
              ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')) := by
      have h1 : (ModuleCat.Hom.hom ((TCC R p (lastEdge t ≫ σ)).d (k+1) k)) ye
          = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex1Incl p σ)).f k))
              (Work.Pi6.MSSK.capThetaLift' R p σ k c)
            - (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex0Incl p σ)).f k))
              ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'') := by
        rw [← show (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex1Incl p σ)).f k))
              ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
                ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
                  ((ComplexShape.down ℕ).next k) rfl hz'))
            = (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (edgeVertex1Incl p σ)).f k))
              (Work.Pi6.MSSK.capThetaLift' R p σ k c) from by
          rw [Work.SSSR.iCycles_cyclesMk_C]]
        rw [heV1]; abel
      rw [h1]
      rw [← Work.Pi6.MSSK.vtx1Incl_eq_edgeVertex1Incl, ← Work.Pi6.MSSK.vtx0Incl_eq_edgeVertex0Incl]
      rw [← Work.SSSR.StepAux.sCCMap_comp_apply, ← Work.SSSR.StepAux.sCCMap_comp_apply]
      rw [← hz1conv]
    have htrans := Work.Pi6.MSSK.edgeTransportChain R p hfib σ γ hγ
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
          (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))).f k))
        ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z''))
      hz0
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
          (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
          ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
            ((ComplexShape.down ℕ).next k) rfl hz')))
      hz1 ye hW0
    -- convert the two `chainClass`-spellings
    have hL : Work.Pi6.MSSK.chainClass R (TCC R p (firstV 1 ≫ (lastEdge t ≫ σ))) k
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
              (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))).f k))
            ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')) hz0
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
              (CategoryTheory.eqToHom (congrArg
                (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))) k))
            ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).homologyπ k)) z'') := by
      rw [← Work.Pi6.MSSK.homologyMap_chainClass R (Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))) k
        (HomologicalComplex.iCycles (TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))) k z'')
        (Work.Pi6.MSSK.iCycles_d_eq_zero (TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))) k z'')
        hz0]
      rw [Work.Pi6.MSSK.chainClass_eq_homologypi (TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))) k z''
        (Work.Pi6.MSSK.iCycles_d_eq_zero (TCC R p (lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))) k z'')]
    have hR : Work.Pi6.MSSK.chainClass R (TCC R p (lastV 1 ≫ (lastEdge t ≫ σ))) k
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
              (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))).f k))
            ((ModuleCat.Hom.hom (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k))
              ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
                ((ComplexShape.down ℕ).next k) rfl hz'))) hz1
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
              (CategoryTheory.eqToHom (congrArg
                (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))) k))
            ((ModuleCat.Hom.hom ((TCC R p (lastV (t+1) ≫ σ)).homologyπ k))
              ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
                ((ComplexShape.down ℕ).next k) rfl hz')) := by
      rw [← Work.Pi6.MSSK.homologyMap_chainClass R (Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
            (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge1 σ).symm))) k
        (HomologicalComplex.iCycles (TCC R p (lastV (t+1) ≫ σ)) k
          ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
            ((ComplexShape.down ℕ).next k) rfl hz'))
        (Work.Pi6.MSSK.iCycles_d_eq_zero (TCC R p (lastV (t+1) ≫ σ)) k
          ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
            ((ComplexShape.down ℕ).next k) rfl hz'))
        hz1]
      rw [Work.Pi6.MSSK.chainClass_eq_homologypi (TCC R p (lastV (t+1) ≫ σ)) k
        ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
          ((ComplexShape.down ℕ).next k) rfl hz')
        (Work.Pi6.MSSK.iCycles_d_eq_zero (TCC R p (lastV (t+1) ≫ σ)) k
          ((TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
            ((ComplexShape.down ℕ).next k) rfl hz'))]
    -- apply `triv`
    have htriv := congrArg (fun z => (Work.SSSR.triv p e₀ hfib hsconn k
      (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV 1 ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ)))).hom.hom z) htrans
    rw [Work.Pi6.MSSK.triv_transport_apply (R := R) p e₀ hfib hsconn k γ
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R
        (Work.Pi6.MSSK.vertexIso p (Work.Pi6.MSSK.firstV 1 ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ))).hom) k))
        (Work.Pi6.MSSK.chainClass R (TCC R p (Work.Pi6.MSSK.firstV 1 ≫
          (Work.Pi6.MSSK.lastEdge t ≫ σ))) k
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (CategoryTheory.eqToHom (congrArg
              (fun g => Work.SSSR.pullAlong (Work.SSSR.sSingP p) g) (hmap_edge0 σ).symm))).f k))
            ((ModuleCat.Hom.hom ((TCC R p (lastV t ≫
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).iCycles k)) z'')) hz0))] at htriv
    rw [hL, hR] at htriv
    rw [Work.Pi6.MSSK.triv_vertexIso_transport (R := R) (p := p) (e₀ := e₀) (hfib := hfib)
      (hsconn := hsconn) (k := k)
      (σ := Work.Pi6.MSSK.firstV 1 ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ))
      (σ' := Work.Pi6.MSSK.lastV t ≫ (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      (h := (hmap_edge0 σ).symm) (x := z'')] at htriv
    rw [Work.Pi6.MSSK.triv_vertexIso_transport (R := R) (p := p) (e₀ := e₀) (hfib := hfib)
      (hsconn := hsconn) (k := k)
      (σ := Work.Pi6.MSSK.lastV 1 ≫ (Work.Pi6.MSSK.lastEdge t ≫ σ))
      (σ' := Work.Pi6.MSSK.lastV (t+1) ≫ σ)
      (h := (hmap_edge1 σ).symm)
      (x := (TCC R p (lastV (t+1) ≫ σ)).cyclesMk (Work.Pi6.MSSK.capThetaLift' R p σ k c)
        ((ComplexShape.down ℕ).next k) rfl hz')] at htriv
    exact htriv.symm

end

end Work.Pi6.MSSK
