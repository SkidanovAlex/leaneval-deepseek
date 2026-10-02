import Mathlib
import Submission.Work.ThomBordism.GtdFlip.Flip
import Submission.Work.ThomBordism.Grassmann.deg8PathConnectedOG
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg
import Submission.Work.Thom.Mpun_natural_map
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.openThom_eq_zero_of_baseSet_rank
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.ThomBordism.GtdFlip.h0Glue
import Submission.Work.ThomBordism.GtdFlip.chartClassOgFlip
import Submission.Work.ThomBordism.GtdFlip.chartCoeffCompat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Work.ThomBordism.GtdFlip

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## The degree cast of a piece class

The degree cast `0 + n = n` of the Thom isomorphism is the only place where the elaborator has to
infer a motive involving the *bundle*, and it does so wrongly when the bundle depends on the degree
variable (`Work.TangentClasses.RealBundle.rank` and the degree coincide for the tautological
bundle).  The following wrapper fixes the motive once and for all. -/

/-- The degree cast of a class of a piece, with the bundle and the piece held fixed and with an
explicit motive (so that the elaborator never has to infer a motive mentioning the bundle). -/
def pieceCast {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} {Z : RealBundle B F ι} {W : Set B} {a b : ℕ} (h : a = b)
    (x : Work.Thom.PieceCoh Z W a) : Work.Thom.PieceCoh Z W b :=
  Eq.ndrec (motive := fun j => Work.Thom.PieceCoh Z W j) x h

/-- Negation commutes with the transport along an equality of degrees. -/
theorem eqRec_neg {α : Sort*} {β : α → Type*} [∀ a, AddCommGroup (β a)] {a b : α} (h : a = b)
    (x : β a) : h ▸ (-x) = -(h ▸ x) := by cases h; rfl

/-- The defining equation of `pieceCast` (a `▸`-caste with the same motive). -/
theorem pieceCast_eq {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} {Z : RealBundle B F ι} {W : Set B} {a b : ℕ} (h : a = b)
    (x : Work.Thom.PieceCoh Z W a) :
    pieceCast h x = (h ▸ x : Work.Thom.PieceCoh Z W b) := rfl

/-! ## Abbreviations for the tautological bundle -/

/-- The tautological oriented bundle. -/
abbrev Gamma (k m : ℕ) := Grassmann.tautologicalBundle k m

/-- The tautological Thom class, as a class of the Thom pair. -/
abbrev Tau (k m : ℕ) : Work.Thom.OpenThom (Gamma k m) k :=
  (Grassmann.tautologicalThomClass k m).τ

/-- The zero complement of the tautological bundle. -/
abbrev Zc (k m : ℕ) : Set (Gamma k m).TotalSpace :=
  Work.Thom.zeroComplement (Gamma k m)

/-- The zero complement of a piece of the tautological bundle. -/
abbrev Pz (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    Set ↥((Gamma k m).proj ⁻¹' Grassmann.baseSet S) :=
  Work.Thom.pieceZero (Gamma k m) (Grassmann.baseSet S)

/-- The explicit chart class of the tautological bundle over the (full) chart cell. -/
abbrev ChartCoh (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    Work.Thom.PieceCoh (Gamma k m) (Grassmann.baseSet S) k :=
  Work.Thom.chartCoh (Gamma k m) k (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S
    (Grassmann.baseSet S) subset_rfl

/-- The local model class `π^*(x) ⌣ chartCoh` in degree `k` (with the degree cast `0 + k = k`
already applied). -/
abbrev LocModel (k m : ℕ) (S : Grassmann.ChartIdx k m) (d : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet S)) :
    Work.Thom.PieceCoh (Gamma k m) (Grassmann.baseSet S) k :=
  pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S)
    (ChartCoh k m S) 0 d)

/-- The rank of the tautological bundle. -/
theorem rank_taut (k m : ℕ) : (Grassmann.tautologicalBundle k m).rank = k := by
  rw [Work.TangentClasses.RealBundle.rank]
  simp [Grassmann.tautologicalBundle, Grassmann.Amb]

/-! ## The restriction of the flip to the pieces -/

/-- **Restriction of the flipped Thom class to a chart piece.** -/
theorem pieceRes_ogFlip (k m : ℕ) (S : Grassmann.ChartIdx k m) (τ : Work.Thom.OpenThom (Gamma k m) k) :
    (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom
        ((Work.Thom.relCohMap (Grassmann.ogFlipTotal k m)
          (Zc k m) (Zc k m) (Grassmann.ogFlipTotal_mem k m) ℤ k).hom τ)
      = (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
          (Pz k m S) (Pz k m S)
          (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom
          ((Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom τ) := by
  have hZ : (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k)
      = Work.Thom.relCohMap
          (Work.Thom.subtypeMap
            ((Gamma k m).proj ⁻¹' Grassmann.baseSet S))
          (Pz k m S) (Zc k m) (fun _ hp => hp) ℤ k := rfl
  rw [hZ]
  erw [Work.Thom.relCohMap_compA_apply
    (Pz k m S) (Zc k m) (Zc k m)
    (Work.Thom.subtypeMap ((Gamma k m).proj ⁻¹' Grassmann.baseSet S))
    (Grassmann.ogFlipTotal k m) (fun _ hp => hp) (Grassmann.ogFlipTotal_mem k m)
    (fun p hp => Grassmann.ogFlipTotal_mem k m _ hp) ℤ k τ]
  erw [Work.Thom.relCohMap_congrA
    (Pz k m S) (Zc k m)
    (Grassmann.subtypeMap_comp_ogFlipPiece k m S).symm
    (fun p hp => Grassmann.ogFlipTotal_mem k m _ hp)
    (fun p hp => Grassmann.ogFlipTotal_mem k m _ hp) ℤ k]
  erw [← Work.Thom.relCohMap_compA_apply
    (Pz k m S) (Pz k m S) (Zc k m)
    (Grassmann.ogFlipPiece k m S)
    (Work.Thom.subtypeMap ((Gamma k m).proj ⁻¹' Grassmann.baseSet S))
    (Grassmann.ogFlipPiece_mem k m S) (fun _ hp => hp)
    (fun p hp => Grassmann.ogFlipTotal_mem k m (p : (Gamma k m).TotalSpace) hp) ℤ k τ]
  rfl

/-! ## The flip acts trivially on the orientation coefficient -/

/-- **The flip fixes every degree-zero class** on the path-connected oriented Grassmannian. -/
theorem CohMap_ogFlipCM_eq (k m : ℕ) (hm : 1 ≤ m) (ε : Work.Thom.Coh ℤ 0 (Grassmann.OG k m)) :
    (Work.Thom.CohMap (Grassmann.ogFlipCM k m) ℤ 0).hom ε = ε := by
  haveI := Grassmann.deg8PathConnectedOG k m hm
  refine Work.Thom.ptEv_ext (fun x => ?_)
  rw [Work.Thom.ptEv_pullback]
  exact Work.Thom.ptEv_eq_of_joined (PathConnectedSpace.joined (Grassmann.ogFlipCM k m x) x) ε


/-! ## The flip of a chart -/

/-- The flip of the chart cell `baseSet S`. -/
noncomputable def chartFlip (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    C(↥(Grassmann.baseSet S), ↥(Grassmann.baseSet S)) :=
  ⟨fun x => ⟨Grassmann.ogFlip k m x.1, (Grassmann.ogFlip_mem_baseSet_iff S x.1).mpr x.2⟩,
    Continuous.subtype_mk ((Grassmann.continuous_ogFlip k m).comp continuous_subtype_val)
      (fun x => (Grassmann.ogFlip_mem_baseSet_iff S x.1).mpr x.2)⟩

theorem chartFlip_apply (k m : ℕ) (S : Grassmann.ChartIdx k m) (x : ↥(Grassmann.baseSet S)) :
    ((chartFlip k m S x : ↥(Grassmann.baseSet S)) : Grassmann.OG k m) = Grassmann.ogFlip k m x.1 :=
  rfl

/-- The projection of the flipped piece is the flip of the projected point. -/
theorem pieceProj_comp_ogFlipPiece (k m : ℕ) (S : Grassmann.ChartIdx k m) :
    (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)).comp (Grassmann.ogFlipPiece k m S)
      = (chartFlip k m S).comp
        (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)) := by
  apply ContinuousMap.ext
  intro p
  exact Subtype.ext rfl

/-- The flip of a chart cell does not change the value of a global degree-zero class. -/
theorem CohMap_chartFlip_eq (k m : ℕ) (hm : 1 ≤ m) (S : Grassmann.ChartIdx k m)
    (ε : Work.Thom.Coh ℤ 0 (Grassmann.OG k m)) :
    (Work.Thom.CohMap (chartFlip k m S) ℤ 0).hom
        ((Work.Thom.CohMap (Work.Thom.subtypeMap (Grassmann.baseSet S)) ℤ 0).hom ε)
      = (Work.Thom.CohMap (Work.Thom.subtypeMap (Grassmann.baseSet S)) ℤ 0).hom ε := by
  have hcomp : (Work.Thom.subtypeMap (Grassmann.baseSet S)).comp (chartFlip k m S)
      = (Grassmann.ogFlipCM k m).comp (Work.Thom.subtypeMap (Grassmann.baseSet S)) := by
    apply ContinuousMap.ext
    intro x
    show Grassmann.ogFlip k m x.1 = Grassmann.ogFlip k m x.1
    rfl
  rw [Work.Thom.CohMap_comp_apply (chartFlip k m S)
    (Work.Thom.subtypeMap (Grassmann.baseSet S)) ℤ 0 ε]
  rw [hcomp]
  rw [← Work.Thom.CohMap_comp_apply (Work.Thom.subtypeMap (Grassmann.baseSet S))
    (Grassmann.ogFlipCM k m) ℤ 0 ε]
  rw [CohMap_ogFlipCM_eq k m hm ε]

/-! ## The local computation: the flip of the chart model class is minus it -/

/-- **The flip of the local model class** `π^*d ⌣ chartCoh` is minus it: this is the chartwise
flip identity (`hchart`, the explicit computation `Work.ThomBordism.GtdFlip.chartClassOgFlip`),
together with the fact that the flip fixes the degree-zero coefficient `d` (`hflipd`). -/
theorem piece_flip_model (k m : ℕ) (S : Grassmann.ChartIdx k m)
    (hchart : (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
        (Pz k m S) (Pz k m S) (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom
        ((Work.Thom.localThomOfChart (Gamma k m) k
          (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S (Grassmann.baseSet S)
          subset_rfl).τ)
      = -((Work.Thom.localThomOfChart (Gamma k m) k
          (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S (Grassmann.baseSet S)
          subset_rfl).τ))
    (d : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet S))
    (hflipd : (Work.Thom.CohMap (chartFlip k m S) ℤ 0).hom d = d) :
    (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
        (Pz k m S) (Pz k m S) (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom (LocModel k m S d)
      = -(LocModel k m S d) := by
  -- split off the degree cast
  have hcast : (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
        (Pz k m S) (Pz k m S) (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom (LocModel k m S d)
      = pieceCast (Nat.zero_add k) ((Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
        (Pz k m S) (Pz k m S) (Grassmann.ogFlipPiece_mem k m S) ℤ (0 + k)).hom
        (Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S) (ChartCoh k m S) 0 d)) :=
    Work.Thom.relCohMap_cast (Grassmann.ogFlipPiece k m S) (Pz k m S) (Pz k m S)
      (Grassmann.ogFlipPiece_mem k m S) (Nat.zero_add k)
      (Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S) (ChartCoh k m S) 0 d)
  rw [hcast]
  -- the degree `0 + k` computation
  have hlow : (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S)
        (Pz k m S) (Pz k m S) (Grassmann.ogFlipPiece_mem k m S) ℤ (0 + k)).hom
        (Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S) (ChartCoh k m S) 0 d)
      = -((Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S) (ChartCoh k m S) 0 d)) := by
    rw [Work.Thom.localThomMap_apply]
    rw [Work.Thom.mixedCupC_pairNatural (Grassmann.ogFlipPiece k m S) (Pz k m S) (Pz k m S)
      (Grassmann.ogFlipPiece_mem k m S) 0 k
      ((Work.Thom.CohMap (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)) ℤ 0).hom d)
      (ChartCoh k m S)]
    have hbase : (Work.Thom.CohMap (Grassmann.ogFlipPiece k m S) ℤ 0).hom
        ((Work.Thom.CohMap (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)) ℤ 0).hom d)
        = (Work.Thom.CohMap (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)) ℤ 0).hom d := by
      rw [Work.Thom.CohMap_comp_apply (Grassmann.ogFlipPiece k m S)
          (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S)) ℤ 0 d,
        pieceProj_comp_ogFlipPiece k m S,
        ← Work.Thom.CohMap_comp_apply (Work.Thom.pieceProj (Gamma k m) (Grassmann.baseSet S))
          (chartFlip k m S) ℤ 0 d,
        hflipd]
    rw [hbase, hchart, map_neg]
  rw [hlow]
  exact eqRec_neg (β := fun j => Work.Thom.PieceCoh (Gamma k m) (Grassmann.baseSet S) j)
    (Nat.zero_add k)
    (Work.Thom.localThomMap (Gamma k m) k (Grassmann.baseSet S) (ChartCoh k m S) 0 d)

/-! ## Compatibility of the chart coefficients, in the degree-cast shape -/

/-- **Compatibility of the chart coefficients of a Thom class on an overlap** (the degree-cast
`pieceCast` form of `Work.ThomBordism.GtdFlip.chartCoeffCompat`). -/
theorem chartCoeffCompat' {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F] (Z : RealBundle B F ι)
    {n : ℕ} (hrank : Z.rank = n) (hn : 1 ≤ n) (T : Work.Thom.ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι)
    (dS : Work.Thom.Coh ℤ 0 ↥(Z.baseSet i)) (dT : Work.Thom.Coh ℤ 0 ↥(Z.baseSet j))
    (hdS : (Work.Thom.PieceRes Z (Z.baseSet i) n).hom T.τ
      = pieceCast (Nat.zero_add n) (Work.Thom.localThomMap Z n (Z.baseSet i)
          (Work.Thom.chartCoh Z n e i (Z.baseSet i) subset_rfl) 0 dS))
    (hdT : (Work.Thom.PieceRes Z (Z.baseSet j) n).hom T.τ
      = pieceCast (Nat.zero_add n) (Work.Thom.localThomMap Z n (Z.baseSet j)
          (Work.Thom.chartCoh Z n e j (Z.baseSet j) subset_rfl) 0 dT))
    (hori : ∀ x : ↥(Z.baseSet i ∩ Z.baseSet j),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    ∀ x : ↥(Z.baseSet i ∩ Z.baseSet j),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ dS = Work.Thom.ptEv ⟨x.1, x.2.2⟩ dT := by
  refine chartCoeffCompat Z hrank hn T e i j dS dT ?_ ?_ hori
  · exact hdS
  · exact hdT

/-! ## The crux: the flip negates the tautological Thom class -/

/-- **The crux: the flip negates the tautological Thom class**, from the chartwise flip identity
(`hchart`, the explicit computation `Work.ThomBordism.GtdFlip.chartClassOgFlip`) and the
compatibility of the chart coefficients on overlaps (`hcompat`, obtained from
`Work.ThomBordism.GtdFlip.chartCoeffCompat`).  The class `z = Ψ^*(τ) + τ` vanishes on each chart
piece and hence globally. -/
theorem gtdFlip_crux_of (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hchart : ∀ S : Grassmann.ChartIdx k m,
      (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S) (Pz k m S) (Pz k m S)
        (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom
        ((Work.Thom.localThomOfChart (Gamma k m) k
          (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S (Grassmann.baseSet S)
          subset_rfl).τ)
      = -((Work.Thom.localThomOfChart (Gamma k m) k
          (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S (Grassmann.baseSet S)
          subset_rfl).τ))
    (hcompat : ∀ (S T : Grassmann.ChartIdx k m)
      (dS : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet S))
      (dT : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet T)),
      (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom (Tau k m)
        = pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k
            (Grassmann.baseSet S) (ChartCoh k m S) 0 dS) →
      (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet T) k).hom (Tau k m)
        = pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k
            (Grassmann.baseSet T) (ChartCoh k m T) 0 dT) →
      ∀ x : ↥(Grassmann.baseSet S ∩ Grassmann.baseSet T),
        Work.Thom.ptEv ⟨x.1, x.2.1⟩ dS = Work.Thom.ptEv ⟨x.1, x.2.2⟩ dT) :
    (Work.Thom.relCohMap (Grassmann.ogFlipTotal k m) (Zc k m) (Zc k m)
      (Grassmann.ogFlipTotal_mem k m) ℤ k).hom (Tau k m) = -(Tau k m) := by
  classical
  -- the chart coefficients of the Thom class
  choose d hd using fun S : Grassmann.ChartIdx k m =>
    Work.Thom.exists_coeff (Gamma k m) k (Grassmann.tautologicalThomClass k m)
      (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S subset_rfl
  have hd' : ∀ S : Grassmann.ChartIdx k m,
      (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom (Tau k m)
        = pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k
            (Grassmann.baseSet S) (ChartCoh k m S) 0 (d S)) := fun S => hd S
  -- they are compatible on overlaps
  have hcompat' : ∀ (S T : Grassmann.ChartIdx k m)
      (x : ↥(Grassmann.baseSet S ∩ Grassmann.baseSet T)),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ (d S) = Work.Thom.ptEv ⟨x.1, x.2.2⟩ (d T) :=
    fun S T x => hcompat S T (d S) (d T) (hd' S) (hd' T) x
  -- glue them into a global orientation coefficient
  obtain ⟨ε, hε⟩ := h0Glue (fun S : Grassmann.ChartIdx k m => Grassmann.baseSet S)
    (fun S => Grassmann.isOpen_baseSet S)
    (fun x => ⟨(Gamma k m).indexAt x, (Gamma k m).mem_baseSet_at x⟩) d hcompat'
  -- the local coefficients are the restrictions of `ε`
  have hdε : ∀ S : Grassmann.ChartIdx k m,
      d S = (Work.Thom.CohMap (Work.Thom.subtypeMap (Grassmann.baseSet S)) ℤ 0).hom ε := by
    intro S
    refine Work.Thom.ptEv_ext (fun x => ?_)
    exact (hε S x).symm
  -- the flip fixes `ε`, hence each local coefficient
  have hflipd : ∀ S : Grassmann.ChartIdx k m,
      (Work.Thom.CohMap (chartFlip k m S) ℤ 0).hom (d S) = d S := by
    intro S
    rw [hdε S, CohMap_chartFlip_eq k m hm S ε]
  -- `z := Ψ^*(τ) + τ` dies on every chart piece
  have hzero : (Work.Thom.relCohMap (Grassmann.ogFlipTotal k m) (Zc k m) (Zc k m)
      (Grassmann.ogFlipTotal_mem k m) ℤ k).hom (Tau k m) + (Tau k m) = 0 := by
    refine Work.Thom.openThom_eq_zero_of_baseSet_rank (Gamma k m) (rank_taut k m) hk _ ?_
    intro S
    change (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom
      ((Work.Thom.relCohMap (Grassmann.ogFlipTotal k m) (Zc k m) (Zc k m)
          (Grassmann.ogFlipTotal_mem k m) ℤ k).hom (Tau k m) + (Tau k m)) = 0
    have hz := pieceRes_ogFlip k m S (Tau k m)
    rw [map_add, hz]
    have hkey : (Work.Thom.relCohMap (Grassmann.ogFlipPiece k m S) (Pz k m S) (Pz k m S)
        (Grassmann.ogFlipPiece_mem k m S) ℤ k).hom
        ((Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom (Tau k m))
        = -((Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom (Tau k m)) := by
      rw [hd' S]
      exact piece_flip_model k m S (hchart S) (d S) (hflipd S)
    rw [hkey, neg_add_cancel]
  exact eq_neg_of_add_eq_zero_left hzero

/-! ## The chart coefficients for the tautological bundle -/

/-- **The coefficient compatibility for the tautological bundle**: the transition functions
`coordChangeO` are orientation preserving (`Work.ThomBordism.Grassmann.det_coordChangeO_pos`). -/
theorem chartCoeffCompat_taut (k m : ℕ) (hk : 1 ≤ k)
    (S T : Grassmann.ChartIdx k m)
    (dS : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet S))
    (dT : Work.Thom.Coh ℤ 0 ↥(Grassmann.baseSet T))
    (hdS : (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet S) k).hom (Tau k m)
      = pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k
          (Grassmann.baseSet S) (ChartCoh k m S) 0 dS))
    (hdT : (Work.Thom.PieceRes (Gamma k m) (Grassmann.baseSet T) k).hom (Tau k m)
      = pieceCast (Nat.zero_add k) (Work.Thom.localThomMap (Gamma k m) k
          (Grassmann.baseSet T) (ChartCoh k m T) 0 dT)) :
    ∀ x : ↥(Grassmann.baseSet S ∩ Grassmann.baseSet T),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ dS = Work.Thom.ptEv ⟨x.1, x.2.2⟩ dT := by
  refine chartCoeffCompat' (Gamma k m) (rank_taut k m) hk (Grassmann.tautologicalThomClass k m)
    (ContinuousLinearEquiv.refl ℝ (Grassmann.Amb k)) S T dS dT hdS hdT ?_
  intro x
  exact Grassmann.det_coordChangeO_pos S T (x : Grassmann.OG k m) x.2

/-! ## The crux, proved -/

/-- **The orientation flip negates the tautological Thom class** (for odd rank). -/
theorem gtdFlip_crux (k m : ℕ) (hodd : Odd k) (hm : 1 ≤ m) :
    (Work.Thom.relCohMap (Grassmann.ogFlipTotal k m) (Zc k m) (Zc k m)
      (Grassmann.ogFlipTotal_mem k m) ℤ k).hom (Tau k m) = -(Tau k m) := by
  have hk : 1 ≤ k := by
    rcases hodd with ⟨n, hn⟩
    omega
  refine gtdFlip_crux_of k m hk hm (fun S => ?_) (fun S T dS dT hdS hdT => ?_)
  · exact chartClassOgFlip k m hk S
  · exact chartCoeffCompat_taut k m hk S T dS dT hdS hdT


/-- **The flip lemma for arbitrary data, from the universal flip identity.** -/
theorem gtdThomClass_flipPairs_of_crux (k m : ℕ)
    (hcrux : (Work.Thom.relCohMap (Grassmann.ogFlipTotal k m) (Zc k m) (Zc k m)
        (Grassmann.ogFlipTotal_mem k m) ℤ k).hom (Tau k m) = -(Tau k m))
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (hodd : Odd k) (hm : 1 ≤ m)
    (gauss : C(B, Grassmann.OG k m))
    (Gplus : C(Z.TotalSpace, (Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp : ∀ p : Z.TotalSpace,
      (Grassmann.tautologicalBundle k m).proj (Gplus p) = gauss p.1)
    (Gminus : C(Z.TotalSpace, (Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp' : ∀ p : Z.TotalSpace,
      (Grassmann.tautologicalBundle k m).proj (Gminus p)
        = Grassmann.ogFlip k m (gauss p.1))
    (hvec : ∀ p : Z.TotalSpace,
      Grassmann.evalVec (Gminus p) = Grassmann.evalVec (Gplus p))
    (hmem : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gplus p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m))
    (hmem' : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gminus p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) :
    (Work.Thom.relCohMap Gminus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) hmem' ℤ k).hom
        (Grassmann.tautologicalThomClass k m).τ
      = -((Work.Thom.relCohMap Gplus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) hmem ℤ k).hom
        (Grassmann.tautologicalThomClass k m).τ) := by
  classical
  have hG : Gminus = (Grassmann.ogFlipTotal k m).comp Gplus := by
    apply ContinuousMap.ext
    intro p
    refine Grassmann.evalVec_injective_of_proj_eq ?_ ?_
    · show (Gminus p).1 = (Grassmann.ogFlipTotal k m (Gplus p)).1
      have h1 : (Grassmann.ogFlipTotal k m (Gplus p)).1 = Grassmann.ogFlip k m (gauss p.1) := by
        rw [Grassmann.ogFlipTotal_proj, ← hbp p]
      rw [h1, show (Gminus p).1 = Grassmann.ogFlip k m (gauss p.1) from hbp' p]
    · rw [ContinuousMap.comp_apply, Grassmann.ogFlipTotal_evalVec, hvec p]
  have hmemB : ∀ p ∈ Work.Thom.zeroComplement Z,
      (Grassmann.ogFlipTotal k m) (Gplus p)
        ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m) :=
    fun p hp => Grassmann.ogFlipTotal_mem k m _ (hmem p hp)
  have hL : (Work.Thom.relCohMap Gminus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) hmem' ℤ k).hom
        (Grassmann.tautologicalThomClass k m).τ
      = (Work.Thom.relCohMap ((Grassmann.ogFlipTotal k m).comp Gplus)
        (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) hmemB ℤ k).hom
        (Grassmann.tautologicalThomClass k m).τ :=
    congrArg (fun f => (ModuleCat.Hom.hom f) (Grassmann.tautologicalThomClass k m).τ)
      (Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) hG hmem' hmemB ℤ k)
  rw [hL]
  erw [← Work.Thom.relCohMap_compA_apply (Work.Thom.zeroComplement Z)
    (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m))
    (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k m)) Gplus
    (Grassmann.ogFlipTotal k m) hmem (Grassmann.ogFlipTotal_mem k m) hmemB ℤ k
    (Grassmann.tautologicalThomClass k m).τ]
  rw [hcrux, map_neg]

end

end Work.ThomBordism.GtdFlip
