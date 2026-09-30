import Mathlib
import Submission.Work.SSSR.serreE1Psi
import Submission.Work.SSSR.pieceBdryHornIso
import Submission.Work.SSSR.ezSimplex_liftFam_coface
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.pieceContraction
import Submission.Work.SSSR.pieceHornAcyclic
import Submission.Work.SSSR.pieceConnectingIso
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- Transport of an element of a chain complex along an equality of degrees. -/
def castElem (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j) (x : K.X i) : K.X j :=
  h ▸ x

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The chain complex of the fibre of `p` over a point `b`, spelled once. -/
abbrev fibreCC (p : C(E, B)) (b : B) : ChainComplex (ModuleCat R) ℕ :=
  Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))

/-- **The Eilenberg–Zilber lift `ι_σ τ` in `C(T_σ)`**, before projecting to the σ-piece. -/
def iotaTLift (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (P + q) :=
  (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) P b σ h)).f (P + q)
    (Work.SSSR.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
      (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      (Work.SSSR.stdIdSimplex P) τ)

/-- The inclusion `C(Λ) ⟶ C(∂T_σ)`. -/
abbrev bdryIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCC R (Work.SSSR.pieceHorn f σ) ⟶ Work.SSSR.sCC R (Work.SSSR.bdryAlong f σ) :=
  Work.SSSR.sCCMap R (SSet.Subcomplex.homOfLE (Work.SSSR.pieceHorn_le_bdryAlong f σ))

/-- The inclusion `C(∂T_σ) ⟶ C(T_σ)`. -/
abbrev TIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCC R (Work.SSSR.bdryAlong f σ) ⟶ Work.SSSR.sCC R (Work.SSSR.pullAlong f σ) :=
  Work.SSSR.sCCMap R (Work.SSSR.bdryAlong f σ).ι

/-- The quotient map `C(T_σ) ⟶ C(T_σ)/C(Λ)`, spelled through the composite
`C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`. -/
abbrev hornCokπ {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong f σ) ⟶
      cokernel (bdryIncl f σ ≫ TIncl f σ) :=
  cokernel.π (bdryIncl f σ ≫ TIncl f σ)

/-- The quotient map `C(∂T_σ) ⟶ C(∂T_σ)/C(Λ)`. -/
abbrev bdryHornProj {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCC R (Work.SSSR.bdryAlong f σ) ⟶ Work.SSSR.pieceBdryHornC R f σ :=
  cokernel.π (bdryIncl f σ)

/-- The horn inclusion into `C(T_σ)` is the composite `C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`. -/
lemma sCCMap_pieceHorn_ι_eq {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCCMap R (Work.SSSR.pieceHorn f σ).ι = bdryIncl f σ ≫ TIncl f σ := by
  rw [show (Work.SSSR.pieceHorn f σ).ι =
      SSet.Subcomplex.homOfLE (Work.SSSR.pieceHorn_le_bdryAlong f σ) ≫
        (Work.SSSR.bdryAlong f σ).ι from
      Subfunctor.homOfLe_ι (Work.SSSR.pieceHorn_le_bdryAlong f σ)]
  exact Work.SSSR.sCCMap_comp' _ _

/-- The last face `pieceLastFace f σ` is contained in the boundary `∂T_σ`. -/
theorem pieceLastFace_le_bdryAlong {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSSR.pieceLastFace f σ ≤ Work.SSSR.bdryAlong f σ :=
  (Work.SSSR.bdryAlong_eq_horn_sup_lastFace f t σ).symm ▸ le_sup_right

/-- **The explicit "last face" chain map `C(T_{d_lastσ}) ⟶ C(∂T_σ)`**: push a chain of the last face
`d_lastσ` into `T_σ` along the pasting map `Work.SSSR.lastFaceMap`, then regard it in `C(∂T_σ)`. -/
def lastFaceChain {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSSR.sCC R (Work.SSSR.pullAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) ⟶
      Work.SSSR.sCC R (Work.SSSR.bdryAlong f σ) :=
  Work.SSSR.sCCMap R (SSet.Subcomplex.toRange (Work.SSSR.lastFaceMap f t σ)) ≫
    Work.SSSR.sCCMap R (SSet.Subcomplex.homOfLE
      ((Work.SSSR.range_lastFaceMap f t σ).symm ▸ pieceLastFace_le_bdryAlong f t σ))

/-- The last-face pasting map is `pullFaceIncl` in the last coface. -/
lemma lastFaceMap_eq_pullFaceIncl {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSSR.lastFaceMap f t σ
      = Work.SSSR.pullFaceIncl f σ (Fin.last (t+1)) := rfl

/-- The transport of the homology of the fibre chain complex along an equality of base points. -/
def fibreConj {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {b b' : B}
    (h : b = b') (q : ℕ) :
    (fibreCC (R := R) p b).homology q ⟶ (fibreCC p b').homology q :=
  HomologicalComplex.homologyMap
    (eqToIso (congrArg (fun x : B => fibreCC p x) h)).hom q

lemma fibreConj_rfl {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b : B)
    (q : ℕ) : fibreConj p (rfl : b = b) q = 𝟙 ((fibreCC (R := R) p b).homology q) := by
  simp [fibreConj]

lemma fibreConj_trans {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {b b' b'' : B} (h : b = b') (h' : b' = b'') (q : ℕ) :
    fibreConj (R := R) p h q ≫ fibreConj p h' q = fibreConj p (h.trans h') q := by
  subst h; subst h'
  simp [fibreConj]

/-- `fibreConj` is the transport of the homology objects along the degree equality. -/
lemma fibreConj_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {b b' : B} (h : b = b') (q : ℕ) :
    fibreConj p h q = (eqToIso (congrArg (fun x : B => (fibreCC (R := R) p x).homology q) h)).hom := by
  subst h; simp [fibreConj]

/-! ## The successor decomposition of `serreE1PieceIso` -/

/-- The horn quotient complex `C(T_σ)/C(Λ)` is acyclic in all degrees for a simplex `σ : Δ[t+1]`
of dimension at least one.  This is the input used by `Work.SSSR.pieceConnectingIso` in the
induction step of `Work.SSSR.serreE1PieceIso`. -/
theorem pieceHornC_acyclic_succ {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    ∀ j : ℕ, IsZero ((Work.SSSR.pieceHornC R (Work.SSSR.sSingP p) σ).homology j) := by
  have hcont := Work.SSSR.pieceContraction p hfib (Nat.succ_le_succ (Nat.zero_le t)) σ
  obtain ⟨g, H, hspec⟩ := hcont
  exact fun j => ModuleCat.isZero_iff_subsingleton.mpr
    (Work.SSSR.pieceHornAcyclic R p σ g H hspec.1 hspec.2 j)

/-- **The induction step of `serreE1PieceIso`**, packaged: the iterated last-face connecting map in
degree `t+1+k` is the connecting map of the σ-descent, followed by the identification of the
boundary-over-horn quotient with the σ-piece of the last face, followed by the induction
hypothesis for `d_lastσ`. -/
noncomputable def serreE1PieceStep {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homology (t+1+k) ≅
      (Work.SSSR.Cohomology.singularChains R
        (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)))).homology k :=
  Work.SSSR.pieceConnectingIsoIso (Work.SSSR.sSingP p) t σ (t+1+k) (by omega)
      (pieceHornC_acyclic_succ p hfib t σ _) (pieceHornC_acyclic_succ p hfib t σ _) ≪≫
    eqToIso (congrArg (fun m => (Work.SSSR.pieceBdryHornC R (Work.SSSR.sSingP p) σ).homology m)
      (by omega : t+1+k-1 = t+k)) ≪≫
    HomologicalComplex.homologyMapIso
      (Work.SSSR.pieceBdryHornIsoIso (Work.SSSR.sSingP p) t σ) (t+k) ≪≫
    Work.SSSR.serreE1PieceIso p hfib t k
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) ≪≫
    eqToIso (congrArg (fun x : B =>
      (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology k)
      (Work.SSSR.sigmaVert_face (Fin.last (t+1)) (by
        intro hh; have := congrArg Fin.val hh; simp [Fin.last] at this) σ))

/-- The packaged step is definitionally the induction step of `Work.SSSR.serreE1PieceIso`. -/
theorem serreE1PieceIso_succ_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    serreE1PieceStep (R := R) p hfib t k σ = Work.SSSR.serreE1PieceIso p hfib (t+1) k σ := by
  simp only [Work.SSSR.serreE1PieceIso.eq_def, Nat.recAux, serreE1PieceStep,
    pieceHornC_acyclic_succ]

end

end Work.SSSR
