import Mathlib
import Submission.Work.SSS.serreE1Psi
import Submission.Work.SSS.pieceBdryHornIso
import Submission.Work.SSS.ezSimplex_liftFam_coface
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.SSS.pieceContraction
import Submission.Work.SSS.pieceHornAcyclic
import Submission.Work.SSS.pieceConnectingIso

/-!
# Vocabulary for the comparison `ε_σ ∘ ι_σ = ±𝟙` (`Work.SSS.serreE1PieceIso_iota`)

This file collects the explicit objects intervening in the induction step of the proof that the
iterated last-face connecting map `ε_σ = Work.SSS.serreE1PieceIso` sends the class of the explicit
Eilenberg–Zilber cycle `ι_σ τ` to `±` the class of `τ`.

Everything is stated with the base point `b : B` as an explicit parameter, together with a proof
`h : Work.SSS.sigmaVert σ = b`; this is what allows the induction step to use the induction
hypothesis on the *last face* `d_lastσ` without transporting the cycle `τ` along the (propositional
but not definitional) equality `sigmaVert (d_lastσ) = sigmaVert σ`.

For `f : X ⟶ Y`, a simplex `σ : Δ[s] ⟶ Y` and `Λ = pieceHorn f σ ≤ ∂T_σ ≤ T_σ = Δ[s] ×_Y X`:

* `bdryIncl f σ : C(Λ) ⟶ C(∂T_σ)` and `TIncl f σ : C(∂T_σ) ⟶ C(T_σ)`;
* `hornCokπ f σ : C(T_σ) ⟶ C(T_σ)/C(Λ)`, spelled as the cokernel of the composite
  `bdryIncl ≫ TIncl` (so that it is definitionally the middle term of the short exact sequence used
  by `Work.SSS.pieceConnectingIso`);
* `bdryHornProj f σ : C(∂T_σ) ⟶ C(∂T_σ)/C(Λ)`;
* `iotaTLift p hfib P b σ h q τ`, the chain `ι_σ τ` *before* projecting to the σ-piece;
* `lastFaceChain f t σ : C(T_{d_lastσ}) ⟶ C(∂T_σ)`, the explicit pasting of the last face.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- Transport of an element of a chain complex along an equality of degrees. -/
def castElem (K : ChainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j) (x : K.X i) : K.X j :=
  h ▸ x

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The chain complex of the fibre of `p` over a point `b`, spelled once. -/
abbrev fibreCC (p : C(E, B)) (b : B) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))

/-- **The Eilenberg–Zilber lift `ι_σ τ` in `C(T_σ)`**, before projecting to the σ-piece. -/
def iotaTLift (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X (P + q) :=
  (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) P b σ h)).f (P + q)
    (Work.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
      (Work.SSS.sSing (Work.StemsB.fibre p b))
      (Work.SSS.stdIdSimplex P) τ)

/-- The inclusion `C(Λ) ⟶ C(∂T_σ)`. -/
abbrev bdryIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCC (Work.SSS.pieceHorn f σ) ⟶ Work.SSS.sCC (Work.SSS.bdryAlong f σ) :=
  Work.SSS.sCCMap (SSet.Subcomplex.homOfLE (Work.SSS.pieceHorn_le_bdryAlong f σ))

/-- The inclusion `C(∂T_σ) ⟶ C(T_σ)`. -/
abbrev TIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCC (Work.SSS.bdryAlong f σ) ⟶ Work.SSS.sCC (Work.SSS.pullAlong f σ) :=
  Work.SSS.sCCMap (Work.SSS.bdryAlong f σ).ι

/-- The quotient map `C(T_σ) ⟶ C(T_σ)/C(Λ)`, spelled through the composite
`C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`. -/
abbrev hornCokπ {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCC (Work.SSS.pullAlong f σ) ⟶
      cokernel (bdryIncl f σ ≫ TIncl f σ) :=
  cokernel.π (bdryIncl f σ ≫ TIncl f σ)

/-- The quotient map `C(∂T_σ) ⟶ C(∂T_σ)/C(Λ)`. -/
abbrev bdryHornProj {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCC (Work.SSS.bdryAlong f σ) ⟶ Work.SSS.pieceBdryHornC f σ :=
  cokernel.π (bdryIncl f σ)

/-- The horn inclusion into `C(T_σ)` is the composite `C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`. -/
lemma sCCMap_pieceHorn_ι_eq {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCCMap (Work.SSS.pieceHorn f σ).ι = bdryIncl f σ ≫ TIncl f σ := by
  rw [show (Work.SSS.pieceHorn f σ).ι =
      SSet.Subcomplex.homOfLE (Work.SSS.pieceHorn_le_bdryAlong f σ) ≫
        (Work.SSS.bdryAlong f σ).ι from
      Subfunctor.homOfLe_ι (Work.SSS.pieceHorn_le_bdryAlong f σ)]
  exact Work.SSS.sCCMap_comp' _ _

/-- The last face `pieceLastFace f σ` is contained in the boundary `∂T_σ`. -/
theorem pieceLastFace_le_bdryAlong {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSS.pieceLastFace f σ ≤ Work.SSS.bdryAlong f σ :=
  (Work.SSS.bdryAlong_eq_horn_sup_lastFace f t σ).symm ▸ le_sup_right

/-- **The explicit "last face" chain map `C(T_{d_lastσ}) ⟶ C(∂T_σ)`**: push a chain of the last face
`d_lastσ` into `T_σ` along the pasting map `Work.SSS.lastFaceMap`, then regard it in `C(∂T_σ)`. -/
def lastFaceChain {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSS.sCC (Work.SSS.pullAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) ⟶
      Work.SSS.sCC (Work.SSS.bdryAlong f σ) :=
  Work.SSS.sCCMap (SSet.Subcomplex.toRange (Work.SSS.lastFaceMap f t σ)) ≫
    Work.SSS.sCCMap (SSet.Subcomplex.homOfLE
      ((Work.SSS.range_lastFaceMap f t σ).symm ▸ pieceLastFace_le_bdryAlong f t σ))

/-- The last-face pasting map is `pullFaceIncl` in the last coface. -/
lemma lastFaceMap_eq_pullFaceIncl {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSS.lastFaceMap f t σ
      = Work.SSS.pullFaceIncl f σ (Fin.last (t+1)) := rfl

/-- The transport of the homology of the fibre chain complex along an equality of base points. -/
def fibreConj {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {b b' : B}
    (h : b = b') (q : ℕ) :
    (fibreCC p b).homology q ⟶ (fibreCC p b').homology q :=
  HomologicalComplex.homologyMap
    (eqToIso (congrArg (fun x : B => fibreCC p x) h)).hom q

lemma fibreConj_rfl {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b : B)
    (q : ℕ) : fibreConj p (rfl : b = b) q = 𝟙 ((fibreCC p b).homology q) := by
  simp [fibreConj]

lemma fibreConj_trans {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {b b' b'' : B} (h : b = b') (h' : b' = b'') (q : ℕ) :
    fibreConj p h q ≫ fibreConj p h' q = fibreConj p (h.trans h') q := by
  subst h; subst h'
  simp [fibreConj]

/-- `fibreConj` is the transport of the homology objects along the degree equality. -/
lemma fibreConj_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    {b b' : B} (h : b = b') (q : ℕ) :
    fibreConj p h q = (eqToIso (congrArg (fun x : B => (fibreCC p x).homology q) h)).hom := by
  subst h; simp [fibreConj]

/-! ## The successor decomposition of `serreE1PieceIso` -/

/-- The horn quotient complex `C(T_σ)/C(Λ)` is acyclic in all degrees for a simplex `σ : Δ[t+1]`
of dimension at least one.  This is the input used by `Work.SSS.pieceConnectingIso` in the
induction step of `Work.SSS.serreE1PieceIso`. -/
theorem pieceHornC_acyclic_succ {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    ∀ j : ℕ, IsZero ((Work.SSS.pieceHornC (Work.SSS.sSingP p) σ).homology j) := by
  have hcont := Work.SSS.pieceContraction p hfib (Nat.succ_le_succ (Nat.zero_le t)) σ
  obtain ⟨g, H, hspec⟩ := hcont
  exact fun j => ModuleCat.isZero_iff_subsingleton.mpr
    (Work.SSS.pieceHornAcyclic p σ g H hspec.1 hspec.2 j)

/-- **The induction step of `serreE1PieceIso`**, packaged: the iterated last-face connecting map in
degree `t+1+k` is the connecting map of the σ-descent, followed by the identification of the
boundary-over-horn quotient with the σ-piece of the last face, followed by the induction
hypothesis for `d_lastσ`. -/
noncomputable def serreE1PieceStep {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).homology (t+1+k) ≅
      (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)))).homology k :=
  Work.SSS.pieceConnectingIsoIso (Work.SSS.sSingP p) t σ (t+1+k) (by omega)
      (pieceHornC_acyclic_succ p hfib t σ _) (pieceHornC_acyclic_succ p hfib t σ _) ≪≫
    eqToIso (congrArg (fun m => (Work.SSS.pieceBdryHornC (Work.SSS.sSingP p) σ).homology m)
      (by omega : t+1+k-1 = t+k)) ≪≫
    HomologicalComplex.homologyMapIso
      (Work.SSS.pieceBdryHornIsoIso (Work.SSS.sSingP p) t σ) (t+k) ≪≫
    Work.SSS.serreE1PieceIso p hfib t k
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) ≪≫
    eqToIso (congrArg (fun x : B =>
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p x))).homology k)
      (Work.SSS.sigmaVert_face (Fin.last (t+1)) (by
        intro hh; have := congrArg Fin.val hh; simp [Fin.last] at this) σ))

/-- The packaged step is definitionally the induction step of `Work.SSS.serreE1PieceIso`. -/
theorem serreE1PieceIso_succ_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    serreE1PieceStep p hfib t k σ = Work.SSS.serreE1PieceIso p hfib (t+1) k σ := by
  simp only [Work.SSS.serreE1PieceIso.eq_def, Nat.recAux, serreE1PieceStep,
    pieceHornC_acyclic_succ]

end

end Work.SSS
