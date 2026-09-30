import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

/-!
# The sign spec of the σ-piece isomorphism `ε_σ = serreE1PieceIso`

`Work.SSS.iotaF_iota_comp_pieceIso` states that the iterated last-face connecting map
`ε_σ = Work.SSS.serreE1PieceIso p hfib n t σ` sends the class of `ι_σ z` to `c n` times the class
of `z`, for a dimension-dependent constant `c : ℕ → ℤ` with `c n = ±1`.  This file records that
specification as a named `Prop` (`Work.SSS.PieceAlpha`), together with its inverse form
`Work.SSS.PieceInv` (which is what the comparison of the first differential with
`∂ ⊗ id` actually uses), and proves that the two are equivalent given `c n = ±1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The sign spec of `ε_σ`.**  `PieceAlpha p hfib c` asserts that for every simplex `σ` of the
base of dimension `n`, every fibre chain `z` over `σ(v₀)` which is a cycle (with `ι_σ z` a cycle in
the σ-piece), the σ-piece isomorphism `ε_σ` sends the class of `ι_σ z` to `c n` times the class
of `z`. -/
def PieceAlpha (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (c : ℕ → ℤ) : Prop :=
  ∀ (n t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (z : (fibreCC p (sigmaVert σ)).X t)
    (hz : (ModuleCat.Hom.hom ((fibreCC p (sigmaVert σ)).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hy : (ModuleCat.Hom.hom ((pieceAlong (sSingP p) σ).d (n+t)
        ((ComplexShape.down ℕ).next (n+t))))
        ((ModuleCat.Hom.hom (iotaF p (liftFam p hfib) (liftFam_proj p hfib) n
          (sigmaVert σ) σ rfl t)) z) = 0),
    (ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).hom)
        ((pieceAlong (sSingP p) σ).homologyπ (n+t)
          ((pieceAlong (sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom (iotaF p (liftFam p hfib) (liftFam_proj p hfib) n
              (sigmaVert σ) σ rfl t)) z)
            ((ComplexShape.down ℕ).next (n+t)) rfl hy))
      = c n • ((fibreCC p (sigmaVert σ)).homologyπ t
          ((fibreCC p (sigmaVert σ)).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))

/-- **The inverse form of the sign spec.**  Same data, but the *inverse* `ε_σ⁻¹` of the σ-piece
isomorphism is applied to the class of `z`. -/
def PieceInv (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (c : ℕ → ℤ) : Prop :=
  ∀ (n t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (z : (fibreCC p (sigmaVert σ)).X t)
    (hz : (ModuleCat.Hom.hom ((fibreCC p (sigmaVert σ)).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (hy : (ModuleCat.Hom.hom ((pieceAlong (sSingP p) σ).d (n+t)
        ((ComplexShape.down ℕ).next (n+t))))
        ((ModuleCat.Hom.hom (iotaF p (liftFam p hfib) (liftFam_proj p hfib) n
          (sigmaVert σ) σ rfl t)) z) = 0),
    (ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv)
        ((fibreCC p (sigmaVert σ)).homologyπ t
          ((fibreCC p (sigmaVert σ)).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))
      = c n • ((pieceAlong (sSingP p) σ).homologyπ (n+t)
          ((pieceAlong (sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom (iotaF p (liftFam p hfib) (liftFam_proj p hfib) n
              (sigmaVert σ) σ rfl t)) z)
            ((ComplexShape.down ℕ).next (n+t)) rfl hy))

/-- `Work.SSS.iotaF_iota_comp_pieceIso`, packaged as the existence of a sign family satisfying the
spec `Work.SSS.PieceAlpha`. -/
theorem exists_pieceAlpha (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) :
    ∃ c : ℕ → ℤ, (∀ n : ℕ, c n = 1 ∨ c n = -1) ∧ PieceAlpha p hfib c :=
  iotaF_iota_comp_pieceIso p hfib

/-- Transport of an element of a graded piece `C(T_m)/C(∂T_m)` along an equality `h : m = m'` of
simplices of the base. -/
noncomputable def pieceCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (pieceAlong f m).X n) : (pieceAlong f m').X n :=
  eqToHom (congrArg (fun m => (pieceAlong f m).X n) h) x

/-- Transport of an element of the chains of a pullback `T_m` along an equality `h : m = m'` of
simplices of the base. -/
noncomputable def pullCastElem {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (sCC (pullAlong f m)).X n) : (sCC (pullAlong f m')).X n :=
  eqToHom (congrArg (fun m => (sCC (pullAlong f m)).X n) h) x

/-- The inverse form of the sign spec follows from the forward form, because `c n = ±1`. -/
theorem pieceInv_of_pieceAlpha (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (c : ℕ → ℤ) (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : PieceAlpha p hfib c) :
    PieceInv p hfib c := by
  intro n t σ z hz hy
  have h := hal n t σ z hz hy
  have hcc : c n * c n = 1 := by
    rcases hc1 n with h' | h' <;> rw [h'] <;> norm_num
  set zh : (fibreCC p (sigmaVert σ)).homology t :=
    (fibreCC p (sigmaVert σ)).homologyπ t
      ((fibreCC p (sigmaVert σ)).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz) with hzh
  set ph : (pieceAlong (sSingP p) σ).homology (n+t) :=
    (pieceAlong (sSingP p) σ).homologyπ (n+t)
      ((pieceAlong (sSingP p) σ).cyclesMk
        ((ModuleCat.Hom.hom (iotaF p (liftFam p hfib) (liftFam_proj p hfib) n
          (sigmaVert σ) σ rfl t)) z)
        ((ComplexShape.down ℕ).next (n+t)) rfl hy) with hph
  change ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh = c n • ph
  have hinv_hom : ∀ x : (pieceAlong (sSingP p) σ).homology (n+t),
      ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv
        (ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).hom x) = x := by
    intro x
    have hcomp := Iso.hom_inv_id (serreE1PieceIso p hfib n t σ)
    have hx := congrArg (fun (f : (pieceAlong (sSingP p) σ).homology (n+t) ⟶
      (pieceAlong (sSingP p) σ).homology (n+t)) => (ModuleCat.Hom.hom f) x) hcomp
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using hx
  have h6 : ph = c n • ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh := by
    calc ph = ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv
                (ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).hom ph) := (hinv_hom ph).symm
      _ = ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv (c n • zh) := by rw [h]
      _ = c n • ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh := map_zsmul _ _ _
  calc ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh
      = (c n * c n) • ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh := by
        rw [hcc, one_smul]
    _ = c n • (c n • ModuleCat.Hom.hom (serreE1PieceIso p hfib n t σ).inv zh) := by
        rw [smul_smul]
    _ = c n • ph := by rw [← h6]

end

end Work.SSS
