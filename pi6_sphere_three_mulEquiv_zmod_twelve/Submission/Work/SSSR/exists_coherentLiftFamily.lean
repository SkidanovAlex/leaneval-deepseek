import Mathlib
import Submission.Work.SSSR.coherentLiftDefs
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.singularFibration
import Submission.Work.SSSR.anodyneIota0
import Submission.Work.SSSR.exists_hornGlue
import Submission.Work.SSSR.exists_lift_sHat
import Submission.Work.SSSR.coherentLiftR
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.sSingP_fibreIncl_comp
import Submission.Work.SSSR.hasLiftingProperty_whisker_horn
import Submission.Work.SSSR.ssetVertex_delta_apply
import Submission.Work.SSSR.vertInclR_whiskerLeft
import Submission.Work.SSSR.stdSimplex_delta_pred_castPred
import Submission.Work.SSSR.exists_hornGlue_tensor
import Submission.Work.SSSR.exists_rlevel_zero
import Submission.Work.SSSR.hcomp_of_rcoh
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSSR

/-- In a cartesian monoidal category, `f ⊗ₘ 𝟙 Z` is the whiskering of `f` by `Z`. -/
lemma tensorHom_id_eq_whiskerRight {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X Y Z : C} (f : X ⟶ Y) : (f ⊗ₘ 𝟙 Z) = f ▷ Z := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.whiskerRight_fst]
  · rw [CartesianMonoidalCategory.tensorHom_snd, CartesianMonoidalCategory.whiskerRight_snd,
      Category.comp_id]

/-- the junk value used off the based locus -/
def rjunk {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) (n : ℕ) : (sSing (Work.SSSR.StemsB.fibre p b') ⊗ stdSimp n) ⟶ sSing E :=
  SemiCartesianMonoidalCategory.fst _ _ ≫ sSingP (Work.SSSR.StemsB.fibreIncl p b')

/-- Uniqueness of a morphism out of the tensor of a horn with a fixed simplicial set, from its
restrictions to the faces. -/
theorem hornTensor_hom_ext {F Y : SSet.{0}} {n : ℕ} {i : Fin (n + 2)}
    (u u' : F ⊗ (SSet.horn (n + 1) i).toSSet ⟶ Y)
    (h : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      (F ◁ SSet.horn.ι i j hj) ≫ u = (F ◁ SSet.horn.ι i j hj) ≫ u') : u = u' := by
  apply MonoidalClosed.curry_injective
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← MonoidalClosed.curry_natural_left (f := SSet.horn.ι i j hj) (g := u),
    ← MonoidalClosed.curry_natural_left (f := SSet.horn.ι i j hj) (g := u'), h j hj]

/-- **The extension step of the recursion**, with the compatibility hypothesis given explicitly. -/
def buildLevelR_gen {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (N : ℕ) (D : RLevel p N)
    (hcomp : ∀ (b' : B) (σ : stdSimp (N + 1) ⟶ sSing B), sigmaVert σ = b' →
      HornTensorCompatible (F := sSing (Work.SSSR.StemsB.fibre p b')) (Y := sSing E) (i := 0)
        (fun (j : Fin (N + 2)) (_ : j ≠ 0) =>
          D.Φ b' (SSet.stdSimplex.δ (n := N) j ≫ σ))) :
    RStep p N D := by
  classical
  have hex : ∀ (b' : B) (σ : stdSimp (N + 1) ⟶ sSing B) (h : sigmaVert σ = b'),
      ∃ Φ : (sSing (Work.SSSR.StemsB.fibre p b') ⊗ stdSimp (N + 1)) ⟶ sSing E,
        (Φ ≫ sSingP p = SemiCartesianMonoidalCategory.snd _ _ ≫ σ) ∧
        (vertInclR p b' (N + 1) ≫ Φ = sSingP (Work.SSSR.StemsB.fibreIncl p b')) ∧
        (∀ (i : Fin (N + 2)) (_ : i ≠ 0)
          (_ : sigmaVert (SSet.stdSimplex.δ (n := N) i ≫ σ) = b'),
          (sSing (Work.SSSR.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := N) i) ≫ Φ =
            D.Φ b' (SSet.stdSimplex.δ (n := N) i ≫ σ)) := by
    intro b' σ h
    have hface : ∀ (j : Fin (N + 2)) (_ : j ≠ 0),
        sigmaVert (SSet.stdSimplex.δ (n := N) j ≫ σ) = b' := by
      intro j hj
      rw [sigmaVert_face j hj σ]
      exact h
    obtain ⟨u, hu⟩ := exists_hornGlue_tensor
      (fun (j : Fin (N + 2)) (_ : j ≠ 0) =>
        D.Φ b' (SSet.stdSimplex.δ (n := N) j ≫ σ)) (hcomp b' σ h)
    -- a face of the horn is the corresponding face of `Δ[N+1]`
    have hδgen : ∀ (j : Fin (N + 2)) (hj : j ≠ 0),
        (sSing (Work.SSSR.StemsB.fibre p b') ◁ SSet.horn.ι (0 : Fin (N + 2)) j hj) ≫
          (sSing (Work.SSSR.StemsB.fibre p b') ◁ (SSet.horn (N + 1) 0).ι) =
        sSing (Work.SSSR.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := N) j := by
      intro j hj
      rw [← whiskerLeft_comp, SSet.horn.ι_ι]
    -- the square commutes
    have hsq : u ≫ sSingP p =
        (sSing (Work.SSSR.StemsB.fibre p b') ◁ (SSet.horn (N + 1) 0).ι) ≫
          (SemiCartesianMonoidalCategory.snd _ _ ≫ σ) := by
      apply hornTensor_hom_ext
      intro j hj
      simp only [← Category.assoc]
      rw [hδgen j hj, CartesianMonoidalCategory.whiskerLeft_snd, hu j hj,
        D.lift b' _ (hface j hj), ← Category.assoc]
    -- the lift
    haveI : HasLiftingProperty
        ((sSing (Work.SSSR.StemsB.fibre p b')) ◁ (SSet.horn (N + 1) 0).ι) (sSingP p) :=
      hasLiftingProperty_whisker_horn p hfib _ 0
    let sq : CommSq u ((sSing (Work.SSSR.StemsB.fibre p b')) ◁ (SSet.horn (N + 1) 0).ι)
        (sSingP p) (SemiCartesianMonoidalCategory.snd _ _ ≫ σ) := ⟨hsq⟩
    obtain ⟨L⟩ : Nonempty sq.LiftStruct := (inferInstance : sq.HasLift).exists_lift
    -- the restriction of the lift to a face is the corresponding piece
    have hpiece : ∀ (j : Fin (N + 2)) (hj : j ≠ 0),
        (sSing (Work.SSSR.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := N) j) ≫ L.l =
          D.Φ b' (SSet.stdSimplex.δ (n := N) j ≫ σ) := by
      intro j hj
      rw [← hδgen j hj, Category.assoc, L.fac_left, hu j hj]
    refine ⟨L.l, L.fac_right, ?_, ?_⟩
    · -- the fibre condition
      have hj : (⟨1, by omega⟩ : Fin (N + 2)) ≠ 0 := by simp
      rw [← vertInclR_whiskerLeft p b' (j := ⟨1, by omega⟩) hj, Category.assoc,
        hpiece ⟨1, by omega⟩ hj]
      exact D.vert b' _ (hface ⟨1, by omega⟩ hj)
    · intro i hi h'
      exact hpiece i hi
  choose Φnew hnew1 hnew2 hnew3 using hex
  let newΦ : ∀ (b' : B) (σ : stdSimp (N + 1) ⟶ sSing B),
      (sSing (Work.SSSR.StemsB.fibre p b') ⊗ stdSimp (N + 1)) ⟶ sSing E :=
    fun b' σ => if h : sigmaVert σ = b' then Φnew b' σ h else rjunk p b' (N + 1)
  have hnewΦ : ∀ (b' : B) (σ : stdSimp (N + 1) ⟶ sSing B) (h : sigmaVert σ = b'),
      newΦ b' σ = Φnew b' σ h := by
    intro b' σ h
    simp only [newΦ]
    exact dif_pos h
  refine ⟨⟨newΦ, ?_, ?_⟩, ?_⟩
  · intro b' σ h
    rw [hnewΦ b' σ h]
    exact hnew1 b' σ h
  · intro b' σ h
    rw [hnewΦ b' σ h]
    exact hnew2 b' σ h
  · intro b' σ h i hi h'
    change (sSing (Work.SSSR.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := N) i) ≫ newΦ b' σ =
      D.Φ b' (SSet.stdSimplex.δ (n := N) i ≫ σ)
    rw [hnewΦ b' σ h]
    exact hnew3 b' σ h i hi h'

/-- **The extension step of the recursion.** -/
def buildLevelR {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (N : ℕ) (D : RLevel p N)
    (hcomp : HComp p N D) : RStep p N D := by
  refine buildLevelR_gen p hfib N D ?_
  intro b' σ h
  match N with
  | 0 => exact trivial
  | (M + 1) => exact hcomp b' σ h

/-- Two consecutive levels of the right-handed family, together with the coherence. -/
structure RPair {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) where
  d : RLevel p n
  d' : RLevel p (n + 1)
  coh : RCoh p n d d'

noncomputable def rpairBase {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) : RPair p 0 :=
  let D0 := Classical.choice (exists_rlevel_zero p)
  let S := buildLevelR p hfib 0 D0 trivial
  ⟨D0, S.D', S.coh⟩

/-- The simplicial identity of `Work.SSSR.stdSimplex_delta_pred_castPred`, at the universe of the
standard simplices used here. -/
lemma delta_pred_castPred_at (n : ℕ) :
    ∀ (j k : Fin (n + 3)) (hjk : j < k),
      (SSet.stdSimplex.δ (n := n) (k.pred (Fin.ne_zero_of_lt hjk)) : stdSimp n ⟶ stdSimp (n + 1)) ≫
        SSet.stdSimplex.δ (n := n + 1) j
      = (SSet.stdSimplex.δ (n := n) (j.castPred (Fin.ne_last_of_lt hjk)) : stdSimp n ⟶ stdSimp (n+1)) ≫
        SSet.stdSimplex.δ (n := n + 1) k :=
  fun j k hjk => stdSimplex_delta_pred_castPred j k hjk

noncomputable def rpairStep {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (n : ℕ) (pd : RPair p n) :
    RPair p (n + 1) :=
  let S := buildLevelR p hfib (n + 1) pd.d'
    (hcomp_of_rcoh p n pd.d' pd.d (delta_pred_castPred_at n) pd.coh)
  ⟨pd.d', S.D', S.coh⟩

noncomputable def rpairRec {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) : (n : ℕ) → RPair p n :=
  Nat.rec (motive := fun n => RPair p n) (rpairBase p hfib)
    (fun n pd => rpairStep p hfib n pd)

/-- The right-handed level-`n` family produced by the recursion. -/
noncomputable def coherentPhiR {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (n : ℕ) :
    ∀ (b' : B) (σ : stdSimp n ⟶ sSing B),
      (sSing (Work.SSSR.StemsB.fibre p b') ⊗ stdSimp n) ⟶ sSing E :=
  fun b' σ => (rpairRec p hfib n).d.Φ b' σ

lemma coherentPhiR_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (n : ℕ) (b' : B)
    (σ : stdSimp n ⟶ sSing B) :
    coherentPhiR p hfib n b' σ = (rpairRec p hfib n).d.Φ b' σ := rfl

lemma coherentPhiR_succ {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (n : ℕ) (b' : B)
    (σ : stdSimp (n + 1) ⟶ sSing B) :
    coherentPhiR p hfib (n + 1) b' σ = (rpairRec p hfib n).d'.Φ b' σ := rfl

/-- The left-handed fibre inclusion followed by the braiding is the right-handed one. -/
theorem vertIncl_braiding {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) (n : ℕ) :
    vertIncl p b' n ≫
        (β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp n)).inv =
      vertInclR p b' n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.braiding_inv_fst, vertIncl_snd, vertInclR_fst]
  · rw [Category.assoc, CartesianMonoidalCategory.braiding_inv_snd, vertIncl_fst, vertInclR_snd]

open scoped Classical in
/-- **The coherent lift family of a Serre fibration over the simplices of the base.** -/
theorem exists_coherentLiftFamily {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (b : B) :
    ∃ Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B),
        (Work.SSSR.sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
            Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b')) ⟶ Work.SSSR.sSing E),
      (∀ (n : ℕ) (b' : B)
          (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B)
          (h : Work.SSSR.sigmaVert σ = b'),
        Φ n b' σ h ≫ Work.SSSR.sSingP p
          = SemiCartesianMonoidalCategory.fst _ _ ≫ σ) ∧
      (∀ (n : ℕ) (b' : B)
          (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B)
          (h : Work.SSSR.sigmaVert σ = b'),
        Work.SSSR.vertIncl p b' n ≫ Φ n b' σ h
          = Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p b')) ∧
      (∀ (n : ℕ) (b' : B)
          (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⟶
            Work.SSSR.sSing B)
          (h : Work.SSSR.sigmaVert σ = b') (i : Fin (n+2)) (hi : i ≠ 0)
          (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := n) i ≫ σ) = b'),
        (SSet.stdSimplex.δ (n := n) i ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b')))
            ≫ Φ (n+1) b' σ h
          = Φ n b' (SSet.stdSimplex.δ (n := n) i ≫ σ) h') := by
  classical
  refine ⟨fun n b' σ _ => (β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp n)).inv ≫
      coherentPhiR p hfib n b' σ, ?_, ?_, ?_⟩
  · intro n b' σ h
    show ((β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp n)).inv ≫
        coherentPhiR p hfib n b' σ) ≫ sSingP p
      = SemiCartesianMonoidalCategory.fst _ _ ≫ σ
    rw [Category.assoc, coherentPhiR_apply, (rpairRec p hfib n).d.lift b' σ h,
      ← Category.assoc, CartesianMonoidalCategory.braiding_inv_snd]
  · intro n b' σ h
    show vertIncl p b' n ≫
        ((β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp n)).inv ≫
          coherentPhiR p hfib n b' σ)
      = sSingP (Work.SSSR.StemsB.fibreIncl p b')
    rw [← Category.assoc, vertIncl_braiding, coherentPhiR_apply,
      (rpairRec p hfib n).d.vert b' σ h]
  · intro n b' σ h i hi h'
    show (SSet.stdSimplex.δ (n := n) i ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b'))) ≫
        ((β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp (n+1))).inv ≫
          coherentPhiR p hfib (n+1) b' σ)
      = (β_ (sSing (Work.SSSR.StemsB.fibre p b')) (stdSimp n)).inv ≫
          coherentPhiR p hfib n b' (SSet.stdSimplex.δ (n := n) i ≫ σ)
    rw [tensorHom_id_eq_whiskerRight]
    rw [← SymmetricCategory.braiding_swap_eq_inv_braiding (sSing (Work.SSSR.StemsB.fibre p b'))
          (stdSimp (n+1)),
      ← SymmetricCategory.braiding_swap_eq_inv_braiding (sSing (Work.SSSR.StemsB.fibre p b'))
          (stdSimp n)]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc]
    rw [coherentPhiR_succ, (rpairRec p hfib n).coh b' σ h i hi h', coherentPhiR_apply]

end Work.SSSR
