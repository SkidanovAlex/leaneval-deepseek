import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.ezSimplex_liftFam_coface
import Submission.Work.SSSR.KunnethEZ.ezGen_map_fst
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## Elementary helpers -/

/-- The transport of an element of a chain complex along an equality of degrees, natural for a chain
map. -/
lemma sCCMap_castElem {X Y : SSet.{0}} (φ : X ⟶ Y) {i j : ℕ} (h : i = j)
    (x : (sCC R X).X i) :
    (sCCMap R φ).f j (castElem (sCC R X) h x) = castElem (sCC R Y) h ((sCCMap R φ).f i x) := by
  subst h
  simp [castElem]

/-- Composition of chain maps applied to an element. -/
lemma sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (sCC R X).X n) : (sCCMap R k).f n ((sCCMap R g).f n x) = (sCCMap R (g ≫ k)).f n x := by
  rw [sCCMap_comp']; rfl

/-- The `i`-th face of the fundamental `(t+1)`-simplex of `Δ[t+1]` is the value of the coface
`δ i` on the fundamental `t`-simplex of `Δ[t]`. -/
lemma delta_stdIdSimplex_eq (t : ℕ) (i : Fin (t+2)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i (stdIdSimplex (t+1))
      = (SSet.stdSimplex.δ (n := t) i).app (op ⦋t⦌) (stdIdSimplex t) := by
  rw [show (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i (stdIdSimplex (t+1))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) from by
    rw [stdIdSimplex]
    rw [SSet.stdSimplex.δ_objEquiv_symm_apply (f := 𝟙 (SimplexCategory.mk (t+1)))]
    rw [Category.comp_id]]
  rw [show (SSet.stdSimplex.δ (n := t) i) = SSet.stdSimplex.map (SimplexCategory.δ i) from rfl]
  have hh := SSet.yonedaEquiv_comp (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk t)))
    (SSet.stdSimplex.map (SimplexCategory.δ i))
  rw [Category.id_comp] at hh
  have hid : stdIdSimplex t = SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk t))) := by
    rw [stdIdSimplex]
    exact (SSet.yonedaEquiv_map (𝟙 (SimplexCategory.mk t))).symm
  rw [hid, ← hh, SSet.yonedaEquiv_map]

/-- The composite `lastFaceChain ≫ TIncl` is the chain map induced by the last-face pasting map. -/
lemma lastFaceChain_comp_TIncl {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    lastFaceChain f t σ ≫ TIncl f σ
      = sCCMap R (pullFaceIncl f σ (Fin.last (t+1))) := by
  simp only [TIncl, lastFaceChain]
  rw [Category.assoc, ← sCCMap_comp', ← sCCMap_comp']
  rw [Subfunctor.homOfLe_ι, SSet.Subcomplex.toRange_ι, lastFaceMap_eq_pullFaceIncl]

/-- `castElem` written in the form produced by `Work.SSSR.KunnethEZ.rawX_eq_ezChain`. -/
lemma castElem_eq_ezChainForm {X Y : SSet.{0}} {i j : ℕ} (h : i = j)
    (x : ((X ⊗ Y).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X i) :
    castElem (sCC R (X ⊗ Y)) h x
      = (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X k) h)).hom x := by
  subst h; simp [castElem]

/-- The `X`-boundary part of the Eilenberg–Zilber shuffle chain at the last face is the shuffle
chain of the last face of the fundamental simplex, transported to the target bidegree. -/
lemma rawX_lastFace_eq_castElem_ezGen {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (t Q : ℕ)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌)
    (hQ : t + (Q+1) = (t+1)+Q) :
    Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
        (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))))
        (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ)
      = Work.SSSR.castElem
          (Work.SSSR.sCC R (Δ[t+1] ⊗ Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))) hQ
          (Work.SSSR.Cohomology.Crux33.ezGen t (Q+1) Δ[t+1]
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
            ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))) τ) := by
  rw [Work.SSSR.KunnethEZ.rawX_eq_ezChain t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
    hQ
    (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))))
    (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ)]
  rw [Work.SSSR.KunnethEZ.ezChain_gen]
  exact (castElem_eq_ezChainForm (X := Δ[t+1]) (Y := Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) hQ
    (Work.SSSR.Cohomology.Crux33.ezGen t (Q+1) Δ[t+1]
      (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))) τ)).symm

end

end Work.SSSR


namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

theorem iotaTLift_last_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t Q : ℕ) (b : B)
    (σ : Δ[t+1] ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌) :
    (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
        (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))))
          (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))
      = (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
          ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)
            (Work.SSSR.castElem
              (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
              (by omega : t + (Q+1) = (t+1)+Q)
              (Work.SSSR.iotaTLift p hfib t b
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ))) := by
  have hQ : t + (Q+1) = (t+1)+Q := by omega
  have hlast : Fin.last (t+1) ≠ 0 := by simp [Fin.last]
  -- ### The RHS reduces to the common form.
  have hR : (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
        ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q)
          (Work.SSSR.castElem
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
            hQ
            (Work.SSSR.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ)))
      = Work.SSSR.castElem
          (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) hQ
          ((Work.SSSR.sCCMap R (Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ
              (Fin.last (t+1)))).f (t+(Q+1))
            (Work.SSSR.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ)) := by
    rw [show (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
          ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ).f ((t+1)+Q) _)
        = ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) t σ) ≫
            (Work.SSSR.TIncl (Work.SSSR.sSingP p) σ)).f ((t+1)+Q) _ from rfl]
    rw [lastFaceChain_comp_TIncl]
    exact sCCMap_castElem _ hQ _
  -- ### The LHS reduces to the same common form.
  have hz : (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f (t+(Q+1))
        (Work.SSSR.Cohomology.Crux33.ezGen t (Q+1) Δ[t+1]
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))) τ)
      = (Work.SSSR.sCCMap R (Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ
            (Fin.last (t+1)))).f (t+(Q+1))
          (Work.SSSR.iotaTLift p hfib t b
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ) := by
    rw [delta_stdIdSimplex_eq t (Fin.last (t+1)),
      Work.SSSR.KunnethEZ.ezGen_map_fst t (Q+1) (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)))
        (Work.SSSR.stdIdSimplex t) τ]
    rw [sCCMap_comp_apply (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ⊗ₘ
        𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
      (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)]
    rw [Work.SSSR.ezSimplex_liftFam_coface p hfib t b σ h (Fin.last (t+1)) hlast h']
    rw [Work.SSSR.sCCMap_comp']
    rfl
  have hrawX := rawX_lastFace_eq_castElem_ezGen (R := R) p b t Q τ hQ
  have hL : (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
        (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))))
          (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))
      = Work.SSSR.castElem
          (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) hQ
          ((Work.SSSR.sCCMap R (Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ
              (Fin.last (t+1)))).f (t+(Q+1))
            (Work.SSSR.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ)) := by
    calc
      (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
          (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
            (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))))
            (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))
          = (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
              (Work.SSSR.castElem
                (Work.SSSR.sCC R (Δ[t+1] ⊗ Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))) hQ
                (Work.SSSR.Cohomology.Crux33.ezGen t (Q+1) Δ[t+1]
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
                  ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))) τ)) := by
            rw [hrawX]
      _ = Work.SSSR.castElem
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) hQ
            ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f (t+(Q+1))
              (Work.SSSR.Cohomology.Crux33.ezGen t (Q+1) Δ[t+1]
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
                ((Δ[t+1]).δ (Fin.last (t+1)) (Work.SSSR.stdIdSimplex (t+1))) τ)) :=
            sCCMap_castElem _ hQ _
      _ = Work.SSSR.castElem
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) hQ
            ((Work.SSSR.sCCMap R (Work.SSSR.pullFaceIncl (Work.SSSR.sSingP p) σ
                (Fin.last (t+1)))).f (t+(Q+1))
              (Work.SSSR.iotaTLift p hfib t b
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ)) := by
            rw [hz]
  rw [hL, ← hR]

end

end Work.SSSR
