import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.faceRestr_eq_ezSimplexZero

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementary transport lemmas used in the proof of `Work.SSS.faceB_grFi_zero` -/

/-- Element-level functoriality of `Work.SSS.sCCMap`: the `(n, n)`-component of the chain map
induced by a composite is the composite of the components. -/
lemma sCCMap_comp_apply_faceB0 {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (sCC X).X n) :
    (ModuleCat.Hom.hom ((sCCMap k).f n)) ((ModuleCat.Hom.hom ((sCCMap g).f n)) x)
      = (ModuleCat.Hom.hom ((sCCMap (g ≫ k)).f n)) x := by
  rw [show sCCMap (g ≫ k) = sCCMap g ≫ sCCMap k from by simp only [sCCMap, Functor.map_comp]]
  rw [HomologicalComplex.comp_f]
  rfl

/-- The quotient projection of a σ-piece commutes with the transport of chains along an equality of
simplices of the base: `Work.SSS.pieceCastElem` is `eqToHom`, so this is the naturality of
`cokernel.π` under the equality of the two `bdryAlong`-inclusions. -/
lemma pieceCastElem_pieceπOf_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    (m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (h : m = m') (x : (sCC (pullAlong f m)).X n) :
    pieceCastElem f h ((ModuleCat.Hom.hom ((pieceπOf f m).f n)) x)
      = (ModuleCat.Hom.hom ((pieceπOf f m').f n))
          (eqToHom (congrArg (fun m => (sCC (pullAlong f m)).X n) h) x) := by
  subst h
  simp only [pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- The second projection into the Serre filtration commutes with the transport of chains along an
equality of simplices of the base (the two range bounds are proof-irrelevant). -/
lemma sndToSerre_cast_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) {P k n : ℕ}
    (m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (h : m = m')
    (h1 : SSet.Subcomplex.range (pullback.snd m f) ≤ Work.StemsB.serreSubcomplex f k)
    (h2 : SSet.Subcomplex.range (pullback.snd m' f) ≤ Work.StemsB.serreSubcomplex f k)
    (x : (sCC (pullAlong f m)).X n) :
    (ModuleCat.Hom.hom ((sCCMap (sndToSerre f m k h1)).f n)) x
      = (ModuleCat.Hom.hom ((sCCMap (sndToSerre f m' k h2)).f n))
          (eqToHom (congrArg (fun m => (sCC (pullAlong f m)).X n) h) x) := by
  subst h
  rw [Subsingleton.elim h1 h2]
  simp only [eqToHom_refl, ModuleCat.id_apply]

/-- `Work.SSS.thetaPhi_mapPhiY_apply_f` at the level of elements: the projection to the σ-piece
followed by `Work.SSS.mapPhiY` is the second projection followed by `Work.SSS.grFι`. -/
lemma mapPhiY_pieceπOf_apply_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) (d n : ℕ) (y : nIndex Y d)
    (z : (sCC (pullAlong f (nIndexSigma Y d y))).X n) :
    (ModuleCat.Hom.hom ((mapPhiY f d y).f n))
        ((ModuleCat.Hom.hom ((pieceπOf f (nIndexSigma Y d y)).f n)) z)
      = (ModuleCat.Hom.hom ((grFι f d).f n))
          ((ModuleCat.Hom.hom ((sCCMap (sndToR f y)).f n)) z) := by
  rw [show pieceπOf f (nIndexSigma Y d y) = pieceπ f d y from rfl]
  have hth := thetaPhi_mapPhiY_apply_f f d n y
  have h3 : (ModuleCat.Hom.hom ((pieceπ f d y).f n ≫ (mapPhiY f d y).f n)) z
      = (ModuleCat.Hom.hom ((sCCMap (sndToR f y)).f n ≫ (grFι f d).f n)) z :=
    congrArg (fun (k : (sCC (pullAlong f (nIndexSigma Y d y))).X n ⟶ (grF (serF f) d).X n) =>
      ModuleCat.Hom.hom k z) hth
  exact h3

/-- **The `0`-th face chain, pushed to the graded piece.**  The `0`-face chain of the coherent lift
is the `0`-face lift `Work.SSS.ezSimplexZero`, so its image in `grF_s` is the `mapPhiY`-image of the
class of `ezSimplexZero` in the piece of the corresponding nondegenerate simplex.

Route: `Work.SSS.faceB ... 0 = (sCCMap (faceRestr 0 ≫ faceC 0)) (ezElem)`,
`Work.SSS.faceRestr_eq_ezSimplexZero` identifies `faceRestr 0` with `ezSimplexZero`, `faceC 0`
is `sndToR f ρ0` up to the equality `hρ0` of simplices (`cases hρ0`, using
`Work.SSS.sndToR_eq_sndToSerre` and proof irrelevance of the two range bounds), and then
`Work.SSS.thetaPhi_mapPhiY_apply_f` (`pieceπ ≫ mapPhiY = sCCMap sndToR ≫ grFι`, degreewise) with
`Work.SSS.pieceCastElem`: `pieceCastElem _ rfl` is the identity and `cases hρ0` transports the
whole equality. -/
theorem faceB_grFi_zero (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s + 1))
    (b : B) (h : Work.SSS.sigmaVert (Work.SSS.sigHat σ) = b)
    (z : (Work.SSS.fibreCC p b).X t)
    (ρ0 : Work.SSS.nIndex (Work.SSS.sSing B) s)
    (hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ
      = Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0) :
    (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s + t)))
        (Work.SSS.faceB p hfib s t b (Work.SSS.sigHat σ) h z 0)
      = (ModuleCat.Hom.hom ((Work.SSS.mapPhiY (Work.SSS.sSingP p) s ρ0).f (s + t)))
          (Work.SSS.pieceCastElem (Work.SSS.sSingP p) hρ0
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)).f (s + t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p
                (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b
                (Work.SSS.sigHat σ) h)).f (s + t))) (Work.SSS.ezElem p s t b z)))) := by
  -- Unfold the definition of the `0`-th face chain and of the face projection.
  unfold Work.SSS.faceB Work.SSS.faceC
  rw [Work.SSS.faceRestr_eq_ezSimplexZero]
  -- The left-hand side, in terms of the Eilenberg–Zilber chain of `ezSimplexZero`.
  rw [← sCCMap_comp_apply_faceB0]
  -- Transport the class of `ezSimplexZero` along the equality of simplices.
  rw [pieceCastElem_pieceπOf_faceB0]
  -- `mapPhiY` is `sCCMap sndToR` followed by `grFι` on the σ-piece.
  rw [mapPhiY_pieceπOf_apply_faceB0]
  -- The two manifestations of the face projection differ only by their (irrelevant) range bound.
  have hcast := sndToSerre_cast_faceB0 (Work.SSS.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ)
      (Work.SSS.nIndexSigma (Work.SSS.sSing B) s ρ0)
      hρ0
      ((Work.SSS.sndToSerre_range (Work.SSS.sSingP p)).1
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSS.sigHat σ))
      (Work.SSS.T_range_le (Work.SSS.sSingP p) ρ0)
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib)
          (Work.SSS.liftFam_proj p hfib) s b (Work.SSS.sigHat σ) h)).f (s+t)))
        (Work.SSS.ezElem p s t b z))
  rw [hcast]
  rw [← Work.SSS.sndToR_eq_sndToSerre]

end Work.SSS
