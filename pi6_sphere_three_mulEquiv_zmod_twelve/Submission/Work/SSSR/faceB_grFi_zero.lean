import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
import Submission.Work.SSSR.faceRestr_eq_ezSimplexZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementary transport lemmas used in the proof of `Work.SSSR.faceB_grFi_zero` -/

/-- Element-level functoriality of `Work.SSSR.sCCMap R`: the `(n, n)`-component of the chain map
induced by a composite is the composite of the components. -/
lemma sCCMap_comp_apply_faceB0 {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (sCC R X).X n) :
    (ModuleCat.Hom.hom ((sCCMap R k).f n)) ((ModuleCat.Hom.hom ((sCCMap R g).f n)) x)
      = (ModuleCat.Hom.hom ((sCCMap R (g ≫ k)).f n)) x := by
  rw [show sCCMap R (g ≫ k) = sCCMap R g ≫ sCCMap R k from by simp only [sCCMap, Functor.map_comp]]
  rw [HomologicalComplex.comp_f]
  rfl

/-- The quotient projection of a σ-piece commutes with the transport of chains along an equality of
simplices of the base: `Work.SSSR.pieceCastElem` is `eqToHom`, so this is the naturality of
`cokernel.π` under the equality of the two `bdryAlong`-inclusions. -/
lemma pieceCastElem_pieceπOf_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    (m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (h : m = m') (x : (sCC R (pullAlong f m)).X n) :
    pieceCastElem f h ((ModuleCat.Hom.hom ((pieceπOf f m).f n)) x)
      = (ModuleCat.Hom.hom ((pieceπOf f m').f n))
          (eqToHom (congrArg (fun m => (sCC R (pullAlong f m)).X n) h) x) := by
  subst h
  simp only [pieceCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- The second projection into the Serre filtration commutes with the transport of chains along an
equality of simplices of the base (the two range bounds are proof-irrelevant). -/
lemma sndToSerre_cast_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) {P k n : ℕ}
    (m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (h : m = m')
    (h1 : SSet.Subcomplex.range (pullback.snd m f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
    (h2 : SSet.Subcomplex.range (pullback.snd m' f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
    (x : (sCC R (pullAlong f m)).X n) :
    (ModuleCat.Hom.hom ((sCCMap R (sndToSerre f m k h1)).f n)) x
      = (ModuleCat.Hom.hom ((sCCMap R (sndToSerre f m' k h2)).f n))
          (eqToHom (congrArg (fun m => (sCC R (pullAlong f m)).X n) h) x) := by
  subst h
  rw [Subsingleton.elim h1 h2]
  simp only [eqToHom_refl, ModuleCat.id_apply]

/-- `Work.SSSR.thetaPhi_mapPhiY_apply_f` at the level of elements: the projection to the σ-piece
followed by `Work.SSSR.mapPhiY R` is the second projection followed by `Work.SSSR.grFι R`. -/
lemma mapPhiY_pieceπOf_apply_faceB0 {X Y : SSet.{0}} (f : X ⟶ Y) (d n : ℕ) (y : nIndex Y d)
    (z : (sCC R (pullAlong f (nIndexSigma Y d y))).X n) :
    (ModuleCat.Hom.hom ((mapPhiY R f d y).f n))
        ((ModuleCat.Hom.hom ((pieceπOf f (nIndexSigma Y d y)).f n)) z)
      = (ModuleCat.Hom.hom ((grFι R f d).f n))
          ((ModuleCat.Hom.hom ((sCCMap R (sndToR f y)).f n)) z) := by
  rw [show pieceπOf f (nIndexSigma Y d y) = pieceπ R f d y from rfl]
  have hth := thetaPhi_mapPhiY_apply_f (R := R) f d n y
  have h3 : (ModuleCat.Hom.hom ((pieceπ R f d y).f n ≫ (mapPhiY R f d y).f n)) z
      = (ModuleCat.Hom.hom ((sCCMap R (sndToR f y)).f n ≫ (grFι R f d).f n)) z :=
    congrArg (fun (k : (sCC R (pullAlong f (nIndexSigma Y d y))).X n ⟶ (grF (serF R f) d).X n) =>
      ModuleCat.Hom.hom k z) hth
  exact h3

/-- **The `0`-th face chain, pushed to the graded piece.**  The `0`-face chain of the coherent lift
is the `0`-face lift `Work.SSSR.ezSimplexZero`, so its image in `grF_s` is the `mapPhiY R`-image of the
class of `ezSimplexZero` in the piece of the corresponding nondegenerate simplex.

Route: `Work.SSSR.faceB ... 0 = (sCCMap R (faceRestr 0 ≫ faceC 0)) (ezElem)`,
`Work.SSSR.faceRestr_eq_ezSimplexZero` identifies `faceRestr 0` with `ezSimplexZero`, `faceC 0`
is `sndToR f ρ0` up to the equality `hρ0` of simplices (`cases hρ0`, using
`Work.SSSR.sndToR_eq_sndToSerre` and proof irrelevance of the two range bounds), and then
`Work.SSSR.thetaPhi_mapPhiY_apply_f` (`pieceπ R ≫ mapPhiY R = sCCMap R sndToR ≫ grFι R`, degreewise) with
`Work.SSSR.pieceCastElem`: `pieceCastElem _ rfl` is the identity and `cases hρ0` transports the
whole equality. -/
theorem faceB_grFi_zero (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (b : B) (h : Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) = b)
    (z : (Work.SSSR.fibreCC p b).X t)
    (ρ0 : Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (hρ0 : SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ
      = Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0) :
    (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s + t)))
        (Work.SSSR.faceB p hfib s t b (Work.SSSR.sigHat σ) h z 0)
      = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ0).f (s + t)))
          (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρ0
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)).f (s + t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p
                (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b
                (Work.SSSR.sigHat σ) h)).f (s + t))) (Work.SSSR.ezElem p s t b z)))) := by
  -- Unfold the definition of the `0`-th face chain and of the face projection.
  unfold Work.SSSR.faceB Work.SSSR.faceC
  rw [Work.SSSR.faceRestr_eq_ezSimplexZero]
  -- The left-hand side, in terms of the Eilenberg–Zilber chain of `ezSimplexZero`.
  rw [← sCCMap_comp_apply_faceB0]
  -- Transport the class of `ezSimplexZero` along the equality of simplices.
  rw [pieceCastElem_pieceπOf_faceB0]
  -- `mapPhiY R` is `sCCMap R sndToR` followed by `grFι R` on the σ-piece.
  rw [mapPhiY_pieceπOf_apply_faceB0]
  -- The two manifestations of the face projection differ only by their (irrelevant) range bound.
  have hcast := sndToSerre_cast_faceB0 (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ)
      (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ0)
      hρ0
      ((Work.SSSR.sndToSerre_range (Work.SSSR.sSingP p)).1
        (SSet.stdSimplex.δ (n := s) 0 ≫ Work.SSSR.sigHat σ))
      (Work.SSSR.T_range_le (Work.SSSR.sSingP p) ρ0)
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) s b (Work.SSSR.sigHat σ) h)).f (s+t)))
        (Work.SSSR.ezElem p s t b z))
  rw [hcast]
  rw [← Work.SSSR.sndToR_eq_sndToSerre]

end Work.SSSR
