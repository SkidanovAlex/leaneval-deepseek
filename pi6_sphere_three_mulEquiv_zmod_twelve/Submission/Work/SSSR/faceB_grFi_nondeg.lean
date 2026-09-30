import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Transport along an equality of simplices of the base

The target statement compares the `i`-th face chain of the coherent lift, pushed into `grF_s`
(where the face simplex is written as `δ i ≫ σ`), with the `mapPhiY R`-image of the corresponding
chain over the nondegenerate simplex `ρ` (where the same simplex is written `nIndexSigma … ρ`).
The two simplices are identified by the hypothesis `hρi`, and the identification is implemented in
the statement by `Work.SSSR.pieceCastElem` / `Work.SSSR.pullCastElem`, i.e. by `eqToHom` along the
induced equality of the chain complexes `C(T_m)` / `piece_m`.

The lemmas below are the (necessarily generic) naturality statements making that transport
compatible with the maps appearing in the statement: the quotient projection `pieceπOf`, the second
projection `sndToSerre` into the Serre filtration, and the identification
`pieceπ R ≫ mapPhiY R = sCCMap R sndToR ≫ grFι R` (`Work.SSSR.thetaPhi_mapPhiY_apply_f`).  Each of these
maps is a *functor* of the simplex `m`, so `cases h` — with `m`, `m'` two *variables* — reduces the
statement to proof irrelevance of the (Prop-valued) range bounds. -/

/-- Composition in `ModuleCat ℤ`, on an element, in the form in which the applications below
appear (element of the source on the inside). -/
lemma hom_comp_apply_elem {M N K : ModuleCat R} (f : M ⟶ N) (g : N ⟶ K) (x : M) :
    (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom f) x) = (ModuleCat.Hom.hom (f ≫ g)) x := by
  rw [ModuleCat.hom_comp]; rfl

/-- `sCCMap R` of a composite, on an element. -/
lemma sCCMap_comp_apply_elem {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (sCC R X).X n) :
    (ModuleCat.Hom.hom ((sCCMap R (g ≫ k)).f n)) x
      = (ModuleCat.Hom.hom ((sCCMap R k).f n)) ((ModuleCat.Hom.hom ((sCCMap R g).f n)) x) := by
  rw [sCCMap_comp']
  exact (chainMap_comp_apply (sCCMap R g) (sCCMap R k) x).symm

/-- **Naturality of the quotient projection under an equality of simplices.**  Transporting the
value of `pieceπOf f m` in the graded piece along `h : m = m'` (through `pieceCastElem`) is the
value of `pieceπOf f m'` at the transported element (through `pullCastElem`).  Route: `subst h`
makes both `pieceCastElem` and `pullCastElem` the identity. -/
lemma pieceCastElem_pieceπOf_elem {X Y : SSet.{0}} (f : X ⟶ Y) {P n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (x : (sCC R (pullAlong f m)).X n) :
    pieceCastElem f h ((ModuleCat.Hom.hom ((pieceπOf f m).f n)) x)
      = (ModuleCat.Hom.hom ((pieceπOf f m').f n)) (pullCastElem f h x) := by
  subst h
  simp only [pieceCastElem, pullCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- **Naturality of the second projection under an equality of simplices.**  Transporting the value
of `sCCMap R (sndToSerre f m k hk)` along `h : m = m'` is the value of `sCCMap R (sndToSerre f m' …)`
at the transported element; the two range bounds are `Prop`-valued, so `subst h` reduces the claim
to proof irrelevance. -/
lemma sCCMap_sndToSerre_cast_elem {X Y : SSet.{0}} (f : X ⟶ Y) {P k n : ℕ}
    {m m' : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y} (h : m = m')
    (hk : SSet.Subcomplex.range (pullback.snd m f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
    (hk' : SSet.Subcomplex.range (pullback.snd m' f) ≤ Work.SSSR.StemsB.serreSubcomplex f k)
    (x : (sCC R (pullAlong f m)).X n) :
    (ModuleCat.Hom.hom ((sCCMap R (sndToSerre f m k hk)).f n)) x
      = (ModuleCat.Hom.hom ((sCCMap R (sndToSerre f m' k hk')).f n)) (pullCastElem f h x) := by
  subst h
  simp only [pullCastElem, eqToHom_refl, ModuleCat.id_apply]

/-- The elementwise form of `Work.SSSR.thetaPhi_mapPhiY_apply_f`: the quotient projection
`pieceπ R` followed by `mapPhiY R` is the second projection followed by `grFι R`. -/
lemma thetaPhi_mapPhiY_apply_f_elem {X Y : SSet.{0}} (f : X ⟶ Y) (d n : ℕ) (y : nIndex Y d)
    (x : (sCC R (pullAlong f (nIndexSigma Y d y))).X n) :
    (ModuleCat.Hom.hom ((mapPhiY R f d y).f n)) ((ModuleCat.Hom.hom ((pieceπ R f d y).f n)) x)
      = (ModuleCat.Hom.hom ((grFι R f d).f n)) ((ModuleCat.Hom.hom ((sCCMap R (sndToR f y)).f n)) x) := by
  erw [hom_comp_apply_elem ((pieceπ R f d y).f n) ((mapPhiY R f d y).f n) x,
      hom_comp_apply_elem ((sCCMap R (sndToR f y)).f n) ((grFι R f d).f n) x]
  exact congrArg (fun g => (ModuleCat.Hom.hom g) x) (thetaPhi_mapPhiY_apply_f f d n y)

/-- **The `i`-th face chain, pushed to the graded piece, for a nondegenerate face `i ≠ 0`.**
`Work.SSSR.faceB ... i` is the image of the Eilenberg–Zilber chain of `Δ[s] ⊗ F_b` under
`faceRestr i ≫ faceC i`; its image in `grF_s` is the `mapPhiY R`-image of the Eilenberg–Zilber chain
`iotaF` of the corresponding nondegenerate simplex `ρ` of the base.

Route: `faceB i = (sCCMap R (faceRestr i ≫ faceC i)) (ezElem)`; after `cases hρi` the lemma
`Work.SSSR.sndToR_eq_sndToSerre` (a `rfl`-equality) identifies `faceC i` with `sndToR f ρ` (the
extra range-bound proofs are `Prop`-valued), and `Work.SSSR.faceRestr_eq_ezSimplex` identifies
`faceRestr i` with `ezSimplex ... (δ i ≫ σHat) h'`; `Work.SSSR.pieceCastElem _ rfl` is the
identity, `Work.SSSR.pieceπ_eq` is `rfl`, and the goal is
`Work.SSSR.thetaPhi_mapPhiY_apply_f` at `ρ` (`pieceπ R ≫ mapPhiY R = sCCMap R sndToR ≫ grFι R`,
degreewise) applied to the chain `sCCMap R (faceRestr i) ezElem`.  The hypotheses `hi` and `h'` are
not needed for the proof but are kept for the call site.

(Implemented as follows.  `faceB` is unfolded, `sCCMap_comp_apply_elem` turns the composite
`sCCMap R (faceRestr ≫ faceC)` into two successive applications; the equality `hρi` is then handled
by the generic transport lemmas above rather than by `cases hρi` — the latter is not available
since it would have to eliminate the composite term `nIndexSigma (sSing B) s ρ`.  Namely
`sCCMap_sndToSerre_cast_elem` with `hρi`, `sndToR_eq_sndToSerre` and proof irrelevance of the range
bounds rewrite `sCCMap R (faceC i)` applied to the chain into `sCCMap R (sndToR f ρ)` applied to the
`pullCastElem`-transport of the chain, while `pieceCastElem_pieceπOf_elem` and `pieceπ_eq` rewrite
the right-hand side into `mapPhiY R` applied to `pieceπ R f s ρ` at that transport, and
`thetaPhi_mapPhiY_apply_f_elem` identifies the two.) -/
theorem faceB_grFi_nondeg (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
    (b : B) (h : Work.SSSR.sigmaVert (Work.SSSR.sigHat σ) = b)
    (z : (Work.SSSR.fibreCC p b).X t)
    (ρ : Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (i : Fin (s + 2)) (hi : i ≠ 0)
    (hρi : SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ
      = Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s ρ)
    (h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ) = b) :
    (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s + t)))
        (Work.SSSR.faceB p hfib s t b (Work.SSSR.sigHat σ) h z i)
      = (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s ρ).f (s + t)))
          (Work.SSSR.pieceCastElem (Work.SSSR.sSingP p) hρi
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
                (SSet.stdSimplex.δ (n := s) i ≫ Work.SSSR.sigHat σ)).f (s + t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.faceRestr p hfib s b
                (Work.SSSR.sigHat σ) h i)).f (s + t))) (Work.SSSR.ezElem p s t b z)))) := by
  -- `faceC i = sndToR f ρ` and `pieceπOf f (δ i ≫ σ) = pieceπ R f s ρ` after transporting along `hρi`.
  have key1 : (ModuleCat.Hom.hom ((sCCMap R (faceC p s (sigHat σ) i)).f (s + t)))
      ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
        (ezElem p s t b z))
    = (ModuleCat.Hom.hom ((sCCMap R (sndToR (sSingP p) ρ)).f (s + t)))
      (pullCastElem (sSingP p) hρi
        ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
          (ezElem p s t b z))) := by
    rw [show faceC p s (sigHat σ) i
          = sndToSerre (sSingP p) (SSet.stdSimplex.δ (n := s) i ≫ sigHat σ) (s + 1)
              ((sndToSerre_range (sSingP p)).1 (SSet.stdSimplex.δ (n := s) i ≫ sigHat σ))
          from rfl]
    rw [sCCMap_sndToSerre_cast_elem (sSingP p) hρi
          ((sndToSerre_range (sSingP p)).1 (SSet.stdSimplex.δ (n := s) i ≫ sigHat σ))
          (T_range_le (sSingP p) ρ)
          ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z))]
    rw [sndToR_eq_sndToSerre]
  have key2 : (ModuleCat.Hom.hom ((mapPhiY R (sSingP p) s ρ).f (s + t)))
      (pieceCastElem (sSingP p) hρi
        ((ModuleCat.Hom.hom ((pieceπOf (sSingP p)
            (SSet.stdSimplex.δ (n := s) i ≫ sigHat σ)).f (s + t)))
          ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z))))
    = (ModuleCat.Hom.hom ((grFι R (sSingP p) s).f (s + t)))
      ((ModuleCat.Hom.hom ((sCCMap R (sndToR (sSingP p) ρ)).f (s + t)))
        (pullCastElem (sSingP p) hρi
          ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z)))) := by
    rw [pieceCastElem_pieceπOf_elem (sSingP p) hρi
          ((ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i)).f (s + t)))
            (ezElem p s t b z))]
    rw [show pieceπOf (sSingP p) (nIndexSigma (sSing B) s ρ) = pieceπ R (sSingP p) s ρ from rfl]
    exact thetaPhi_mapPhiY_apply_f_elem (sSingP p) s (s + t) ρ _
  rw [show faceB p hfib s t b (sigHat σ) h z i
        = (ModuleCat.Hom.hom ((sCCMap R (faceRestr p hfib s b (sigHat σ) h i
              ≫ faceC p s (sigHat σ) i)).f (s + t))) (ezElem p s t b z) from rfl]
  rw [sCCMap_comp_apply_elem (faceRestr p hfib s b (sigHat σ) h i) (faceC p s (sigHat σ) i)
        (ezElem p s t b z)]
  rw [key1]
  exact key2.symm

end Work.SSSR
