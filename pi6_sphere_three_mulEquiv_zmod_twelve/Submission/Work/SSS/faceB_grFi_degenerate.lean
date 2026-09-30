import Mathlib
import Submission.Work.SSS.serreE1CruxD1

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **A degenerate face chain dies in the graded piece.**  If the `i`-th face of the nondegenerate
simplex `σ` is degenerate (its nondegenerate part has dimension `< k+1`), then `faceB ... i`
vanishes in `grF_{k+1}`.

Route: `Work.SSS.sndToSerre_range` gives the sharper range bound `range (pullback.snd ...) ≤ R_{k+1}`
for a degenerate simplex (note `SSet.yonedaEquiv (δ i ≫ sigHat σ) = δ (sSing B) i (nIndexBase σ)`,
so `hdeg` is exactly the degeneracy hypothesis), so `faceC` is
`sndToSerre ... (k+1) _ ≫ homOfLe (R_{k+1} ⊆ R_{k+2})` by `Work.SSS.sndToSerre_compat`'s second
clause, and `homOfLe (R_{k+1} ⊆ R_{k+2})` followed by `grFι f (k+1)` is `0`
(`Work.SSS.sCCMap_homOfLe_comp_grFι`).  Note `k+1 ≥ 1` is forced: a `0`-simplex is never
degenerate. -/
theorem faceB_grFi_degenerate (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (k t : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (k + 2))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t) (i : Fin (k + 3))
    (hdeg : SimplicialObject.δ (Work.SSS.sSing B) i
      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∉ (Work.SSS.sSing B).nonDegenerate (k + 1)) :
    (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (k + 1)).f ((k+1) + t)))
        (Work.SSS.faceB p hfib (k + 1) t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z i) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  -- The `i`-th face of `σ`, as a simplex of the base, is the degenerate simplex `hdeg` talks
  -- about, so `sndToSerre_range` bounds its second projection by `R_{k+1}` rather than `R_{k+2}`.
  have hye : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSS.sigHat σ)
      = SimplicialObject.δ (Work.SSS.sSing B) i
          (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) := by
    rw [show Work.SSS.sigHat σ
        = SSet.yonedaEquiv.symm (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) from rfl]
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact Equiv.apply_symm_apply _ _
  have hrange : SSet.Subcomplex.range
        (pullback.snd (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSS.sigHat σ)
          (Work.SSS.sSingP p))
      ≤ Work.StemsB.serreSubcomplex (Work.SSS.sSingP p) (k+1) :=
    (Work.SSS.sndToSerre_range (Work.SSS.sSingP p)).2 _ (by rw [hye]; exact hdeg)
  -- `faceC` at level `k+2` factors through the level-`(k+1)` second projection, via the
  -- compatibility of `sndToSerre` with the inclusions of the Serre filtration.
  have hfaceC : Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i
      = Work.SSS.sndToSerre (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSS.sigHat σ) (k+1) hrange
        ≫ Subfunctor.homOfLe
            (Work.StemsB.serreSubcomplex_mono (Work.SSS.sSingP p) (Nat.le_succ (k+1))) := by
    rw [Work.SSS.faceC]
    exact ((Work.SSS.sndToSerre_compat (Work.SSS.sSingP p)).2 (Nat.le_succ (k+1))
      _ hrange ((Work.SSS.sndToSerre_range (Work.SSS.sSingP p)).1 _)).symm
  -- The induced map of chain complexes splits as `sCCMap faceRestr ≫ sCCMap faceC`.
  have hsplit : Work.SSS.sCCMap (Work.SSS.faceRestr p hfib (k+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl i
        ≫ Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i)
      = Work.SSS.sCCMap (Work.SSS.faceRestr p hfib (k+1)
          (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl i)
        ≫ Work.SSS.sCCMap (Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i) := by
    simp only [Work.SSS.sCCMap, Functor.map_comp]
  -- The chain map `sCCMap (faceRestr ≫ faceC)` followed by `grFι` is zero: it factors through
  -- `C(R_{k+1})`, which `grFι` kills.
  have hkey : Work.SSS.sCCMap (Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i)
      = Work.SSS.sCCMap (Work.SSS.sndToSerre (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSS.sigHat σ) (k+1) hrange)
        ≫ Work.SSS.sCCMap (Subfunctor.homOfLe
            (Work.StemsB.serreSubcomplex_mono (Work.SSS.sSingP p) (Nat.le_succ (k+1)))) := by
    rw [hfaceC]
    simp only [Work.SSS.sCCMap, Functor.map_comp]
  have hzero : Work.SSS.sCCMap (Work.SSS.faceRestr p hfib (k+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl i
        ≫ Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i)
      ≫ Work.SSS.grFι (Work.SSS.sSingP p) (k+1) = 0 := by
    rw [hsplit, hkey]
    simp only [Category.assoc]
    rw [Work.SSS.sCCMap_homOfLe_comp_grFι (Work.SSS.sSingP p) k]
    simp
  -- Evaluate the vanishing chain map on the Eilenberg–Zilber chain.
  have hv := congrArg (fun m => (ModuleCat.Hom.hom (m.f ((k+1) + t)))
      (Work.SSS.ezElem p (k+1) t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) z)) hzero
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply] at hv
  change (ModuleCat.Hom.hom ((Work.SSS.grFι (Work.SSS.sSingP p) (k+1)).f ((k+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.faceRestr p hfib (k+1)
        (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl i
        ≫ Work.SSS.faceC p (k+1) (Work.SSS.sigHat σ) i)).f ((k+1)+t)))
        (Work.SSS.ezElem p (k+1) t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) z)) = 0
  exact hv

end Work.SSS
