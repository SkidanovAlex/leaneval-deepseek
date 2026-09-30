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

/-- **A degenerate face chain dies in the graded piece.**  If the `i`-th face of the nondegenerate
simplex `σ` is degenerate (its nondegenerate part has dimension `< k+1`), then `faceB ... i`
vanishes in `grF_{k+1}`.

Route: `Work.SSSR.sndToSerre_range` gives the sharper range bound `range (pullback.snd ...) ≤ R_{k+1}`
for a degenerate simplex (note `SSet.yonedaEquiv (δ i ≫ sigHat σ) = δ (sSing B) i (nIndexBase σ)`,
so `hdeg` is exactly the degeneracy hypothesis), so `faceC` is
`sndToSerre ... (k+1) _ ≫ homOfLe (R_{k+1} ⊆ R_{k+2})` by `Work.SSSR.sndToSerre_compat`'s second
clause, and `homOfLe (R_{k+1} ⊆ R_{k+2})` followed by `grFι R f (k+1)` is `0`
(`Work.SSSR.sCCMap_homOfLe_comp_grFι`).  Note `k+1 ≥ 1` is forced: a `0`-simplex is never
degenerate. -/
theorem faceB_grFi_degenerate (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (k t : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k + 2))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t) (i : Fin (k + 3))
    (hdeg : SimplicialObject.δ (Work.SSSR.sSing B) i
      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∉ (Work.SSSR.sSing B).nonDegenerate (k + 1)) :
    (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (k + 1)).f ((k+1) + t)))
        (Work.SSSR.faceB p hfib (k + 1) t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z i) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  -- The `i`-th face of `σ`, as a simplex of the base, is the degenerate simplex `hdeg` talks
  -- about, so `sndToSerre_range` bounds its second projection by `R_{k+1}` rather than `R_{k+2}`.
  have hye : SSet.yonedaEquiv (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSSR.sigHat σ)
      = SimplicialObject.δ (Work.SSSR.sSing B) i
          (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) := by
    rw [show Work.SSSR.sigHat σ
        = SSet.yonedaEquiv.symm (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) from rfl]
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact Equiv.apply_symm_apply _ _
  have hrange : SSet.Subcomplex.range
        (pullback.snd (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSSR.sigHat σ)
          (Work.SSSR.sSingP p))
      ≤ Work.SSSR.StemsB.serreSubcomplex (Work.SSSR.sSingP p) (k+1) :=
    (Work.SSSR.sndToSerre_range (Work.SSSR.sSingP p)).2 _ (by rw [hye]; exact hdeg)
  -- `faceC` at level `k+2` factors through the level-`(k+1)` second projection, via the
  -- compatibility of `sndToSerre` with the inclusions of the Serre filtration.
  have hfaceC : Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i
      = Work.SSSR.sndToSerre (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSSR.sigHat σ) (k+1) hrange
        ≫ Subfunctor.homOfLe
            (Work.SSSR.StemsB.serreSubcomplex_mono (Work.SSSR.sSingP p) (Nat.le_succ (k+1))) := by
    rw [Work.SSSR.faceC]
    exact ((Work.SSSR.sndToSerre_compat (Work.SSSR.sSingP p)).2 (Nat.le_succ (k+1))
      _ hrange ((Work.SSSR.sndToSerre_range (Work.SSSR.sSingP p)).1 _)).symm
  -- The induced map of chain complexes splits as `sCCMap R faceRestr ≫ sCCMap R faceC`.
  have hsplit : Work.SSSR.sCCMap R (Work.SSSR.faceRestr p hfib (k+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl i
        ≫ Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i)
      = Work.SSSR.sCCMap R (Work.SSSR.faceRestr p hfib (k+1)
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl i)
        ≫ Work.SSSR.sCCMap R (Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i) := by
    simp only [Work.SSSR.sCCMap, Functor.map_comp]
  -- The chain map `sCCMap R (faceRestr ≫ faceC)` followed by `grFι R` is zero: it factors through
  -- `C(R_{k+1})`, which `grFι R` kills.
  have hkey : Work.SSSR.sCCMap R (Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i)
      = Work.SSSR.sCCMap R (Work.SSSR.sndToSerre (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := k+1) i ≫ Work.SSSR.sigHat σ) (k+1) hrange)
        ≫ Work.SSSR.sCCMap R (Subfunctor.homOfLe
            (Work.SSSR.StemsB.serreSubcomplex_mono (Work.SSSR.sSingP p) (Nat.le_succ (k+1)))) := by
    rw [hfaceC]
    simp only [Work.SSSR.sCCMap, Functor.map_comp]
  have hzero : Work.SSSR.sCCMap R (Work.SSSR.faceRestr p hfib (k+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl i
        ≫ Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i)
      ≫ Work.SSSR.grFι R (Work.SSSR.sSingP p) (k+1) = 0 := by
    rw [hsplit, hkey]
    simp only [Category.assoc]
    rw [Work.SSSR.sCCMap_homOfLe_comp_grFι (Work.SSSR.sSingP p) k]
    simp
  -- Evaluate the vanishing chain map on the Eilenberg–Zilber chain.
  have hv := congrArg (fun m => (ModuleCat.Hom.hom (m.f ((k+1) + t)))
      (Work.SSSR.ezElem p (k+1) t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) z)) hzero
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply] at hv
  change (ModuleCat.Hom.hom ((Work.SSSR.grFι R (Work.SSSR.sSingP p) (k+1)).f ((k+1)+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.faceRestr p hfib (k+1)
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl i
        ≫ Work.SSSR.faceC p (k+1) (Work.SSSR.sigHat σ) i)).f ((k+1)+t)))
        (Work.SSSR.ezElem p (k+1) t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) z)) = 0
  exact hv

end Work.SSSR
