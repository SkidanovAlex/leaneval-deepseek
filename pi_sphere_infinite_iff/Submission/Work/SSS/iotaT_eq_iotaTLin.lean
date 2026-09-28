import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The chain-level Eilenberg-Zilber map `Work.SSS.iotaT` evaluated on an element of the fibre
chains is `Work.SSS.iotaTLin`.

Route: `Work.SSS.iotaT` is `Sigma.desc` of the maps `eltHom (sCCMap ezSimplex (ezGen ... τ))`, whose
value on the coprojection `(sSing F_b).ιChainComplex τ` is `Work.SSS.iotaT_gen`; `ezLinSnd` is the
linear extension of `τ ↦ ezGen ... τ` (`Work.KunnethEZ.ezLinSnd_ι` / `Work.SSS.ezLinSnd_apply`),
and `sCCMap ezSimplex` is ℤ-linear.  Alternatively state both sides via
`SSet.chainComplex_hom_ext` and the generator `ιChainComplex τ` and use
`Work.KunnethEZ.chain_eq_sum_gen` in the second variable. -/
theorem iotaT_eq_iotaTLin (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (z : (Work.SSS.fibreCC p b).X t) :
    (ModuleCat.Hom.hom (Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (s + 1) b σ h t)) z
      = Work.SSS.iotaTLin p hfib s t b σ h z := by
  -- Both sides are the same morphism out of the fibre chains, evaluated at `z`: it suffices to
  -- compare them on the generators `ιChainComplex τ`, which is `SSet.chainComplex_hom_ext`.
  have hmap : Work.SSS.iotaT p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (s + 1) b σ h t
      = Work.SSS.ezLinSnd (s + 1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (s + 1))
        ≫ (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (s + 1) b σ h)).f ((s + 1) + t) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [Work.SSS.iotaT_gen, ← Category.assoc, Work.SSS.ezLinSnd_ι, ← Work.SSS.eltHom_comp]
    congr 1
  rw [hmap, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end Work.SSS
