import Mathlib
import Submission.Work.SSSR.serreE1CruxDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The chain-level Eilenberg-Zilber map `Work.SSSR.iotaT` evaluated on an element of the fibre
chains is `Work.SSSR.iotaTLin`.

Route: `Work.SSSR.iotaT` is `Sigma.desc` of the maps `eltHom (sCCMap R ezSimplex (ezGen ... τ))`, whose
value on the coprojection `(sSing F_b).ιChainComplex τ` is `Work.SSSR.iotaT_gen`; `ezLinSnd` is the
linear extension of `τ ↦ ezGen ... τ` (`Work.SSSR.KunnethEZ.ezLinSnd_ι` / `Work.SSSR.ezLinSnd_apply`),
and `sCCMap R ezSimplex` is ℤ-linear.  Alternatively state both sides via
`SSet.chainComplex_hom_ext` and the generator `ιChainComplex τ` and use
`Work.SSSR.KunnethEZ.chain_eq_sum_gen` in the second variable. -/
theorem iotaT_eq_iotaTLin (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (s t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (z : (Work.SSSR.fibreCC (R := R) p b).X t) :
    (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (s + 1) b σ h t)) z
      = Work.SSSR.iotaTLin p hfib s t b σ h z := by
  -- Both sides are the same morphism out of the fibre chains, evaluated at `z`: it suffices to
  -- compare them on the generators `ιChainComplex τ`, which is `SSet.chainComplex_hom_ext`.
  have hmap : Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (s + 1) b σ h t
      = Work.SSSR.ezLinSnd (s + 1) t
          (SSet.stdSimplex.obj (SimplexCategory.mk (s + 1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (s + 1))
        ≫ (Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
            (Work.SSSR.liftFam_proj p hfib) (s + 1) b σ h)).f ((s + 1) + t) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [Work.SSSR.iotaT_gen, ← Category.assoc, Work.SSSR.ezLinSnd_ι, ← Work.SSSR.eltHom_comp]
    congr 1
  rw [hmap, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

end Work.SSSR
