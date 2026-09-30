import Mathlib
import Submission.Work.SSSR.ezLinSnd_boundary_succ
import Submission.Work.SSSR.iotaF_chainMap
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- The `P = 0` case of the Eilenberg–Zilber derivation, linearised in the second variable: the
shuffle chain of a *vertex* of `X` and a chain `z` of `Y` is a chain map of degree `0`, i.e.
`∂ (ezLinSnd 0 (q+1) X Y σ z) = ezLinSnd 0 q X Y σ (∂z)` (in this case there are no `X`-face terms).

Route: `SSet.chainComplex_hom_ext` on the generators `Y.ιChainComplex τ`, `τ : Y _⦋q+1⦌`; the left
hand side becomes `eltHom (∂ (ezGen 0 (q+1) X Y σ τ))`
(`Work.SSSR.ι_comp_ezLinSnd_compS`), which is `eltHom (∑_j (-1)^j ezGen 0 q X Y σ (Y.δ_j τ))`
(`Work.SSSR.ezGen_boundary_zero`); the right hand side becomes
`∑_j (-1)^j eltHom (ezGen 0 q X Y σ (Y.δ_j τ))` (`Work.SSSR.ι_comp_d_compS`,
`Work.SSSR.ezLinSnd_ι_eltHomS`), and `eltHom` commutes with finite sums and `zsmul`
(`eltHom_sum`, `eltHom_zsmul`, `eltHom_addS`). -/
theorem ezLinSnd_d_zero (R : Type) [CommRing R] [Nontrivial R] (q : ℕ) (X Y : SSet.{0})
    (σ : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    CategoryTheory.CategoryStruct.comp (Work.SSSR.ezLinSnd 0 (q + 1) X Y σ)
        (((CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).chainComplex
          (Work.SSSR.KunnethEZ.eZR R)).d (0 + (q + 1)) (0 + q))
      = CategoryTheory.CategoryStruct.comp
        (((Y.chainComplex (Work.SSSR.KunnethEZ.eZR R)).d (q + 1) q))
        (Work.SSSR.ezLinSnd 0 q X Y σ) := by
  apply SSet.chainComplex_hom_ext (X := Y) (R := Work.SSSR.ezR R) (n := q + 1)
  intro τ
  rw [Work.SSSR.ι_comp_ezLinSnd_compS 0 (q + 1) X Y σ τ _,
    Work.SSSR.ι_comp_d_compS q Y τ _]
  simp only [Work.SSSR.ezLinSnd_ι_eltHomS]
  rw [Work.SSSR.ezGen_boundary_zero q X Y σ τ]
  rw [← Work.SSSR.eltHom_sum Finset.univ]
end Work.Pi6.MSS
