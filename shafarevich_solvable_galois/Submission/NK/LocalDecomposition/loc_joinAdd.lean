import Mathlib
import Submission.NK.BrauerHasse.exists_add
import Submission.NK.LocalDecomposition.Localisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalDecomposition

open NK.BrauerHasse

set_option maxHeartbeats 800000

universe u

/-- **Restriction commutes with the addition of `H2Profinite`.**

For an inclusion `V ≤ U` of closed subgroups of `Gal(K'/K)`, the restriction map
`H2Profinite.res p h : H²(U, Z/p) → H²(V, Z/p)` is additive with respect to the addition
`H2Profinite.joinAdd` of the colimit: since both sides are computed on the finite levels and
the level-wise restriction `H2.map (levelInclHom h L)` is a map of the filtered systems
(`levelQuotHom_comp_levelInclHom`) and hence commutes with inflation, the identity follows from
the computation rules `H2Profinite.joinAdd_ofLevel` and `H2Profinite.res_ofLevel`. -/
theorem H2Profinite.res_joinAdd {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x y : H2Profinite p U) :
    H2Profinite.res p h (H2Profinite.joinAdd p U x y) =
      H2Profinite.joinAdd p V (H2Profinite.res p h x) (H2Profinite.res p h y) := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := H2Profinite.ofLevel_surjective y
  rw [H2Profinite.joinAdd_ofLevel, H2Profinite.res_ofLevel, H2Profinite.res_ofLevel,
    H2Profinite.res_ofLevel, H2Profinite.joinAdd_ofLevel]
  congr 1
  rw [map_add]
  congr 1
  · rw [levelMap_apply, levelMap_apply, ← CategoryTheory.comp_apply, ← H2.map_comp,
      levelQuotHom_comp_levelInclHom h (le_sup_left : L ≤ L ⊔ L'), H2.map_comp,
      CategoryTheory.comp_apply]
  · rw [levelMap_apply, levelMap_apply, ← CategoryTheory.comp_apply, ← H2.map_comp,
      levelQuotHom_comp_levelInclHom h (le_sup_right : L' ≤ L ⊔ L'), H2.map_comp,
      CategoryTheory.comp_apply]

theorem loc_joinAdd {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : NK.BrauerHasse.OverFinitePrime K K') (x y : NK.BrauerHasse.H2Profinite p U) :
    (NK.BrauerHasse.H2Profinite.loc p U (NK.BrauerHasse.H2Profinite.joinAdd p U x y) A :
        NK.BrauerHasse.H2Profinite p (U ⊓ NK.BrauerHasse.stabSubgroup A.1)) =
      NK.BrauerHasse.H2Profinite.joinAdd p (U ⊓ NK.BrauerHasse.stabSubgroup A.1)
        (NK.BrauerHasse.H2Profinite.loc p U x A) (NK.BrauerHasse.H2Profinite.loc p U y A) := by
  rw [loc_eq_res p U A (H2Profinite.joinAdd p U x y)]
  rw [loc_eq_res p U A x, loc_eq_res p U A y]
  rw [H2Profinite.res_joinAdd]

end NK.LocalDecomposition
