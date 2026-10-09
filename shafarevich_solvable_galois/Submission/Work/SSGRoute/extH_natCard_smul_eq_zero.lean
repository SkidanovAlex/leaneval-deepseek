import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The order of a finite group kills its positive-degree `Ext`-cohomology

`cor ∘ extRes = [G : ⊥] = |G|` (`Work.SSGRoute.ext_corestriction`), and
`Extⁿ_{↥⊥}(ℤ, A) = 0` for `n > 0` since `ℤ = unitRep` is projective in `Rep Coeff 1`
(`Abelian.Ext.subsingleton_of_projective`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

theorem extH_natCard_smul_eq_zero {G : Type} [Group G] [Fintype G] (A : Rep Coeff G)
    {n : ℕ} (hn : 0 < n) (y : Abelian.Ext (unitRep G) A n) : Nat.card G • y = 0 := by
  classical
  haveI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup G)) := Classical.decRel _
  haveI : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  obtain ⟨cor, hcor⟩ := ext_corestriction (G := G) (S := ⊥)
  have h := hcor (unitRep G) A n y
  have hzero : extRes (⊥ : Subgroup G).subtype y = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    haveI : Projective (Rep.res (⊥ : Subgroup G).subtype (unitRep G)) := by
      rw [show Rep.res (⊥ : Subgroup G).subtype (unitRep G)
          = Rep.trivial Coeff (↥(⊥ : Subgroup G)) Coeff from rfl]
      infer_instance
    haveI : Subsingleton (Abelian.Ext (Rep.res (⊥ : Subgroup G).subtype (unitRep G))
        (Rep.res (⊥ : Subgroup G).subtype A) k.succ) :=
      Abelian.Ext.subsingleton_of_projective _ _ k
    exact Subsingleton.elim _ _
  rw [hzero, map_zero] at h
  rw [Subgroup.index_bot] at h
  exact h.symm

end Work.SSGRoute
