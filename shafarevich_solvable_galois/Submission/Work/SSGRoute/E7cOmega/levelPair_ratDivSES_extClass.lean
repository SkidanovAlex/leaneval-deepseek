import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level pairing through the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`

Third piece of the local-duality infrastructure for
`Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`, and the exact analogue of the
on-disk `Work.SSGRoute.levelPair_pushClass` (which does the same job for the `p`-torsion sequence
`0 → ℤ →^p ℤ → ℤ/p → 0`).

For a coefficient morphism `μ : M ⟶ ℚ/ℤ` over `G`, put `φ := δ(μ) = (mk₀ μ).comp (ratDivSES G).extClass
∈ Ext¹_G(M, ℤ)`.  Then for `h ∈ H¹(H, res_f M)`, the level pairing of `φ` with `h` is the
connecting image (over `H`) of the composite `μ ∘ h`:

  `levelPair f (trivResInv f Coeff) φ h
     = (h.comp (mk₀ (res_f μ ≫ trivResInv f ℚ/ℤ))).comp (ratDivSES H).extClass`.

Consequently (with `Work.SSGRoute.E7cOmega.extClass_comp_injective` for the sequence over `H`):

  `levelPair … φ h ≠ 0  ⟺  μ ∘ res_f h ≠ 0`,

which is the local half of C6: the pairing is detected exactly by the `ℚ/ℤ`-valued functional.
-/

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace Work.SSGRoute.E7cOmega

variable {G H : Type} [Group G] [Group H]

/-- **The pairing formula for the `ℚ/ℤ` coefficient sequence.** -/
theorem levelPair_ratDivSES_extClass (f : H →* G)
    {M : Rep.{0} SSGRoute.PTExt.Coeff G} (μ : M ⟶ divRep G)
    (h : extH (Rep.res f M) 1) :
    levelPair f (trivResInv f SSGRoute.PTExt.Coeff)
        ((Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (ratDivSES_shortExact (G := G))) (zero_add 1)) h
      = h.comp ((Abelian.Ext.mk₀ (Rep.resMap f μ)).comp
          ((CategoryTheory.ShortComplex.ShortExact.extClass
              (ratDivSES_shortExact (G := H))).comp
            (Abelian.Ext.mk₀ (trivResInv f SSGRoute.PTExt.Coeff)) (add_zero 1))
          (zero_add 1)) rfl := by
  have hext : ((CategoryTheory.ShortComplex.ShortExact.extClass
        (ratDivSES_shortExact (G := G))).mapExactFunctor (Rep.resFunctor f)) =
      CategoryTheory.ShortComplex.ShortExact.extClass (ratDivSES_shortExact (G := H)) := by
    rw [Abelian.Ext.mapExactFunctor_extClass]
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, hext,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

end Work.SSGRoute.E7cOmega
