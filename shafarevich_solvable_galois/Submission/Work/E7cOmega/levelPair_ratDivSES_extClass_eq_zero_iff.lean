import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.E7cOmega.extClass_comp_injective
import Submission.Work.SSGRoute.E7cOmega.levelPair_ratDivSES_extClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nonvanishing of the level pairing is detected by the `ℚ/ℤ`-coefficient functional

Write `φ := δ(μ) = (mk₀ μ).comp (ratDivSES G).extClass ∈ Ext¹_G(M, ℤ)` for a coefficient map
`μ : M ⟶ ℚ/ℤ` over `G`, and put `c := μ ∘ h = h.comp (mk₀ (res_f μ)) ∈ H¹(H, ℚ/ℤ)` for
`h ∈ H¹(H, res_f M)`.

The pairing formula `Work.SSGRoute.E7cOmega.levelPair_ratDivSES_extClass` expresses
`levelPair f (trivResInv f ℤ) φ h`, the image of `c` under the connecting map of the coefficient
sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` over `H`, as `c.comp (ratDivSES H).extClass` (the scalar
`trivResInv f ℤ = 𝟙` contributes nothing).

Since `H¹(H, ℚ) = Ext¹_H(ℤ, ℚ) = 0` — the hypothesis `hsub` of the statement — the connecting map
`x ↦ x.comp (ratDivSES H).extClass` is injective
(`Work.SSGRoute.E7cOmega.extClass_comp_injective`), so it detects zero:

  `levelPair f (trivResInv f ℤ) φ h = 0  ↔  μ ∘ h = 0`.
-/

namespace Work.E7cOmega

/- The computation of the pairing, together with the injectivity of the connecting map for the
coefficient sequence over `H`.  The auxiliary statement has the same shape as the target; the
only reason for the separate declaration is that the (project-standard) defeq options are needed
for the `Ext`-bookkeeping, while the target statement is elaborated with the default ones. -/
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem levelPair_ratDivSES_extClass_eq_zero_iff_aux {G H : Type} [Group G] [Group H]
    (f : H →* G) {M : Rep.{0} SSGRoute.PTExt.Coeff G}
    (μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G)
    (h : SSGRoute.PTExt.extH (Rep.res f M) 1)
    (hsub : Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep H)
      (Work.SSGRoute.E7cOmega.ratRep H) 1)) :
    SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff)
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)) h = 0
      ↔ h.comp (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap f μ)) (add_zero 1) = 0 := by
  -- the coefficient map `trivResInv f ℤ` is the identity, so it drops out of the composition
  rw [Work.SSGRoute.E7cOmega.levelPair_ratDivSES_extClass f μ h]
  rw [show SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff =
      CategoryTheory.CategoryStruct.id (SSGRoute.PTExt.unitRep H) from rfl]
  -- left-associate, so that `c := h.comp (mk₀ (resMap f μ))` appears as a factor
  rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
  constructor
  · -- vanishing of the pairing implies vanishing of `μ ∘ h`, by injectivity of `δ` over `H`
    intro hz
    exact Work.SSGRoute.E7cOmega.extClass_comp_injective H
      (Work.SSGRoute.E7cOmega.ratDivSES (G := H))
      (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := H)) hsub _ _
      (by simpa using hz)
  · intro hz
    rw [hz]
    simp

theorem levelPair_ratDivSES_extClass_eq_zero_iff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M : Rep.{0} SSGRoute.PTExt.Coeff G} (μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G)
    (h : SSGRoute.PTExt.extH (Rep.res f M) 1)
    (hsub : Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep H)
      (Work.SSGRoute.E7cOmega.ratRep H) 1)) :
    SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff)
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)) h = 0
      ↔ h.comp (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap f μ)) (add_zero 1) = 0 :=
  levelPair_ratDivSES_extClass_eq_zero_iff_aux f μ h hsub

end Work.E7cOmega
