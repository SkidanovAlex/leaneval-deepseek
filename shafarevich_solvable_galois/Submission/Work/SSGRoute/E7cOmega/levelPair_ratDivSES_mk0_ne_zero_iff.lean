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

namespace Work.SSGRoute.E7cOmega

/- The `Ext`-bookkeeping of the criterion needs the defeq options used throughout `E7cOmega/*`
(the composition `Ext.comp` is only propositionally — not definitionally — well behaved across the
two restriction functors), while the *statement* of the criterion is elaborated with the default
options.  Hence the argument is carried out here, in a declaration with exactly the same statement,
and the target theorem is the (elaboration-neutral) application of it. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem levelPair_ratDivSES_mk0_ne_zero_iff_aux {G H : Type} [Group G] [Group H] (f : H →* G)
    {M : Rep.{0} SSGRoute.PTExt.Coeff G} (μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G)
    (h : SSGRoute.PTExt.extH (Rep.res f M) 1)
    (hsub : Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep H)
      (Work.SSGRoute.E7cOmega.ratRep H) 1)) :
    SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff)
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)) h ≠ 0
      ↔ h.comp (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap f μ)) (add_zero 1) ≠ 0 := by
  -- the pairing formula `levelPair_ratDivSES_extClass`, expressing the left-hand side as the
  -- connecting image over `H` of the composite `μ ∘ h`
  rw [levelPair_ratDivSES_extClass f μ h]
  -- the coefficient morphism `trivResInv f ℤ : res_f ℤ_G ⟶ ℤ_H` *is* the identity of `ℤ_H`
  -- (both objects are the trivial `H`-module on `ℤ`), so the scalar drops out
  rw [show SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff =
      CategoryTheory.CategoryStruct.id (SSGRoute.PTExt.unitRep H) from rfl]
  -- left-associate, so that `c := h.comp (mk₀ (resMap f μ)) : H¹(H, ℚ/ℤ)` is a factor
  rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]
  constructor
  · -- vanishing of `c` kills the pairing
    intro hne hc0
    apply hne
    rw [hc0]
    simp
  · -- conversely the pairing is `c.comp (ratDivSES H).extClass`, and the connecting map over `H`
    -- detects zero because `H¹(H, ℚ) = 0` (`extClass_comp_injective`)
    intro hne hz
    apply hne
    exact SSGRoute.E7cOmega.extClass_comp_injective H
      (ratDivSES (G := H)) (ratDivSES_shortExact (G := H)) hsub _ _
      (by simpa using hz)

/-- **The `ℚ/ℤ`-criterion for the level pairing with a connecting class `δ μ`.**

For a group homomorphism `f : H →* G`, a coefficient morphism `μ : M ⟶ ℚ/ℤ` over `G`
(`Work.SSGRoute.E7cOmega.divRep`), and a class `h ∈ H¹(H, res_f M)`:

  `levelPair f (trivResInv f ℤ) ((mk₀ μ).comp (ratDivSES G).extClass) h ≠ 0
      ↔ h.comp (mk₀ (res_f μ)) ≠ 0`,

i.e. the Yoneda pairing of `δ(μ) = (mk₀ μ).comp (ratDivSES G).extClass` with `h` vanishes exactly
when the `ℚ/ℤ`-valued functional `μ` kills the class `h`.

This is the local half of node `C6` (`Work.SSGRoute.SSGStage.unramifiedDetector`); it is stated (with
`sorry`) as `Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff` and is proved here from the
on-disk pairing formula `Work.SSGRoute.E7cOmega.levelPair_ratDivSES_extClass` plus the `δ`-injectivity
`Work.SSGRoute.E7cOmega.extClass_comp_injective` for the sequence over `H` (both sorry-free).  The
`Subsingleton` hypothesis is `H¹(H, ℚ) = 0`, supplied by finiteness of `H`.

Proof (reviewers' sketch): the pairing formula gives
`LHS = ((h.comp (mk₀ (resMap f μ))).comp extClass_H).comp (mk₀ (trivResInv f Coeff))`; the second
factor is invertible (`trivRes f Coeff` is a two-sided inverse) and the first map is injective by
`extClass_comp_injective` with `S = ratDivSES H` (`ratDivSES_X₂` is `rfl`).  The remaining work is
`Ext`-associativity/degree bookkeeping (the files `E7cOmega/*` use the local helpers
`Abelian.Ext.comp_assoc_of_second_deg_zero` and `comp_assoc_of_third_deg_zero` for this). -/
theorem levelPair_ratDivSES_mk0_ne_zero_iff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M : Rep.{0} SSGRoute.PTExt.Coeff G} (μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G)
    (h : SSGRoute.PTExt.extH (Rep.res f M) 1)
    (hsub : Subsingleton (CategoryTheory.Abelian.Ext (SSGRoute.PTExt.unitRep H)
      (Work.SSGRoute.E7cOmega.ratRep H) 1)) :
    SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f SSGRoute.PTExt.Coeff)
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1)) h ≠ 0
      ↔ h.comp (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap f μ)) (add_zero 1) ≠ 0 :=
  levelPair_ratDivSES_mk0_ne_zero_iff_aux f μ h hsub

end Work.SSGRoute.E7cOmega
