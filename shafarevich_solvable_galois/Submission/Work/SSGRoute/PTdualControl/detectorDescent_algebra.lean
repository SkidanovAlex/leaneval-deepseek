import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.E7cOmega.functional_of_ext_nonzero
import Submission.Work.SSGRoute.sylow_descend
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The algebraic half of the base-change descent for the unramified detector `C6`

Node `C6` (`Work.Sha2Lib.unramifiedDetector`) is stated for an *arbitrary* finite Galois extension
`K/k`: in particular it carries **no** hypothesis that `μ_p ⊆ K`.  The arithmetic routes to `C6`
that are on disk (the Kummer/Shapiro routes, `Work.SSGRoute.E7cC.*`, `Work.Sha2Lib.*`) all work
with Kummer theory over `K`, hence require a primitive `p`-th root of unity *in* `K`.  The way to
recover the general statement is to apply the `ζ_p ∈ K` result to the larger field
`K' = K(ζ_p)` (for which `[K' : K] ∣ p - 1`, so `p ∤ [K' : K]`) and to *descend*.

This file contains the two purely cohomological/linear-algebraic ingredients of that descent, with
no number theory at all.  Write `Γ = Gal(K/k)`, `Γ' = Gal(K'/k)`, `g : D_{w'} →* D_w` for the
restriction map on decomposition groups, `f : D_{q'} →* D_{w'}` for the level map, so that
`g.comp f` is the level map over `K`.

* **`levelPair_inflation`** — the *level-pairing square*: for a class `φ` over `D_w` and a class
  `h` over `D_{q'}`, the pairing computed over `K` equals the pairing computed over `K'` with the
  *inflated* class `extRes g φ` (pushed along the identity coefficient maps).  This is the
  transpose of `Work.SSGRoute.SylowIn.levelPair_restrict` (which restricts `h` instead).

* **`extRes_extDelta`** — naturality of the connecting map
  `δ : Hom_G(M, ℚ/ℤ) → Ext¹_G(M, ℤ)` of the coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` under
  change of group, and **`extDelta_ne_zero`** — `δ μ ≠ 0` for `μ ≠ 0` (`M` of exponent `p`), which
  is what makes the inflated class nonzero.

Together they reduce the descent to bookkeeping about places, ramification indices and the
`IntermediateField` structure; the arithmetic (and hence `μ_p ⊆ K`) is confined to the `K'`-side.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **The level-pairing square for an inflated coefficient class.**

For groups `G`, `G'`, `H`, homomorphisms `f : G' →* G` and `g : H →* G'`, a coefficient module
`M` over `G`, a class `φ ∈ Ext¹_G(M, ℤ)` and a class `h ∈ H¹(H, res_{f∘g} M)`, the level pairing
at the composite level map `f.comp g` on `K` equals the level pairing at the level map `g` on `K'`
paired with the inflation `extRes f φ` (transported along the identity coefficient maps).

This is the "inflation companion" of `Work.SSGRoute.SylowIn.levelPair_restrict`; in the descent it
is the step `K' → K`. -/
theorem levelPair_inflation {G G' H : Type} [Group G] [Group G'] [Group H]
    (f : G' →* G) (g : H →* G') (M : Rep.{0} Coeff G)
    (φ : Abelian.Ext.{0} M (unitRep G) 1) (h : extH (Rep.res (f.comp g) M) 1) :
    levelPair (f.comp g) (trivResInv (f.comp g) Coeff) φ h
      = levelPair g (trivResInv g Coeff)
          ((extRes f φ).comp (Abelian.Ext.mk₀ (trivResInv f Coeff)) (add_zero 1)) h := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor g)
        (Abelian.Ext.mapExactFunctor (Rep.resFunctor f) φ)
      = Abelian.Ext.mapExactFunctor (Rep.resFunctor (f.comp g)) φ := by
    simpa only [SSGRoute.PTExt.extRes] using
      (Work.SSGRoute.SylowDesc.extRes_comp_aux f g φ).symm
  have hcoe : Rep.resMap g (trivResInv f Coeff) ≫ trivResInv g Coeff
      = trivResInv (f.comp g) Coeff := rfl
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp, Abelian.Ext.mk₀_comp_mk₀, hcoe,
    Abelian.Ext.comp_assoc_of_second_deg_zero]

/-- **Naturality of the connecting map `δ` of `0 → ℤ → ℚ → ℚ/ℤ → 0` under change of group.**

For `f : H →* G`, a coefficient map `μ : M ⟶ ℚ/ℤ` over `G` and its pullback
`Rep.resMap f μ : res_f M ⟶ ℚ/ℤ` over `H`, the connecting class `δ_G μ = (mk₀ μ).comp extClass`
pulls back to `δ_H (res_f μ)`.

This is the identity that makes the *inflation* of an `Ext¹(M, ℤ)`-class computable: inflating
`δ μ` gives `δ (res μ)`, and the latter is nonzero as soon as `μ` is. -/
theorem extRes_extDelta {G H : Type} [Group G] [Group H] (f : H →* G)
    {M : Rep.{0} Coeff G} (μ : M ⟶ SSGRoute.E7cOmega.divRep G) :
    extRes f ((Abelian.Ext.mk₀ μ).comp
        (CategoryTheory.ShortComplex.ShortExact.extClass
          (SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1))
      = (Abelian.Ext.mk₀ (Rep.resMap f μ)).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (SSGRoute.E7cOmega.ratDivSES_shortExact (G := H))) (zero_add 1) := by
  have hext : ((CategoryTheory.ShortComplex.ShortExact.extClass
        (SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))).mapExactFunctor
          (Rep.resFunctor f))
      = CategoryTheory.ShortComplex.ShortExact.extClass
          (SSGRoute.E7cOmega.ratDivSES_shortExact (G := H)) := by
    rw [Abelian.Ext.mapExactFunctor_extClass]
  simp only [extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀, hext]

/-- **The connecting map is nonzero on nonzero functionals.**

For a finite module `M` of exponent `p` over a group `G` and a nonzero coefficient map
`μ : M ⟶ ℚ/ℤ`, the connecting class `δ μ ∈ Ext¹_G(M, ℤ)` is nonzero.  (The connecting map is
bijective onto `Ext¹_G(M, ℤ)` because `Hom_G(M, ℚ) = 0 = Ext¹_G(M, ℚ)`; this is
`Work.E7cOmega.exists_divRep_of_ext_nonzero_aux` read backwards.) -/
theorem extDelta_ne_zero {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    {M : Rep.{0} Coeff G} [Finite M] (hM : ∀ m : M, p • m = 0)
    {μ : M ⟶ SSGRoute.E7cOmega.divRep G} (hμ : μ ≠ 0) :
    (Abelian.Ext.mk₀ μ).comp
      (CategoryTheory.ShortComplex.ShortExact.extClass
        (SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) ≠ 0 := by
  intro h0
  have h₀ : Subsingleton (Abelian.Ext M (SSGRoute.E7cOmega.ratDivSES (G := G)).X₂ 0) :=
    SSGStage.subsingleton_ext_zero_ratRep M hM
  have h₁ : Subsingleton (Abelian.Ext M (SSGRoute.E7cOmega.ratDivSES (G := G)).X₂ 1) :=
    E7cOmega.subsingleton_ext_one_ratRep G p M hM
  have hinj := (Work.Ext.extClass_postcomp_bijective_Rep M
    (SSGRoute.E7cOmega.ratDivSES (G := G))
    (SSGRoute.E7cOmega.ratDivSES_shortExact (G := G)) (zero_add 1) h₀ h₁).1
  have hmk : (Abelian.Ext.mk₀ μ : Abelian.Ext M (SSGRoute.E7cOmega.ratDivSES (G := G)).X₃ 0)
      = 0 := by
    refine hinj ?_
    rw [Work.SSGRoute.ext_postcomp_apply, h0]
    exact (map_zero _).symm
  have hμ0 : μ = 0 := by
    have h1 : Abelian.Ext.addEquiv₀
        (Abelian.Ext.mk₀ μ : Abelian.Ext M (SSGRoute.E7cOmega.ratDivSES (G := G)).X₃ 0) = μ := by
      rw [← Abelian.Ext.addEquiv₀_symm_apply μ]
      exact AddEquiv.apply_symm_apply _ _
    rw [← h1, hmk, map_zero]
  exact hμ hμ0

end Work.SSGRoute.PTdualControl
