import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.ext_shift_natural_res
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the syzygy shift as a *named* map, and its naturality in the first variable

The chain of the `Ext`-side dictionary of node `E1a` starts with the syzygy shift
`Ext²_G(E',Kˣ) ≅ Ext¹_G(R,Kˣ)`, where `0 → R → F → E' → 0` is the canonical free cover of `E'`.

The workspace's `Work.SSGRoute.ext_shift_of_projective_presentation` only produces the shift as a
`Nonempty`-witness (and for a `Classical.choose`d cover), which is not enough for the *naturality*
clause of `Work.SSGRoute.PT.e1a_ext_sha2_bridge`: the two coefficients `E₁'`, `E₂'` need shifts
that are compatible with the comparison morphism of the two canonical resolutions.  This file
provides the shift as a named `AddEquiv` — the connecting map `S.extClass` of the presentation,
which is a bijection in degrees `≥ 1` (`Work.SSGRoute.ExtChain.bijective_extClass_precomp`) — and
proves its naturality with respect to a morphism of short complexes, which reduces to Mathlib's
`ShortComplex.ShortExact.extClass_naturality`.
-/

open CategoryTheory

universe w

namespace Work.SSGRoute.PT

noncomputable section

section General

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- **The syzygy shift, as a named isomorphism.**  For a short exact sequence
`S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` with projective middle term and `n ≥ 1`, the connecting map
`S.extClass` gives an isomorphism `Ext^n(S.X₁,Y) ≅ Ext^{n+1}(S.X₃,Y)`.  Being the connecting map
itself, it is compatible with morphisms of short complexes (`e1aShiftEquiv_natural`). -/
noncomputable def e1aShiftEquiv (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) (hn : 1 ≤ n) :
    Abelian.Ext.{w} S.X₁ Y n ≃+ Abelian.Ext.{w} S.X₃ Y (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.precomp Y (by omega))
    (Work.SSGRoute.ExtChain.bijective_extClass_precomp hS Y hn (by omega))

/-- The computation rule of the shift: it is the connecting map `S.extClass`. -/
theorem e1aShiftEquiv_apply {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) (hn : 1 ≤ n) (x : Abelian.Ext.{w} S.X₁ Y n) :
    e1aShiftEquiv S hS Y n hn x = hS.extClass.comp x (by omega : 1 + n = n + 1) := by
  rw [e1aShiftEquiv, AddEquiv.ofBijective_apply]
  rfl

variable {S₁ S₂ : ShortComplex C}

/-- **Naturality of the syzygy shift in the first variable.**  For a morphism of short exact
sequences `φ : S₁ ⟶ S₂` with projective middle terms and `n ≥ 1`, pushing an `Ext^n(S₂.X₁,Y)`-class
along `φ.τ₁` and shifting equals shifting and pushing along `φ.τ₃`:

`e1aShiftEquiv S₁ (x ∘ mk₀ φ.τ₁) = e1aShiftEquiv S₂ (x) ∘ mk₀ φ.τ₃`.

This is what makes the `Ext`-side dictionary of `E1a` functorial in the coefficient: the two
canonical resolutions `freeCoverSES E₁'`, `freeCoverSES E₂'` are compared by
`Work.SSGRoute.freeMapKernel` and `Work.SSGRoute.freeMap`. -/
theorem e1aShiftEquiv_natural (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    [Projective S₁.X₂] [Projective S₂.X₂] (φ : S₁ ⟶ S₂) (Y : C) (n : ℕ) (hn : 1 ≤ n)
    (x : Abelian.Ext.{w} S₂.X₁ Y n) :
    e1aShiftEquiv S₁ h₁ Y n hn ((Abelian.Ext.mk₀ φ.τ₁).comp x (zero_add n))
      = (Abelian.Ext.mk₀ φ.τ₃).comp (e1aShiftEquiv S₂ h₂ Y n hn x) (zero_add (n + 1)) := by
  rw [e1aShiftEquiv_apply, e1aShiftEquiv_apply,
    ← CategoryTheory.Abelian.Ext.comp_assoc h₁.extClass (Abelian.Ext.mk₀ φ.τ₁) x
      (add_zero 1) (zero_add n) (by omega)]
  rw [CategoryTheory.ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]
  rw [CategoryTheory.Abelian.Ext.comp_assoc (a₁₂ := 1) (a₂₃ := n + 1) (a := n + 1)
    (Abelian.Ext.mk₀ φ.τ₃) h₂.extClass x (zero_add 1) (by omega) (by omega)]

/-- **The degree-zero case of the same naturality**: pushing an `Ext⁰(S₂.X₁,Y)`-class along
`φ.τ₁` and applying the connecting map `h₂.extClass` equals applying `h₁.extClass` and pushing along
`φ.τ₃`.  (This is the form needed for the naturality of the `E1c` dictionary, whose first map is
`hS.extClass.precomp (unitsK k K) (1 + 0 = 1)`.) -/
theorem extClass_precomp_natural_zero (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    [Projective S₁.X₂] [Projective S₂.X₂] (φ : S₁ ⟶ S₂) (Y : C)
    (x : Abelian.Ext.{w} S₂.X₁ Y 0) :
    (h₁.extClass.precomp Y (by omega : 1 + 0 = 1))
        ((Abelian.Ext.mk₀ φ.τ₁).comp x (zero_add 0)) =
      (Abelian.Ext.mk₀ φ.τ₃).comp ((h₂.extClass.precomp Y (by omega : 1 + 0 = 1)) x)
        (zero_add 1) := by
  rw [show (h₁.extClass.precomp Y (by omega : 1 + 0 = 1))
        ((Abelian.Ext.mk₀ φ.τ₁).comp x (zero_add 0)) =
      h₁.extClass.comp ((Abelian.Ext.mk₀ φ.τ₁).comp x (zero_add 0))
        (by omega : 1 + 0 = 1) from rfl]
  rw [← CategoryTheory.Abelian.Ext.comp_assoc (a₁₂ := 1) (a₂₃ := 0) (a := 1)
    h₁.extClass (Abelian.Ext.mk₀ φ.τ₁) x (add_zero 1) (zero_add 0) (by omega)]
  rw [CategoryTheory.ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]
  rw [CategoryTheory.Abelian.Ext.comp_assoc (a₁₂ := 1) (a₂₃ := 1) (a := 1)
    (Abelian.Ext.mk₀ φ.τ₃) h₂.extClass x (zero_add 1) (by omega) (by omega)]
  rfl

end General

end

end Work.SSGRoute.PT
