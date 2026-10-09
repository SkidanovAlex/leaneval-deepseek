import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.e1a_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The connecting map of the coefficient LES preserves the localisation kernel

For a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with projective middle term,
the syzygy shift `Work.SSGRoute.PT.e1aShiftEquiv S hS Y n hn : Extⁿ(X₁,Y) ≃+ Extⁿ⁺¹(X₃,Y)` is the
connecting map `x ↦ hS.extClass ∘ x` (`Work.SSGRoute.PT.e1aShiftEquiv_apply`).  Its *coefficient*
naturality — the associativity of `Abelian.Ext.comp` —

`(e1aShiftEquiv S hS Y n hn x) ∘ mk₀ f = e1aShiftEquiv S hS Y' n hn (x ∘ mk₀ f)`

is the engine that lets a *localisation* hypothesis on a class `y ∈ Ext²(S.X₃, Kˣ)` be transported
through the shift: for the coefficient map `ideleIncl k K : Kˣ → 𝕀_K` one gets

`extToIdeles (δ y) = δ (extToIdeles y) = δ 0 = 0`,

so the connecting map `δ = (e1aShiftEquiv S hS unitsK 1 _).symm` descends to the localisation
kernels `ker (extToIdeles)`.  This is the connecting half of the snake step of the dévissage in the
coefficient `E`.
-/

open CategoryTheory

universe w

namespace Work.SSGRoute.ExtChain

section General

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- **Coefficient naturality of the syzygy shift.**  For a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` with projective middle term, degrees `n ≥ 1`, and a morphism of
coefficients `f : Y ⟶ Y'`, postcomposing the shift with `mk₀ f` equals shifting the postcomposition:

`(e1aShiftEquiv S hS Y n hn x) ∘ mk₀ f = e1aShiftEquiv S hS Y' n hn (x ∘ mk₀ f)`.

Both sides are `hS.extClass ∘ (x ∘ mk₀ f)` — the statement is associativity of `Ext.comp`, and it
records that the syzygy shift is natural in the *second* variable (the coefficient).  This is the
`Ext`-level content of the snake step: applied to the inclusion `Kˣ → 𝕀_K` it says that the
connecting map of a presentation descends to the localisation kernels. -/
theorem e1aShiftEquiv_natural_coeff {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y Y' : C) (f : Y ⟶ Y') (n : ℕ) (hn : 1 ≤ n) (x : Abelian.Ext.{w} S.X₁ Y n) :
    (Work.SSGRoute.PT.e1aShiftEquiv S hS Y n hn x).comp (Abelian.Ext.mk₀ f)
        (add_zero (n + 1)) =
      Work.SSGRoute.PT.e1aShiftEquiv S hS Y' n hn
        (x.comp (Abelian.Ext.mk₀ f) (add_zero n)) := by
  rw [Work.SSGRoute.PT.e1aShiftEquiv_apply, Work.SSGRoute.PT.e1aShiftEquiv_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

end General

/-- The connecting map of the coefficient LES (in the first variable) preserves the localisation
kernel `ker (extToIdeles)`: for a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` with `X₂`
projective and `y : Ext²(S.X₃, Kˣ)` with `extToIdeles y = 0`, the class
`(e1aShiftEquiv S hS unitsK 1 _).symm y : Ext¹(S.X₁, Kˣ)` also has vanishing idèle localisation.
This is the connecting half of the snake step of the dévissage in the coefficient `E`. -/
theorem shift_symm_extToIdeles_eq_zero_gen
    {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    {S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))}
    (hS : S.ShortExact) [CategoryTheory.Projective S.X₂]
    (y : CategoryTheory.Abelian.Ext.{0} S.X₃ (SSGRoute.PTExt.unitsK k K) 2)
    (h : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    SSGRoute.PTExt.extToIdeles (k := k)
      ((Work.SSGRoute.PT.e1aShiftEquiv S hS (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1)).symm y) = 0 := by
  -- Name the class `x = δ y ∈ Ext¹(S.X₁, Kˣ)`; it is characterised by `hS.extClass ∘ x = y`.
  set x : CategoryTheory.Abelian.Ext.{0} S.X₁ (SSGRoute.PTExt.unitsK k K) 1 :=
    (Work.SSGRoute.PT.e1aShiftEquiv S hS (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1)).symm y with hx
  have hxy : Work.SSGRoute.PT.e1aShiftEquiv S hS (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1) x = y := by
    rw [hx]
    exact AddEquiv.apply_symm_apply _ y
  rw [Work.SSGRoute.PT.e1aShiftEquiv_apply] at hxy
  -- It suffices to check the vanishing after applying the *injective* shift at the coefficient
  -- `𝕀_K`, where the two sides are `hS.extClass ∘ (x ∘ mk₀ ideleIncl)` and `extToIdeles y = 0`.
  apply (Work.SSGRoute.PT.e1aShiftEquiv S hS (SSGRoute.PTExt.idelesK k K) 1 (le_refl 1)).injective
  rw [map_zero, Work.SSGRoute.PT.e1aShiftEquiv_apply]
  rw [← h, ← hxy]
  rw [SSGRoute.PTExt.extToIdeles]
  rw [SSGRoute.PTExt.extToIdeles]
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]

end Work.SSGRoute.ExtChain
