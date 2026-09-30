/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sections of the graph closure over an affine open of the base inject into `K(X)`

Let `g : X ⇢ Y` be a partial `S`-map, with `X` integral and locally Noetherian and `Y`
proper over `S`, and let `Γ` be the closure of the graph of `g` (the scheme-theoretic image of
`Work.Domain.PartialMap.graphMap S g`).  For an affine open `U ⊆ X` we produce a ring
homomorphism

`φ : Γ(Γ, pr₁ ⁻¹ᵁ U) ⟶ K(X)`

which is injective, and which makes the triangle

```
Γ(X, U) ---pr₁.app U---> Γ(Γ, pr₁ ⁻¹ᵁ U)
   \                          |
    \ algebraMap               | φ
     v                         v
                K(X)  <--------
```

commute.

The map is "restrict a section of the graph to the generic point of the graph closure, and then
read it in `K(X)`": it is the composite of `germToFunctionField` of `Γ` at its generic point with
the comparison map `Work.Domain.PartialMap.theta` (see `Theta.lean`).  Injectivity follows because
`Γ` is integral (`Work.Domain.Engine.isIntegral_graph`), so that `germToFunctionField` is
injective, and because `theta` is a ring homomorphism out of the *field* `K(Γ)`.  Commutativity is
the identity `Work.Domain.Engine.comp_stalkMap`, together with the generic point computation
`Work.Domain.Engine.pr₁_genericPoint`.
-/
import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Engine.isIntegral_graph
import Submission.Work.Domain.Engine.pr1_genericPoint_facts
import Submission.Work.Domain.Engine.comp_stalkMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped AlgebraicGeometry

universe u

namespace Work.Domain.Engine

theorem exists_injective_sections_to_functionField {S X Y : AlgebraicGeometry.Scheme} [X.Over S]
    [Y.Over S] [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U] :
    ∃ φ : (Work.Domain.PartialMap.graph S g).presheaf.obj
          (Opposite.op ((TopologicalSpace.Opens.map
            (Work.Domain.PartialMap.pr₁ S g).base).obj U)) →+* X.functionField,
      Function.Injective φ ∧
      ∀ r : X.presheaf.obj (Opposite.op U),
        φ ((Work.Domain.PartialMap.pr₁ S g).app U r) =
          algebraMap (X.presheaf.obj (Opposite.op U)) X.functionField r := by
  have _hU : AlgebraicGeometry.IsAffineOpen U := hU
  -- The graph closure is integral, so `germToFunctionField` on it is injective.
  haveI hIntG : IsIntegral (Work.Domain.PartialMap.graph S g) := isIntegral_graph (S := S) g
  haveI hIrrDom : IrreducibleSpace ↥g.domain.toScheme := irreducibleSpace_toScheme_domain g
  -- The generic point of `X` lies in the nonempty open `U`.
  obtain ⟨x₀⟩ := ‹Nonempty U›
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).specializes (y := x₀.1) trivial).mem_open U.isOpen x₀.2
  -- `pr₁` sends the generic point of the graph closure to the generic point of `X`.
  have hgen : (Work.Domain.PartialMap.pr₁ S g) (genericPoint (Work.Domain.PartialMap.graph S g))
      = genericPoint X := pr₁_genericPoint (S := S) g
  have hγ : genericPoint (Work.Domain.PartialMap.graph S g) ∈
      (Work.Domain.PartialMap.pr₁ S g) ⁻¹ᵁ U := by
    show (Work.Domain.PartialMap.pr₁ S g) (genericPoint (Work.Domain.PartialMap.graph S g)) ∈ U
    rw [hgen]; exact hηU
  haveI hneU' : Nonempty ((Work.Domain.PartialMap.pr₁ S g) ⁻¹ᵁ U) :=
    ⟨⟨genericPoint (Work.Domain.PartialMap.graph S g), hγ⟩⟩
  -- `φ` is `θ` at the generic point of the graph closure, composed with the germ map.
  refine ⟨(Work.Domain.PartialMap.theta g (genericPoint (Work.Domain.PartialMap.graph S g))).hom.comp
      (Scheme.germToFunctionField (Work.Domain.PartialMap.graph S g)
        ((Work.Domain.PartialMap.pr₁ S g) ⁻¹ᵁ U)).hom, ?_, ?_⟩
  · -- injectivity: the germ map is injective (`Γ` integral) and `θ` is a map out of a field
    intro a b hab
    exact (Scheme.germToFunctionField_injective (Work.Domain.PartialMap.graph S g)
        ((Work.Domain.PartialMap.pr₁ S g) ⁻¹ᵁ U))
      (RingHom.injective (Work.Domain.PartialMap.theta g
        (genericPoint (Work.Domain.PartialMap.graph S g))).hom hab)
  · -- compatibility with the structure map `pr₁.app U`
    intro r
    show (Work.Domain.PartialMap.theta g (genericPoint (Work.Domain.PartialMap.graph S g))).hom
        ((Scheme.germToFunctionField (Work.Domain.PartialMap.graph S g)
          ((Work.Domain.PartialMap.pr₁ S g) ⁻¹ᵁ U)) ((Work.Domain.PartialMap.pr₁ S g).app U r))
      = algebraMap ↑(X.presheaf.obj (Opposite.op U)) X.functionField r
    have hx : (Work.Domain.PartialMap.pr₁ S g)
        (genericPoint (Work.Domain.PartialMap.graph S g)) ∈ U := hγ
    -- identify the germ of the section with the stalk map applied to the germ of `r`
    have hgsa := Scheme.Hom.germ_stalkMap_apply (Work.Domain.PartialMap.pr₁ S g) U
      (genericPoint (Work.Domain.PartialMap.graph S g)) hx r
    rw [← hgsa]
    -- `θ ∘ (pr₁).stalkMap = algebraMap`
    have hcs := Work.Domain.Engine.comp_stalkMap (S := S) g
      (genericPoint (Work.Domain.PartialMap.graph S g))
    have hcs' : ∀ z, (Work.Domain.PartialMap.theta g
          (genericPoint (Work.Domain.PartialMap.graph S g))).hom
        ((Work.Domain.PartialMap.pr₁ S g).stalkMap
          (genericPoint (Work.Domain.PartialMap.graph S g)) z)
        = algebraMap (X.presheaf.stalk ((Work.Domain.PartialMap.pr₁ S g)
            (genericPoint (Work.Domain.PartialMap.graph S g)))) X.functionField z := by
      intro z
      have hh := congrArg CommRingCat.Hom.hom hcs
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hh
      exact DFunLike.congr_fun hh z
    rw [hcs' (X.presheaf.germ U ((Work.Domain.PartialMap.pr₁ S g)
      (genericPoint (Work.Domain.PartialMap.graph S g))) hx r)]
    -- the germ of `r` at the generic point of `X` is `algebraMap r`
    rw [Scheme.algebraMap_germ_eq_germToFunctionField X hx r]
    rfl

end Work.Domain.Engine
