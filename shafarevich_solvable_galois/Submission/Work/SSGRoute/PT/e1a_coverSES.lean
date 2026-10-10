import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.PT.e1a_chain
import Submission.Work.SSGRoute.PT.e1a_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the comparison of the canonical presentations `0 → R_X → F_X → X → 0`

For `h : X ⟶ Y` a morphism of `Gal(K/k)`-modules, the canonical presentations
`Work.SSGRoute.freeCoverSES X` and `Work.SSGRoute.freeCoverSES Y` are compared by the morphism of
short complexes with components `freeMapKernel h`, `freeMap h`, `h` (the two squares being
`freeMapKernel_ι` and `freeMap_freeCover`).  This file records that morphism, the projectivity of
the middle terms, and the resulting specialisation of the naturality of the syzygy shift
`Work.SSGRoute.PT.e1aShiftEquiv`: the shift of the canonical presentation is compatible with the
comparison.

This is the first square of the naturality clause of `Work.SSGRoute.PT.e1a_ext_sha2_bridge`: the
`Ext²`-side of the chain catches a class `y ∈ Ext²(X,Kˣ)` by the comparison of the two canonical
presentations.
-/

open CategoryTheory

namespace Work.SSGRoute

noncomputable section

section CoverSES

variable {G : Type} [Group G] [Fintype G]

/-- The middle term of the canonical presentation is the free representation on `X.V`, hence
projective. -/
instance instProjectiveFreeCoverSES (X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Projective (freeCoverSES X).X₂ :=
  Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := G) (α := X.V)

/-- **The comparison morphism of canonical presentations** induced by `h : X ⟶ Y`: the syzygy map
`freeMapKernel h` on the kernels, `freeMap h` on the free covers and `h` on the quotients. -/
noncomputable def freeCoverSESMap {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} (h : X ⟶ Y) :
    freeCoverSES X ⟶ freeCoverSES Y where
  τ₁ := freeMapKernel h
  τ₂ := freeMap h
  τ₃ := h
  comm₁₂ := freeMapKernel_ι h
  comm₂₃ := freeMap_freeCover h

@[simp] theorem freeCoverSESMap_τ₁ {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} (h : X ⟶ Y) :
    (freeCoverSESMap h).τ₁ = freeMapKernel h := rfl

@[simp] theorem freeCoverSESMap_τ₂ {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} (h : X ⟶ Y) :
    (freeCoverSESMap h).τ₂ = freeMap h := rfl

@[simp] theorem freeCoverSESMap_τ₃ {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} (h : X ⟶ Y) :
    (freeCoverSESMap h).τ₃ = h := rfl

end CoverSES

end

end Work.SSGRoute

namespace Work.SSGRoute.PT

open CategoryTheory

/-- **The first square of the naturality of the `Ext`-side chain**: the syzygy shift of the
canonical presentation is compatible with the comparison morphism `freeCoverSESMap h`.  For
`x : Ext¹(R_Y, Z)` (the syzygy of `Y`), shifting the precomposition of `x` along `freeMapKernel h`
equals the precomposition of the shift of `x` along `h`. -/
theorem e1aShiftEquiv_freeCoverSES {G : Type} [Group G] [Fintype G]
    {X Y : Rep.{0} SSGRoute.PTExt.Coeff G} (h : X ⟶ Y) (Z : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ∀ x : CategoryTheory.Abelian.Ext (Work.SSGRoute.freeCoverSES Y).X₁ Z 1,
      e1aShiftEquiv (Work.SSGRoute.freeCoverSES X)
          (Work.SSGRoute.freeCoverSES_shortExact X) Z 1 (by norm_num)
          ((CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel h)).comp x (zero_add 1))
        = (CategoryTheory.Abelian.Ext.mk₀ h).comp
            (e1aShiftEquiv (Work.SSGRoute.freeCoverSES Y)
              (Work.SSGRoute.freeCoverSES_shortExact Y) Z 1 (by norm_num) x) (zero_add 2) := by
  intro x
  exact e1aShiftEquiv_natural (Work.SSGRoute.freeCoverSES_shortExact X)
    (Work.SSGRoute.freeCoverSES_shortExact Y) (Work.SSGRoute.freeCoverSESMap h)
    Z 1 (by norm_num) x

end Work.SSGRoute.PT
