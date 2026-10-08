import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.Step5.mulAut_eight_order21

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Aut(V) ≅ GL(3,2)` for `V` elementary abelian of order `8`

Let `V` be a finite group of order `8` all of whose elements are involutions.  Then `V` is
elementary abelian of rank `3`, and its automorphism group is `GL(3,F₂) = GL32`.

The substance of the classification of `V` is in `Work.Hering.Step5.iso_fin3`, which produces a
group isomorphism `V ≃* Multiplicative (Fin 3 → ZMod 2)`; the remaining step is the natural
identification `MulAut (Multiplicative M) ≃* (M ≃ₗ[ZMod 2] M)` for a `ZMod 2`-module `M`
(`MulAutMultiplicative` composed with `multAddAutLinearEquiv` below).
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

noncomputable section

/-- An additive automorphism of a `ZMod 2`-module is the same thing as a `ZMod 2`-linear
automorphism: the `ZMod 2`-action on an abelian group of exponent `2` is determined. -/
def multAddAutLinearEquiv (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] :
    Multiplicative (AddAut M) ≃* (M ≃ₗ[ZMod 2] M) where
  toFun a := LinearEquiv.ofBijective
    (((Multiplicative.toAdd (α := AddAut M) a) : M →+ M).toZModLinearMap 2)
    (Multiplicative.toAdd (α := AddAut M) a).bijective
  invFun f := Multiplicative.ofAdd f.toAddEquiv
  left_inv a := by ext x; simp [LinearEquiv.ofBijective]
  right_inv f := by ext x; simp [LinearEquiv.ofBijective]
  map_mul' a b := by ext x; simp [LinearEquiv.ofBijective]

/-- `MulAut (Multiplicative M) ≃* (M ≃ₗ[ZMod 2] M)` for a `ZMod 2`-module `M`. -/
def mulAutMultiplicativeLinearEquiv (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] :
    MulAut (Multiplicative M) ≃* (M ≃ₗ[ZMod 2] M) :=
  (MulAutMultiplicative M).trans (multAddAutLinearEquiv M)

/-- **`Aut(V) ≅ GL(3,2)`.**  A finite group of order `8` of exponent `2` is elementary abelian of
rank `3`, hence its automorphism group is `GL(3,F₂) = GL32`. -/
theorem gl32_mulAut_V_iso {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 8)
    (hexp : ∀ x : V, x * x = 1) :
    Nonempty (Work.Hering.GL32 ≃* MulAut V) := by
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp
  exact ⟨((MulAut.congr e).trans (mulAutMultiplicativeLinearEquiv (Fin 3 → ZMod 2))).symm⟩

end

end Work.Hering.HardCore
