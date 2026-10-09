import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `F`-algebra automorphisms of a Lubin–Tate level preserve the division points

The Lubin–Tate level `K_n = LTLevel F π q n` is generated over `F` by the set `Λ_n` of
`π^n`-division points (the roots of the iterate `f^{(n)}` of the standard Lubin–Tate polynomial
`f(T) = πT + T^q`).  Since `Λ_n` is the root set of a polynomial with coefficients in `F`, every
`F`-algebra automorphism `σ` of `K_n` permutes `Λ_n`: it maps a root of `f^{(n)}` to a root of
`f^{(n)}` because it is `F`-linear.

This is the elementary step underlying `ext_of_eqOn_LTdivisionSet` — an `F`-automorphism of `K_n` is
determined by its action on the division points.
-/

open Polynomial

universe u

namespace NK.LocalReciprocityLubinTate.LubinTate

theorem map_mem_LTdivisionSet_of_algEquiv (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : F) (q n : ℕ) (hq : 2 ≤ q)
    (σ : ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n) ≃ₐ[F]
      ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)) {x : AlgebraicClosure F}
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q n) :
    ((σ ⟨x, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F π q n hx⟩ :
        ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)) : AlgebraicClosure F)
      ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q n := by
  -- `x` is a root of the iterate `f^{(n)}`, hence so is its image under `σ`.
  have hxroot : (aeval x) (NK.LocalReciprocityLubinTate.LTpolyIter π q n) = 0 :=
    (NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (F := F) π q n hq).mp hx
  -- the same is true inside the level `K_n` (the coefficient field is `F`, and the coercion
  -- `K_n → F̄` is an `F`-algebra map, so `aeval` commutes with it)
  have hP : (aeval (⟨x, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F π q n hx⟩ :
      ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)))
      (NK.LocalReciprocityLubinTate.LTpolyIter π q n) = 0 := by
    have h1 : (((aeval (⟨x, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F π q n hx⟩ :
        ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)))
        (NK.LocalReciprocityLubinTate.LTpolyIter π q n)
        : ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)) : AlgebraicClosure F) = 0 := by
      rw [← IntermediateField.aeval_coe]
      exact hxroot
    exact Subtype.coe_injective h1
  -- `σ` fixes the coefficients (which lie in `F`), so `aeval (σ x) f^{(n)} = σ (aeval x f^{(n)}) = 0`
  rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (F := F) π q n hq]
  rw [IntermediateField.aeval_coe, Polynomial.aeval_algHom_apply, hP, map_zero]
  exact ZeroMemClass.coe_zero _

end NK.LocalReciprocityLubinTate.LubinTate
