import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Core

set_option linter.style.haveILetI false in
/-- **Freeness of the relative chart over the base ring.**  For a `K`-algebra `A` and a
`K`-algebra `R`, the tensor product `A ⊗[K] R` is a free `R`-module when the `R`-module
structure is the canonical one on the right factor (`Algebra.TensorProduct.rightAlgebra`, which
is *not* a global instance in Mathlib, hence pinned here by `letI`).  A `K`-basis `b` of `A`
gives the `R`-basis `b i ↦ b i ⊗ₜ 1`; equivalently `A ⊗[K] R ≅ (ι →₀ R)`.

This is what makes the content normalisation
`Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map` applicable to the coordinate ring
`A ⊗_K R` of the relative chart of a curve.

Suggested proof: `Module.Free.of_divisionRing K A` gives `Module.Free K A`; use
`Module.Basis.baseChange` (or `Module.Free.tensor`) on `Module.Free.chooseBasis K A` and
transport the basis across `TensorProduct.comm` (or use the `letI`-pinned instances). -/
theorem module_free_chartTensor {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {R : Type*} [CommRing R] [Algebra K R] :
    letI : Algebra R (TensorProduct K A R) :=
      Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
    Module.Free R (TensorProduct K A R) := by
  -- Put the canonical `R`-algebra structure on the right factor into scope, so that the
  -- `R`-module structure on `A ⊗[K] R` is the intended one.
  letI : Algebra R (TensorProduct K A R) :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
  -- The `R`-algebra isomorphism `R ⊗[K] A ≃ₐ[R] A ⊗[K] R` (right factor on the right).
  refine Module.Free.of_equiv (Algebra.TensorProduct.commRight K R A).toLinearEquiv

end Work.SpecLin.Core
