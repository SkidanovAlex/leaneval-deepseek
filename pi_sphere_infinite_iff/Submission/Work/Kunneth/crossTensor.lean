import Mathlib
import Submission.Work.Kunneth.CrossHBilin

/-!
# The cross product as a map on the tensor product

`Work.Kunneth.crossHLin X Y p q` is the cross product as a *bilinear* map
`Hᵖ(X) →ₗ H^q(Y) →ₗ H^{p+q}(X × Y)`; its transpose
`Hᵖ(X) ⊗ H^q(Y) → H^{p+q}(X × Y)` is `Work.Kunneth.crossTensor` below.

This file is in the "re-registered" convention (§6 of `README.md`), so that the `ℤ`-module
structure on the linear maps synthesises and `TensorProduct.lift` applies.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [local instance 5000] AddCommGroup.toIntModule

/-- **The cross product on the tensor product**: `a ⊗ b ↦ a × b = π₁^*a ⌣ π₂^*b`. -/
noncomputable def crossTensor (X Y : SSet) (p q : ℕ) :
    (↥((cochainC ℤ X).homology p) ⊗[ℤ] ↥((cochainC ℤ Y).homology q)) →ₗ[ℤ]
      ↥((cochainC ℤ (sProd X Y)).homology (p + q)) :=
  TensorProduct.lift (crossHLin X Y p q)

/-- The computation rule for the cross product on the tensor product. -/
theorem crossTensor_tmul (X Y : SSet) (p q : ℕ)
    (a : ↥((cochainC ℤ X).homology p)) (b : ↥((cochainC ℤ Y).homology q)) :
    crossTensor X Y p q (a ⊗ₜ[ℤ] b) = crossH X Y p q a b :=
  (TensorProduct.lift.tmul (f' := crossHLin X Y p q) a b).trans
    (crossHLin_apply_eq_cup X Y p q a b)

end

end Work.Kunneth
