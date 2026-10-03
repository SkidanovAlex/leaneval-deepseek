import Submission.Work.ORFlatness.FlatCrit
import Submission.Work.ORFlatness.leftFlat_of_projective

/-!
# `Tor₁^{R}(X, N) = 0` for `N` projective

`Work.ORFlatness.Tor1Vanishes R X N` (`Submission/Work/ORFlatness/Flat.lean`) is the dimension
criterion for `Tor₁^{R}(X, N) = 0`: some projective presentation `0 → K → P → X → 0` of the right
`R`-module `X` has `K ⊗[R] N → P ⊗[R] N` injective.  It holds *for every* `X` as soon as the left
`R`-module `N` is flat; in particular as soon as `N` is projective (in particular: free).

This is the criterion used in node N3 to dispose of JL Claim 5.8: in the single two-cell case the
middle term `I^G_{K[A]} ⊕ K[G]` of the transposed Claim 5.10 is in fact *free* over `K[G]` (it is
isomorphic to `K[G]^X`, see `Submission/Work/ORLyndon/MagnusMiddle.lean`), so `Tor₁` vanishes
against it for trivial reasons.
-/

set_option autoImplicit false

open TensorProduct MulOpposite

universe u

namespace Work.ORLyndon

/-- **`Tor₁^{R}(X, N) = 0` for `N` projective.**  For every right `R`-module `X` and every
projective left `R`-module `N`, `Work.ORFlatness.Tor1Vanishes R X N` holds. -/
theorem tor1Vanishes_of_projective (R : Type u) [Ring R] {N : Type u} [AddCommGroup N]
    [Module R N] [Module.Projective R N] (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] :
    Work.ORFlatness.Tor1Vanishes R X N :=
  Work.ORFlatness.Tor1Vanishes.of_leftFlat R
    (Work.ORFlatness.leftFlat_of_projective R) X

/-- `Tor₁^{R}(X, N) = 0` for `N` free: the special case of
`Work.ORLyndon.tor1Vanishes_of_projective` for free modules. -/
theorem tor1Vanishes_of_free (R : Type u) [Ring R] {N : Type u} [AddCommGroup N]
    [Module R N] [Module.Free R N] (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] :
    Work.ORFlatness.Tor1Vanishes R X N :=
  Work.ORFlatness.Tor1Vanishes.of_leftFlat R
    (Work.ORFlatness.leftFlat_of_projective R) X

end Work.ORLyndon
