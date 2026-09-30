import Mathlib
import Submission.Work.CurveBasics.Order.reduce_to_pure_case
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_general_assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- **The integral closure of `k[x]` in a finite extension of `k(x)` is a finite `k[x]`-module.**

Equivalently: for a field `k` and `x` transcendental over `k`, the polynomial ring `k[x]`
(via `k[x] ≅ k[X]`, Mathlib's `Polynomial.algEquivOfTranscendental`) is a *Japanese* (N-2)
ring, i.e. its normalisation in every finite extension of its fraction field `k(x)` is finite.
This is the algebraic input ("the normalisation of the affine line in a finite extension of its
function field is finite") behind the finiteness of the morphism `C → ℙ¹` for a smooth proper
curve `C`.

The proof splits the finite extension `L/k(x)` along the separable/purely inseparable
decomposition.  The purely inseparable case is `kx_pure_insep` (the normalisation of `k[x]` in a
purely inseparable extension of `k(x)`); the passage from that case to the general one is
`normalClosure_reduction`, applied to `normal_case` (in `reduce_to_pure_case`): one passes to the
normal closure `M` of `L` over `k(x)`, where `L` sits inside an extension whose maximal purely
inseparable part `P` admits a separable quotient `M/P`; `P/k(x)` is purely inseparable so the
pure case bounds the integral closure there, and the separable step is Mathlib's
`IsIntegralClosure.finite` (with `perfectClosure_separable_of_normal`). -/
theorem integralClosure_adjoin_finite_of_transcendental {k L : Type*} [Field k] [Field L]
    [Algebra k L] (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) :=
  normalClosure_reduction (fun x _ _ hx => normal_case x hx) x hx

end Work.CurveBasics.Order
