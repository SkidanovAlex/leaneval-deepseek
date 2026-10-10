import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.MotAS.ASRulV3.rangeClosureAS

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASrulTheta_rangeClosure` — the range closure of the AS ruling presentation

`A := ASrulA a b g = K[X₀,X₁,X₂] ⧸ √(ZIAS a b g)` (a domain under `hDZ`),
`ε := ASrulEpsA a b g = mk (kbRw a b g 4) : A`, `S := Localization.Away (Polynomial.C ε)` and
`θ := ASrulTheta a b g hDZ : K[X₀,X₁,X₂] →ₐ[K] S`,
`X_j ↦ (C (mk (kbRv (j+1)))·T + C (mk (kbRw (j+1))))·(C ε)⁻¹`.

The statement: under `a b ≠ 0`, `b ≠ 2a`, `g ≠ 0`, `ε ≠ 0` and `θ (fwVecAS2 a b g 0) ≠ 0`, the
fraction field of `θ.range` is the fraction field of `A[T]`:
`Nonempty (FractionRing θ.range ≃ₐ[K] FractionRing (Polynomial A))`.

## Route (the AS analogue of `Work.MotK.TGen.ThetaRangeClosure`)

Two ingredients suffice.

**(1) `θ (fwVecAS2 a b g 0) * C (mk (X i)) = θ (fwVecAS2 a b g (asCh3 i))`** for `i : Fin 3` — the
"chart identity", the single missing input, isolated in `Work.MotC5N3.ASrulTheta_fwVec` (see its
module docstring and `Submission/Work/MotC5N3/_notes/ASrulTheta_fwVec_ROUTE.md`).  With `h0` it
gives `C (mk (X i)) = θ (fwVecAS2 (i+1)) / θ (fwVecAS2 0) ∈ Frac (θ.range)` for `i = 0,1,2`.

**(2) `(a + 2b) * θ (X 2) = algebraMap R S Polynomial.X`** (`R := Polynomial A`): indeed
`kbRw a b g 3 = 0` and `kbRw a b g 4 = C (a + 2b) * kbRv a b g 3` in `K[X₀,X₁,X₂]`
(`Work.MotAS.Nodes.Shim.kbRw_four_eq`), so `(a+2b) · θ (X 2)` is the class of `ε · X`; as `C ε` is a
unit of `S` this is `algebraMap R S X`.  (`a + 2b ≠ 0` follows from `b ≠ 2a` in characteristic `5`;
it is not needed for the identity.)

Then `Subfield.closure (Set.range (algebraMap θ.range L)) = ⊤` with `L := FractionRing S` (the
constants, `Polynomial.X` from (2) and the three `C (mk (X i))` from (1) generate `A` and `T`), so
`IsFractionRing θ.range L` by the standard `Subfield.mem_closure_iff` argument — verbatim the proof
of `Work.MotK.TGen.ThetaRangeClosure` (its `hTheta`, `hX`, `hCi`, `hmemA`, `hmemR` steps).
Finally `L = FractionRing S ≅ₐ[K] FractionRing (Polynomial A)`: `C ε` is a non-zero-divisor of the
domain `A[T]` (`ε ≠ 0` and `A` a domain), so `FractionRing S` is a localization of `Polynomial A` at
the non-zero-divisors; `IsLocalization.localizationAlgebraOfSubmonoidLe` +
`IsFractionRing.isFractionRing_of_isLocalization` + `IsLocalization.algEquiv`
(cf. `Work.MotK.TGen.FractionRingAwayEquiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

theorem ASrulTheta_rangeClosure (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (Work.MotC5N3.ASrulA a b g)) (hε : Work.MotC5N3.ASrulEpsA a b g ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (h2ab : b ≠ 2 * a) (hg : g ≠ 0)
    (h0 : Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g 0) ≠ 0) :
    Nonempty (FractionRing (Work.MotC5N3.ASrulTheta a b g hDZ).range ≃ₐ[K]
      FractionRing (Polynomial (Work.MotC5N3.ASrulA a b g))) :=
  Work.MotAS.ASRulV3.rangeClosureAS K a b g hDZ hε ha hb h2ab hg h0

end Work.MotC5N3
