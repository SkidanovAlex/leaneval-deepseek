import Mathlib
import Submission.Work.WingbergRoute.Verification
import Submission.Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot

/-!
# `Work.WingbergRoute.Traps` -- machine-checked traps of the unramified route

Two traps that this area's construction ran into, recorded so that they are not rediscovered.

## 1. The finiteness hypotheses of `KcH3Wall` cannot be dropped

The chapter consumes the relation count through

```
#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2]
```

(`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`, unconditional) together with
`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) = 2^5`.  The workspace proves the *inequality* `≤ 2^5`
unconditionally (`Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`), and the
tempting route to the equality is the general implication

```
#A[2] ≤ #(A/2A)          (A abelian)
```

which would combine with the unconditional lower bound `2^5 ≤ #H²(G_∅,ℤ)[2]` (the connecting map
`δ¹ : H¹(G_∅,𝔽₂) ↪ H²(G_∅,ℤ)[2]`).  **That general implication is FALSE**, as
`Work.WingbergRoute.not_twoTorsion_card_le_quot_twoMul` below shows: for the Prüfer group
`ℚ/ℤ` the `2`-torsion has `2` elements while `(ℚ/ℤ)/2(ℚ/ℤ)` is trivial (`ℚ/ℤ` is divisible).
Consequently the finiteness of `H²(G_∅,ℤ)` is a genuine part of the classical input, and
`Work.WingbergRoute.KcH3Wall` carries it.  With the quotient infinite, the unconditional bound
`≤ 2^5` is *vacuous* (`Nat.card` of an infinite type is `0`).

## 2. The `Kc` instance of the wall cannot produce the benchmark

`InfiniteProTwoExtension Kc` gives the levels of the unramified tower over the *imaginary*
quadratic `Kc`; these are totally complex, and `Submission/Work/HilbertTowerCM/` proves that their
maximal real subfields have *bounded* degree (`Work.HilbertTowerCM.not_isCMField_of_inverting_involution`
with the numerical certificate `Work.HilbertTowerCM/certificate.gp`).  So the `Kc` instance yields
only `Submission.NumberField.BoundedRdTowerWall`
(`Work.WingbergRoute.boundedRdTowerWall_of_kcWingbergWall`), and the benchmark needs the extra
level clause of `Work.WingbergRoute.benchmark_of_kcWingbergWall_of_realPart`.  The instance that
reaches the benchmark is the **totally real** one, `Work.WingbergRoute.gsFArithmeticInput`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergRoute

/-- **The general implication `#A[2] ≤ #(A/2A)` is false.**  A counterexample is the Prüfer
`2`-group `ℚ/ℤ`, whose `2`-torsion has two elements while `(ℚ/ℤ)/2(ℚ/ℤ)` is trivial. -/
theorem not_twoTorsion_card_le_quot_twoMul :
    ¬ (∀ (A : Type) [AddCommGroup A],
        Nat.card {x : A // (2 : ℕ) • x = 0} ≤
          Nat.card (A ⧸ AddSubgroup.closure (Set.range (fun x : A => (2 : ℕ) • x)))) :=
  fun h => not_le_of_gt pruefer_twoTorsion_card_gt_quot (h QZ)

end Work.WingbergRoute
