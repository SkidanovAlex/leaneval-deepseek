import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.centralizer_irreducible_isCyclic
import Submission.Work.ThmF.ChV12.zpowers_eq_of_commute_of_orderOf_prime
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.ChV12.transitive_orbit_basics
import Submission.Work.ThmF.ChV12.solvable_of_cyclic_normal_irreducible
import Submission.Work.ThmF.ChV12.even_card_closure_of_two_ppd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12
-- **(2026-10-07, area owner).**  Per the lead's ruling the odd-order theorem may be assumed,
-- so this node carries `(hFT : FeitThompsonProp)`; the FT-free route survives as the
-- `PpdClosureProp`/`TransitiveLinearSolvable` definitions (`ChV12/ppdClosureProp_holds.lean`).


/-- **(2026-10-07, area owner, second pass.)**  The *statement* is

> an odd-order group `D` acting faithfully and transitively on the non-identity elements of an
> elementary abelian `2`-group `A` of order `2 ^ k`, with `p` a primitive prime divisor of
> `2 ^ k - 1`, is solvable,

which is exactly `FeitThompsonProp` at `↥D` (`hodd` plus `Nat.card ↥D = Nat.card D`); the `ppd`
argument it used to carry (through `even_card_closure_of_two_ppd`) belongs to the
**Feit–Thompson-free** route, which is out of scope (see `ChV12/ppdClosureProp_holds.lean`).  The
former body is recorded in `NOTES.md` §12. -/
theorem isSolvable_of_transitive_of_primitive_ppd (hFT : Submission.Blueprint.FeitThompsonProp) {A D : Type} [Group A] [Finite A] [Group D] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k p : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hp : Nat.Prime p)
    (hord : orderOf (2 : ZMod p) = k) (hodd : Odd (Nat.card D))
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    Group.IsSolvable D :=
  hFT D hodd

end Work.ThmF.ChV12
