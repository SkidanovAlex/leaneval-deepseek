import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.NPC.All
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: Thompson's theorem on fixed-point-free automorphisms

Thompson (1959): a finite group admitting a fixed-point-free automorphism of prime order is
nilpotent.  The blueprint's `Prop` for this area is
`Submission.Blueprint.ThompsonFrobeniusProp`:

```
∀ (Q : Type) [Group Q] [Finite Q] (α : MulAut Q), (orderOf α).Prime →
  (∀ x : Q, α x = x → x = 1) → Group.IsNilpotent Q
```

This module fixes the vocabulary of the area; the proof is assembled in
`Submission.Work.ThompsonFrobenius.Main` on top of the delivered Feit--Thompson libraries
(`Work.NPC`, `Work.Frobenius.Fpf`) and the black-box `Prop`s of the blueprint
(`BrauerSuzukiProp`, `FeitThompsonProp`, ...).

## Conventions

* `Work.NPC.Fpf.IsFpf α` (`∀ x, α x = x → x = 1`) is the delivered fixed-point-free-ness
  predicate; we reuse it rather than duplicating it.
* `Work.NPC.Fpf.IsInv α H` is `α`-invariance of a subgroup `H`.
* Conjugation is `MulAut.conj`, so `MulAut.conj g • H = g H g⁻¹`.

## Main definitions

* `IsFpfPrimeAuto`: a bundled fixed-point-free automorphism of prime order;
* `SolvabilityStep`: the (only remaining) input of the proof of the main theorem,
  "a finite group with a fixed-point-free automorphism of prime order is solvable";
* `IsMinimalFpfCounterexample`: the minimal counterexample predicate used in the structure
  theorems of `Submission.Work.ThompsonFrobenius.Minimal`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

variable {Q : Type*}

/-- A **fixed-point-free automorphism of prime order** of a group, bundled. -/
structure IsFpfPrimeAuto (Q : Type*) [Group Q] where
  /-- the underlying automorphism -/
  toMulAut : MulAut Q
  /-- its order is prime -/
  orderOf_prime : (orderOf toMulAut).Prime
  /-- it is fixed-point-free -/
  fpf : ∀ x : Q, toMulAut x = x → x = 1

namespace IsFpfPrimeAuto

variable [Group Q] (α : IsFpfPrimeAuto Q)

instance : CoeFun (IsFpfPrimeAuto Q) (fun _ => Q → Q) := ⟨fun α => α.toMulAut⟩

theorem isFpf : IsFpf (α.toMulAut) := α.fpf

theorem aut_pow_eq_one : α.toMulAut ^ orderOf α.toMulAut = 1 := pow_orderOf_eq_one _

end IsFpfPrimeAuto

/-- **The remaining input of Thompson's theorem.**  Every finite group with a fixed-point-free
automorphism of prime order is solvable.  (This is the "Hughes--Thompson" step; historically it
is proved from the same normal `p`-complement machinery as Theorem A of Thompson's 1960 paper.
The main theorem of this file is proved from this statement and the *delivered* theorem
`Work.Frobenius.Fpf.isNilpotent_of_fpf_prime` "solvable + fpf of prime order ⇒ nilpotent".) -/
def SolvabilityStep : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (α : MulAut Q), (orderOf α).Prime →
    (∀ x : Q, α x = x → x = 1) → Group.IsSolvable Q

/-- The main theorem of the area is obtained from the solvability input by the delivered
solvable-case theorem. -/
theorem thompsonFrobenius_of_solvability (h : SolvabilityStep) :
    Submission.Blueprint.ThompsonFrobeniusProp := by
  intro Q _ _ α hprime hfpf
  haveI : Group.IsSolvable Q := h Q α hprime hfpf
  exact Work.Frobenius.Fpf.isNilpotent_of_fpf_prime hprime (pow_orderOf_eq_one α) hfpf

end Work.ThompsonFrobenius
