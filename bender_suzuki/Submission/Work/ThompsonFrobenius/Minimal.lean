import Mathlib
import Submission.Work.ThompsonFrobenius.Defs
import Submission.Work.ThompsonFrobenius.Structure
import Submission.Work.Frobenius.Fpf.exists_invariant_sylow
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: the minimal-counterexample framework

Route-independent backbone of Thompson's theorem (Thompson 1959): the strong induction on
`|Q|` and the structure of a minimal counterexample.

* `ThmBelow n` is the induction hypothesis "every group of cardinal `< n` carrying a
  fixed-point-free automorphism of prime order is nilpotent";
* `IsMinimalCounterexample Q α` bundles: the induction hypothesis below `|Q|`, `α` fpf of prime
  order, `Q` not nilpotent, and every proper `α`-invariant subgroup of `Q` nilpotent;
* `IsMinimalCounterexample.not_solvable`: a minimal counterexample is not solvable (the delivered
  solvable case `Work.Frobenius.Fpf.isNilpotent_of_fpf_prime` would otherwise give nilpotency);
* `IsMinimalCounterexample.not_odd_card`: `|Q|` is even (`FeitThompsonProp` + the solvable case);
* `IsMinimalCounterexample.exists_invariant_sylow`: an `α`-invariant Sylow subgroup exists for
  every prime (`Work.Frobenius.Fpf.exists_invariant_sylow`).

The main theorem of the area is assembled in `Submission.Work.ThompsonFrobenius.Main` from the
solvability step (`SolvabilityStep` in `Submission.Work.ThompsonFrobenius.Defs`) and the delivered
solvable case.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

/-- **The induction hypothesis of Thompson's theorem below `n`**: every finite group of cardinal
`< n` admitting a fixed-point-free automorphism of prime order is nilpotent. -/
def ThmBelow (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (β : MulAut K), Nat.card K < n →
    (orderOf β).Prime → IsFpf β → Group.IsNilpotent K

theorem ThmBelow.mono {m n : ℕ} (h : ThmBelow n) (hmn : m ≤ n) : ThmBelow m :=
  fun K _ _ β hlt => h K β (lt_of_lt_of_le hlt hmn)

/-- **A minimal counterexample to Thompson's theorem**: `Q` is not nilpotent, `α` is a
fixed-point-free automorphism of prime order, the theorem holds below `|Q|`, and every proper
`α`-invariant subgroup of `Q` is nilpotent. -/
structure IsMinimalCounterexample (Q : Type) [Group Q] [Finite Q] (α : MulAut Q) : Prop where
  /-- the induction hypothesis below `|Q|` -/
  below : ThmBelow (Nat.card Q)
  /-- `α` has prime order -/
  orderOf_prime : (orderOf α).Prime
  /-- `α` is fixed-point-free -/
  fpf : IsFpf α
  /-- `Q` is not nilpotent -/
  not_nilpotent : ¬ Group.IsNilpotent Q
  /-- every proper `α`-invariant subgroup is nilpotent -/
  invariant_nilpotent : ∀ H : Subgroup Q, IsInv α H → H ≠ ⊤ → Group.IsNilpotent H

/-- A minimal counterexample is not solvable: the delivered solvable case of Thompson's theorem
(`Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`) would make it nilpotent. -/
theorem IsMinimalCounterexample.not_solvable {Q : Type} [Group Q] [Finite Q] {α : MulAut Q}
    (h : IsMinimalCounterexample Q α) : ¬ Group.IsSolvable Q := by
  obtain ⟨-, hprime, hfpf, hnot, -⟩ := h
  exact fun hsol => hnot (isNilpotent_of_fpf_of_solvable hprime hfpf)

/-- **`|Q|` is even** in a minimal counterexample: an odd-order group is solvable by
`FeitThompsonProp`, hence nilpotent by the delivered solvable case. -/
theorem IsMinimalCounterexample.not_odd_card {Q : Type} [Group Q] [Finite Q] {α : MulAut Q}
    (h : IsMinimalCounterexample Q α) (hFT : Submission.Blueprint.FeitThompsonProp) :
    ¬ Odd (Nat.card Q) := by
  obtain ⟨-, hprime, hfpf, hnot, -⟩ := h
  intro hodd
  exact hnot (isNilpotent_of_fpf_of_odd hFT hprime hfpf hodd)

/-- An `α`-invariant Sylow subgroup exists for every prime
(`Work.Frobenius.Fpf.exists_invariant_sylow`). -/
theorem IsMinimalCounterexample.exists_invariant_sylow {Q : Type} [Group Q] [Finite Q]
    {α : MulAut Q} (h : IsMinimalCounterexample Q α) (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p Q, IsInv α (P : Subgroup Q) := by
  obtain ⟨-, -, hfpf, -, -⟩ := h
  exact Work.Frobenius.Fpf.exists_invariant_sylow hfpf p

/-- **The final assembly step of the induction**: if there is no minimal counterexample then
Thompson's theorem holds.  Together with `SolvabilityStep` (see
`Submission.Work.ThompsonFrobenius.Defs`) this reduces the theorem to the solvability of a group
with a fixed-point-free automorphism of prime order. -/
theorem thompsonFrobenius_of_solvabilityStep (h : SolvabilityStep) :
    Submission.Blueprint.ThompsonFrobeniusProp :=
  thompsonFrobenius_of_solvability h

end Work.ThompsonFrobenius
