import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_p(G) ≤ F(G)`

Every `p`-core is contained in the Fitting subgroup:

  `O_p(G) ≤ F(G)`  for every natural number `p` and every finite group `G`.

Here `O_p(G) = Work.Fitting.pCore p G` is the supremum of the normal subgroups `N ≤ G` whose
order has no prime divisor other than `p`, and `F(G) = Work.Fitting.fitting G` is the supremum
of the normal nilpotent subgroups of `G`.  So it suffices to see that each such `N` is
nilpotent, and since `N` is normal the conclusion `N ≤ F(G)` is exactly `le_fitting`.

The nilpotency of `N` is immediate when `p` is prime: then `|N|` is a power of `p`, i.e. `N` is
a `p`-group (`isPiNat_prime_iff_isPGroup`), and a finite `p`-group is nilpotent
(`IsPGroup.isNilpotent`).  When `p` is not prime the hypothesis `IsPiNat (· = p) |N|` forces
`|N| = 1`: a non-trivial finite group has a prime divisor `q`, and `q = p` would make `p`
prime.  Hence `N = ⊥` is trivial, and a trivial group is nilpotent
(`Group.isNilpotent_of_subsingleton`).

Note that no primality hypothesis on `p` is needed, because for non-prime `p` (and also for
`p = 0`) the `p`-core is trivial.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G]

/-- A subgroup `N` of a finite group whose order has no prime divisor other than `p` is
nilpotent.  For `p` prime this is the statement that a finite `p`-group is nilpotent; for `p`
not prime the hypothesis forces `N = ⊥`, which is trivially nilpotent. -/
theorem isNilpotent_of_isPiNat_eq [Finite G] {p : ℕ} {N : Subgroup G}
    (h : IsPiNat (fun q => q = p) (Nat.card ↥N)) : Group.IsNilpotent ↥N := by
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    exact ((isPiNat_prime_iff_isPGroup hp N).mp h).isNilpotent
  · -- `p` is not prime, so `|N|` has no prime divisor, i.e. `|N| = 1` and `N = ⊥`.
    have hcard : Nat.card ↥N = 1 := by
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      exact hp (h q hq hqdvd ▸ hq)
    rw [Subgroup.eq_bot_of_card_eq (H := N) hcard]
    infer_instance

/-- `O_p(G) ≤ F(G)`: the `p`-core is a normal nilpotent subgroup, hence lies in the Fitting
subgroup. -/
theorem pCore_le_fitting (G : Type*) [Group G] [Finite G] (p : ℕ) :
    Work.Fitting.pCore p G ≤ Work.Fitting.fitting G := by
  rw [pCore, piCore]
  refine sSup_le fun N hN => ?_
  exact le_fitting hN.1 (isNilpotent_of_isPiNat_eq hN.2)

end Work.Fitting
