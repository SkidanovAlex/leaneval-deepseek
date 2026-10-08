import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.IterComm` — iterated commutators `e_n(u,z)`

`Work.Grun.iterComm n u z = ⁅u, z, …, z⁆` (`n` copies of `z`) is M. Hall's `e_{n+1}(u,z)`
(`u₁ = u`, `u_{k+1} = ⁅u_k, z⁆`), so `Work.Grun.iterComm (p - 1) u z` is Hall's `e_p(u,z)`.

The two facts used by the Hall–Wielandt argument:

* `iterComm_succ_eq_iterComm_commutator` — the shift `e_{n+1}(u,z) = e_n(⁅u,z⁆, z)`, which is how
  Hall's condition 1) (`e_p(u,z) = 1` for `u ∈ S`, `z ∈ A`) is deduced from condition 2)
  (`e_{p-1}(u,z) = 1` for `u, z ∈ A`) together with `⁅S, A⁆ ≤ A`;
* `iterComm_eq_one_of_abelian` — for commuting `u, z` all the higher iterated commutators of length
  `≥ 1` vanish.  Applied with `u := ⁅u₀,z⁆` for `u₀ ∈ S`, `z ∈ A` (both in the abelian group `A`)
  this gives `iterComm (p - 1) u₀ z = 1` for odd `p`: the point where `p ≠ 2` is used.
-/

set_option autoImplicit false

open scoped commutatorElement

namespace Work.BSHallW

/-- **The shift identity for iterated commutators**: `e_{n+1}(u,z) = e_n(⁅u,z⁆, z)`. -/
theorem iterComm_succ_eq_iterComm_commutator {G : Type*} [Group G] (n : ℕ) (u z : G) :
    Work.Grun.iterComm (n + 1) u z = Work.Grun.iterComm n ⁅u, z⁆ z := by
  induction n with
  | zero => rw [Work.Grun.iterComm_one, Work.Grun.iterComm_zero]
  | succ k ih =>
    rw [Work.Grun.iterComm_succ, ih]
    rfl

/-- **Commuting elements have vanishing iterated commutators.**  If `u, z` lie in a subgroup `A` in
which multiplication is commutative, then `e_n(u,z) = 1` for every `n ≥ 1`. -/
theorem iterComm_eq_one_of_abelian {G : Type*} [Group G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u z : G} (hu : u ∈ A) (hz : z ∈ A) {n : ℕ}
    (hn : 1 ≤ n) : Work.Grun.iterComm n u z = 1 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Work.Grun.iterComm_one]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hAab u hu z hz)
    · rw [Work.Grun.iterComm_succ, ih hk]
      simp

end Work.BSHallW
