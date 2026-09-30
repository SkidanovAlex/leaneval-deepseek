import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-!
An integer is coprime to a product of primes iff none of them divides it.

This is the (only) place where the coprime condition in `mr_core.coprime_density_tk` is converted
into `ω_{[P,Q]}(n) = 0` with `ω(n) = #{p ∈ s : p ∣ n}`.

Easiest route: `Nat.coprime_prod_right_iff` reduces to `∀ p ∈ s, n.Coprime p`, and
`Nat.Prime.coprime_iff_not_dvd` finishes each.  (A related specialised lemma
`Work.BMF.mr_direct.coprime_primesIn_iff` already exists in this workspace.)
-/
theorem coprime_prod_iff (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    n.Coprime (∏ p ∈ s, p) ↔ ∀ p ∈ s, ¬ p ∣ n := by
  rw [Nat.coprime_prod_right_iff]
  exact ⟨fun h p hp => (Nat.Prime.coprime_iff_not_dvd (hs p hp)).mp (Nat.coprime_comm.mpr (h p hp)),
    fun h p hp => Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hs p hp)).mpr (h p hp))⟩

end Work.BMF.mr_core
