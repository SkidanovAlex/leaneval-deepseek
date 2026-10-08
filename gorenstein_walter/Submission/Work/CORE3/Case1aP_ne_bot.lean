import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.pCoreIn_of_pow_eq_one_of_mem_fittingIn

/-!
# `O_p(U) ≠ 1` for the §3 prime `p ∈ π(F(U))`

The target of this file is

`Work.CORE3.Case1aP_ne_bot`:

in the subcase `Ĥ = H` of Bender 1981 §3 the prime `p` is chosen so that
`p ∈ π(F(U))`, where `U = O(H)`; the corresponding `p`-core of `U` is then nontrivial,
i.e. `P = O_p(U) ≠ 1`.

The mathematics is a two-line general fact, valid for *every* subgroup `K` of a finite group
`G`: `p ∈ π(F(K))` means that `p` divides `|F(K)|`; the Fitting subgroup `F(K)` is nontrivial
precisely then, and since `|F(K)|` is divisible by the prime `p` Cauchy's theorem produces an
element `x ∈ F(K)` of order `p`.  Such an `x` satisfies `x ^ p = 1`, so
`Work.CORE3.pCoreIn_of_pow_eq_one_of_mem_fittingIn` puts it in `O_p(K)`; as `x ≠ 1`, that
subgroup is nontrivial.

No hypothesis beyond `D.p_mem` is needed: the `Case1aData` fields `t1, t2, hp, cent, inv`
are used by the *other* leaves of CORE3, not here.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3

open Subgroup

/-- **`O_p(K) ≠ 1` when `p ∈ π(F(K))`.**  General form, for an arbitrary subgroup `K` of a
finite group; the statement of the leaf is the special case `K = B.U`. -/
theorem pCoreIn_ne_bot_of_mem_primesOf_fittingIn (G : Type) [Group G] [Finite G]
    (K : Subgroup G) (p : ℕ)
    (hp : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn K)) : Work.GW2.pCoreIn p K ≠ ⊥ := by
  -- `p` is a prime dividing `|F(K)|`
  have hmem : p ∈ (Nat.card (Work.GW2.fittingIn K)).primeFactors := hp
  obtain ⟨hpprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hmem
  haveI : Fact p.Prime := ⟨hpprime⟩
  -- Cauchy: an element of `F(K)` of order `p`
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.fittingIn K)) p hdvd
  -- it lies in `O_p(K)`
  have hmem_pcore : (y : G) ∈ Work.GW2.pCoreIn p K :=
    pCoreIn_of_pow_eq_one_of_mem_fittingIn K p y.2 (by
      have h1 : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      simpa using congrArg (fun z : ↥(Work.GW2.fittingIn K) => (z : G)) h1)
  -- and it is not the identity, because its order is the prime `p`
  have hyne : (y : G) ≠ 1 := fun h =>
    hpprime.ne_one (by
      have h1 : (1 : ↥(Work.GW2.fittingIn K)) = y := Subtype.ext (by simpa using h.symm)
      rw [← hy, ← h1, orderOf_one])
  intro hbot
  exact hyne (by have := hbot ▸ hmem_pcore; simpa using this)

theorem Case1aP_ne_bot (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) : Work.GW2.pCoreIn D.p B.U ≠ ⊥ :=
  pCoreIn_ne_bot_of_mem_primesOf_fittingIn G B.U D.p D.p_mem

end Work.CORE3
