import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic base case for a cycle: the saturated case

The cyclotomic input of Lang's Theorem 2 (`NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe`) is
stated for a natural-number modulus `m` with `n ∣ m` for an extension `M ⊆ k'(ζ_n)`: it says
`P(m) ≤ ker ψ`, i.e. the Artin symbol kills the principal ideals `(b)` with `b ≡ 1 mod m`.

This module records the transfer of that statement to a **cycle** `c`, in the case where the cycle
is *finer* than `m` on the primes dividing `(m)` — precisely:

* `c.supp` contains every prime `𝔭` with `(m : 𝓞 k') ∈ 𝔭.asIdeal` (`hsupp`), and
* `cycleLevel m 𝔭 ≤ c.lev 𝔭` on `c.supp` (`hcmp`).

Then `c.CongrOne b` implies `CongrOne m b`, so `P(c) ≤ P(m) ≤ ker ψ`
(`cyclotomicKernelLe_cycle_of_saturated`).

**What is *not* covered, and is the genuinely new ingredient of the cycle form** of Lang's
Theorem 2: a cycle `c` which is supported on the *ramified* primes only, while `(m)` also contains
unramified primes (`hsupp` then fails).  For such a prime `𝔭 ∤ c.supp` (a "gap" prime) the element
`b ≡ 1 mod c` may have `v_𝔭(b) ≠ 0`, and the local norm condition at `𝔭` (`f_𝔭 ∣ v_𝔭(b)`) may fail;
the ℕ-modulus statement `P(m) ≤ ker` says nothing about it.  Concretely, for
`k' = ℚ(∛2)`, `n = 15`, the rational prime `3` has a ramified prime `𝔭₁` and an unramified prime
`𝔭₂` with residue degree `2` in `k'(ζ_15)/k'`, so no ℕ-modulus supported on the ramified primes
exists and the gap is real.  Classically the gap is closed by the *local* computation of the
Frobenius action on `ζ_n` (Milne, *CFT*, Example 8.2), which is the missing ingredient here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative

noncomputable section

namespace Work.SSGRoute.ZDataMup

namespace Cycle

/-- **The cyclotomic base case for a cycle, in the saturated case**: if `M ⊆ k'(ζ_n)`, `n ∣ m`,
every prime ramified in `M/k'` divides `(m)`, and the cycle `c` refines `m` on the primes dividing
`(m)` (`hsupp`, `hcmp`), then the Artin symbol of `M/k'` kills the principal ray `P(c)`. -/
theorem cyclotomicKernelLe_cycle_of_saturated
    {k' E' : Type} [Field k'] [NumberField k'] [Field E'] [NumberField E'] [Algebra k' E']
    [FiniteDimensional k' E'] [IsGalois k' E']
    (M : IntermediateField k' E') [FiniteDimensional k' M] [NumberField ↥M] [IsGalois k' ↥M]
    [IsMulCommutative (Gal(↥M/k'))]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} k' E']
    (m : ℕ) (hm : 0 < m) (hn : n ∣ m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal k',
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := k') (L := ↥M) p →
      (m : 𝓞 k') ∈ p.asIdeal)
    (c : Cycle k') (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hsupp : ∀ 𝔭 : HeightOneSpectrum (𝓞 k'), (m : 𝓞 k') ∈ 𝔭.asIdeal → 𝔭 ∈ c.supp)
    (hcmp : ∀ 𝔭 ∈ c.supp, cycleLevel (K := k') m 𝔭 ≤ c.lev 𝔭) :
    c.principalRay ≤ (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := k') (L := ↥M)
      (fun a b : Gal(↥M/k') => IsMulCommutative.is_comm.comm a b)).ker := by
  have hbase := NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe_principalRay_le_ker
    (k' := k') (E' := E') M n m hm hn hram
  rw [Cycle.principalRay, Subgroup.closure_le]
  rintro A ⟨b, hb, rfl⟩
  have hcongm : NK.CFTLib.ArtinReciprocityIdeal.CongrOne m b := by
    refine ⟨fun 𝔭 h𝔭 => ?_, hb.2⟩
    refine le_trans (hb.1 𝔭 (hsupp 𝔭 h𝔭)) ?_
    rw [valued_natCast_eq_exp_cycleLevel (K := k') m hm 𝔭, WithZero.exp_le_exp]
    have h := hcmp 𝔭 (hsupp 𝔭 h𝔭)
    have h' : -(((c.lev 𝔭 : ℕ) : ℤ)) ≤ -(((cycleLevel (K := k') m 𝔭 : ℕ) : ℤ)) := by
      exact neg_le_neg (by exact_mod_cast h)
    exact h'
  exact hbase (Subgroup.subset_closure ⟨b, hcongm, rfl⟩)

end Cycle

end Work.SSGRoute.ZDataMup
