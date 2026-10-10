import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- **Descent of an arithmetic Frobenius along a commuting subfield inclusion.**  Let
`K ⊆ L ⊆ N ⊆ M` be a tower of number fields, `P` a prime of `𝓞 M` whose contraction `Pn = P ∩ 𝓞 N`
is a prime of `𝓞 N`, `ρ ∈ Gal(M/K)` a Frobenius element at `P` over `K`, and `τ ∈ Gal(N/L)` an
element which commutes with `ρ` on `N` at the level of the rings of integers:
`galRestrict ρ (i y) = i (galRestrict τ y)` for all `y ∈ 𝓞 N`, where `i : 𝓞 N → 𝓞 M` is induced by
the inclusion.  If moreover the residue cardinalities of the two base primes agree
(`Nat.card (𝓞 L ⧸ Pn ∩ 𝓞 L) = Nat.card (𝓞 K ⧸ P ∩ 𝓞 K)`, the hypothesis `hf`; it holds for instance
when `Pn ∩ 𝓞 L` has inertia degree one over `K`), then `τ` is a Frobenius element at `Pn` over
`L`. -/
theorem frobAt_descend_of_galRestrict_commutes
    {K L N M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K N] [Algebra L N] [IsScalarTower K L N]
    [Algebra K M] [Algebra N M] [Algebra L M]
    [IsScalarTower K N M] [IsScalarTower L N M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L N] [FiniteDimensional K M]
    {P : NK.Chebotarev.PrimeIdeal M} {Pn : NK.Chebotarev.PrimeIdeal N}
    (hP : P.asIdeal.LiesOver Pn.asIdeal)
    {ρ : Gal(M/K)} (hρ : NK.Chebotarev.IsFrobAt (K := K) (L := M) P ρ) {τ : Gal(N/L)}
    (hcomm : ∀ y : NumberField.RingOfIntegers N,
      galRestrict (NumberField.RingOfIntegers K) K M (NumberField.RingOfIntegers M) ρ
          (algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M) y)
        = algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M)
            (galRestrict (NumberField.RingOfIntegers L) L N (NumberField.RingOfIntegers N) τ y))
    (hf : Nat.card (NumberField.RingOfIntegers L ⧸
            Pn.asIdeal.under (NumberField.RingOfIntegers L))
          = Nat.card (NumberField.RingOfIntegers K ⧸
            P.asIdeal.under (NumberField.RingOfIntegers K))) :
    NK.Chebotarev.IsFrobAt (K := L) (L := N) Pn τ := by
  -- `IsFrobAt` unfolds to `∀ y, galRestrict ρ ↾ y - y ^ #(residue field) ∈ P`.
  intro y
  -- The Frobenius condition for `ρ` at the element `i y`, where `i : 𝓞 N → 𝓞 M`.
  have hρ' := hρ (algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M) y)
  -- Apply `i` to the witness `galRestrict τ y - y ^ #(𝓞K ⧸ P ∩ 𝓞K)` and rewrite using the
  -- commuting hypothesis, which identifies `ρ (i y)` with `i (τ y)`.
  have h2 : algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M)
      (galRestrict (NumberField.RingOfIntegers L) L N (NumberField.RingOfIntegers N) τ y
        - y ^ Nat.card (NumberField.RingOfIntegers K ⧸
            P.asIdeal.under (NumberField.RingOfIntegers K))) ∈ P.asIdeal := by
    rw [map_sub, map_pow, ← hcomm y]
    exact hρ'
  -- Since `P` lies over `Pn`, membership descends along `i`.
  have h3 : galRestrict (NumberField.RingOfIntegers L) L N (NumberField.RingOfIntegers N) τ y
      - y ^ Nat.card (NumberField.RingOfIntegers K ⧸
          P.asIdeal.under (NumberField.RingOfIntegers K)) ∈ Pn.asIdeal := by
    rw [hP.over, Ideal.mem_under]
    exact h2
  -- The exponents agree by hypothesis.
  rw [hf]
  exact h3

end NK.Reconstruct
