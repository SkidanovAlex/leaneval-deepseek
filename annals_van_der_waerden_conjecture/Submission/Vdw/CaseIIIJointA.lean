import Mathlib
import Submission.Vdw.CaseIIIRootCount
import Submission.Vdw.Omega
import Submission.Vdw.CaseISieve
import Submission.Commons.Data.Int.interval_congruent_product_card_le

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Case III, subcase (ii): the joint squarefree-`A` constant-coefficient count

For the Case-III subcase-(ii) counting one fixes the upper coefficients
`u : Fin (n-1) → ℤ` and must count the constant coefficients `c ∈ [-H,H]` for which
`Disc(f_{u,c})` vanishes modulo every prime `p | A`, where `A` is a squarefree
divisor of `DD(u)` with `A > H`.  This module proves the joint bound

    #{c ∈ [-H,H] : ∀ p | A, p | Disc(monicOfUpper n u c)}
        ≤ 2 · (n-1)^{ω(A)}

for squarefree `A > H` whose prime factors are all `∤ n` (`3 ≤ n`):

* per prime `p | A`, the residue classes `c (mod p)` making `p | Disc(f_{u,c})`
  are the roots of `P̄_u` over `ZMod p`, at most `n-1` of them
  (`CaseIIIRootCount.concInnerZ_modp_root_card_le`);
* the joint multi-prime count is the CRT product bound
  `Commons.Data.Int.interval_congruent_product_card_le`
  (delegated: `|{z : |z| ≤ H, ∀ p, z mod p ∈ R p}| ≤ d^{|ι|}·((2H+1)/∏p + 1)`)
  instantiated at the prime divisors of `A`;
* `∏_{p | A} p = A` (`Squarefree`), so `(2H+1)/∏p + 1 ≤ 2` (`A > H`), and
  `|{p | A}| = ω(A)`.

The counted set is stated over the integer interval `{c : ℤ | |c| ≤ H}` (matching the
eventual assembly, which sums over `c = f.coeff 0`); a `BddInt`-typed corollary
`bddInt_discr_modA_joint_le` is derived by the trivial embedding `BddInt H ↪ ℤ`.
-/

noncomputable section

namespace Submission.Vdw

/-- **Case-III subcase-(ii) joint bound.**  For squarefree `A > H` whose prime divisors
all fail to divide `n` (`n ≥ 2`), and fixed upper coefficients `u`, at most
`2·(n-1)^{ω(A)}` integers `c` with `|c| ≤ H` satisfy
`∀ p | A : p | Disc(monicOfUpper n u c)`. -/
theorem joint_discr_modA_interval_le (n H A : ℕ) (hn : 2 ≤ n) (hsq : Squarefree A)
    (hAH : H < A) (hpn : ∀ p ∈ A.primeFactors, ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    ({c : ℤ | |c| ≤ (H : ℤ) ∧ ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u c)} : Set ℤ).ncard ≤
      2 * (n - 1) ^ omega A := by
  classical
  let s : Finset ℕ := A.primeFactors
  let ι : Type := {p : ℕ // p ∈ s}
  -- per-prime instances and objects
  haveI (p : ι) : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  haveI (p : ι) : NeZero (p : ℕ) := ⟨(Fact.out : Nat.Prime (p : ℕ)).ne_zero⟩
  let m : ι → ℕ := fun p => (p : ℕ)
  let R : (p : ι) → Set (ZMod (m p)) := fun p =>
    {x : ZMod (m p) | ((concInnerZ n u).map (Int.castRingHom (ZMod (m p)))).eval x = 0}
  -- hypothesis: per-prime root bound
  have hR (p : ι) : (R p).ncard ≤ n - 1 := by
    have hp : ¬ (p : ℕ) ∣ n := hpn (p : ℕ) (by simpa [s] using p.2)
    simpa [R, m] using concInnerZ_modp_root_card_le (p : ℕ) n hn hp u
  have hm1 (p : ι) : 1 ≤ m p := by
    dsimp [m]
    exact (Fact.out : Nat.Prime (p : ℕ)).one_lt.le
  have hcop : ∀ p q : ι, p ≠ q → Nat.Coprime (m p) (m q) := by
    intro p q hpq
    dsimp [m]
    exact (Nat.coprime_primes (Fact.out : Nat.Prime (p : ℕ))
      (Fact.out : Nat.Prime (q : ℕ))).2 (fun hEq => hpq (Subtype.ext hEq))
  -- the interval set counted by the fleet lemma
  let J' : Set ℤ := {z : ℤ | |z| ≤ (H : ℤ) ∧ ∀ i : ι, (z : ZMod (m i)) ∈ R i}
  -- fleet bound on J'
  have hJ' : J'.ncard ≤ (n - 1) ^ Fintype.card ι * ((2 * H + 1) / (∏ p : ι, m p) + 1) := by
    have hF := Commons.Data.Int.interval_congruent_product_card_le
      (H := H) (ι := ι) (m := m) (hm1 := hm1) (hcop := hcop) (d := n - 1) (R := R) (hR := hR)
    simpa [J'] using hF

  -- rewrite ∏ p : ι, m p = A
  have hprod : (∏ p : ι, m p) = A := by
    calc
      (∏ p : ι, m p) = ∏ p ∈ s, (p : ℕ) := by
        simpa [ι, m] using (prod_type_eq_finset s (fun p : ℕ => (p : ℕ)))
      _ = ∏ p ∈ A.primeFactors, p := by simp [s]
      _ = A := Nat.prod_primeFactors_of_squarefree hsq
  -- and the main counted set equals J'
  have hJ : ({c : ℤ | |c| ≤ (H : ℤ) ∧ ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u c)} : Set ℤ) = J' := by
    ext c
    constructor
    · intro hc
      refine ⟨hc.1, ?_⟩
      intro p
      have hdvd : ((p : ℕ) : ℤ) ∣ Polynomial.discr (monicOfUpper n u c) :=
        hc.2 (p : ℕ) (by simpa [s] using p.2)
      simpa [R, m] using
        (int_dvd_discr_monicOfUpper_iff_modp_root (p : ℕ) n (by omega : 1 ≤ n) u c).mp hdvd
    · intro hc
      refine ⟨hc.1, ?_⟩
      intro p hp
      haveI : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hroot : ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval (c : ZMod p) = 0 := by
        simpa [R, m] using hc.2 ⟨p, by simpa [s] using hp⟩
      exact (int_dvd_discr_monicOfUpper_iff_modp_root p n (by omega : 1 ≤ n) u c).mpr hroot
  -- cardinality identities
  have hcardι : Fintype.card ι = omega A := by
    dsimp [ι, s]
    unfold omega
    simp
  -- assemble
  calc
    ({c : ℤ | |c| ≤ (H : ℤ) ∧ ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u c)} : Set ℤ).ncard = J'.ncard := by
      rw [hJ]
    _ ≤ (n - 1) ^ Fintype.card ι * ((2 * H + 1) / (∏ p : ι, m p) + 1) := hJ'
    _ ≤ (n - 1) ^ Fintype.card ι * ((2 * H + 1) / A + 1) := by
      rw [hprod]
    _ ≤ (n - 1) ^ omega A * 2 := by
      rw [hcardι]
      exact Nat.mul_le_mul_left _ (div_twoH_add_one_le_two_of_lt H A hAH)
    _ = 2 * (n - 1) ^ omega A := by rw [Nat.mul_comm]

/-- `BddInt`-form of `joint_discr_modA_interval_le`. -/
theorem bddInt_discr_modA_joint_le (n H A : ℕ) (hn : 2 ≤ n) (hsq : Squarefree A)
    (hAH : H < A) (hpn : ∀ p ∈ A.primeFactors, ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    Nat.card {c : BddInt H // ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} ≤
      2 * (n - 1) ^ omega A := by
  classical
  let J : Set ℤ := {c : ℤ | |c| ≤ (H : ℤ) ∧ ∀ p ∈ A.primeFactors,
    (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u c)}
  have hJle : J.ncard ≤ 2 * (n - 1) ^ omega A := joint_discr_modA_interval_le n H A hn hsq hAH hpn u
  -- X embeds into {z : ℤ // z ∈ J}
  let X : Type := {c : BddInt H // ∀ p ∈ A.primeFactors,
    (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))}
  -- finiteness of the interval set (bounded integers)
  have hJfin : J.Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-(H : ℤ)) (H : ℤ))) ?_
    intro z hz
    rw [Finset.mem_coe]
    rw [Finset.mem_Icc]
    have hz1 : |z| ≤ (H : ℤ) := hz.1
    rw [abs_le] at hz1
    exact hz1
  haveI : Fintype {z : ℤ // z ∈ J} := hJfin.fintype
  -- X embeds into {z : ℤ // z ∈ J}
  have hXle : Nat.card X ≤ Nat.card {z : ℤ // z ∈ J} := by
    let f : X → {z : ℤ // z ∈ J} := fun c => ⟨(c : ℤ), by
      refine ⟨c.1.2, ?_⟩
      simpa using c.2⟩
    exact Nat.card_le_card_of_injective f (by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa [f] using congrArg (fun z : {z : ℤ // z ∈ J} => (z : ℤ)) hxy)
  have hJcard : Nat.card {z : ℤ // z ∈ J} = J.ncard := by
    exact (Commons.Data.Set.ncard_eq_natCard J).symm

  calc
    Nat.card {c : BddInt H // ∀ p ∈ A.primeFactors,
        (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} =
        Nat.card X := rfl
    _ ≤ Nat.card {z : ℤ // z ∈ J} := hXle
    _ = J.ncard := hJcard
    _ ≤ 2 * (n - 1) ^ omega A := hJle

end Submission.Vdw
