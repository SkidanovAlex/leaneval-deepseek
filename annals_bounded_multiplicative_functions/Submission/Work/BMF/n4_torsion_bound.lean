import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mtorsion_prod_le
import Submission.Work.BMF.mtorsion_odd_prime_pow
import Submission.Work.BMF.mtorsion_two_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The `ℕ`-valued form of `n4_torsion_bound`: the number of `m`-th roots of unity in
`(ZMod q)ˣ` is at most `(2m)^{ω(q)}`.

This is proved by writing `q = ∏_{p ∈ q.primeFactors} p ^ q.factorization p`, applying the
Chinese-remainder bound `mtorsion_prod_le`, bounding each factor `(ZMod (p^e))ˣ` by `m` for odd
`p` (`mtorsion_odd_prime_pow`) and by `2m` for `p = 2` (`mtorsion_two_pow`), and multiplying
the bound `2m` over the `ω(q)` prime factors. -/
lemma n4_torsion_bound_nat (q m : ℕ) [NeZero q] (hm : 1 ≤ m) :
    ((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card ≤
      (2 * m) ^ q.primeFactors.card := by
  classical
  have hqne : q ≠ 0 := NeZero.ne q
  -- Factor `q` into its maximal prime powers.
  set s : Finset ℕ := q.primeFactors with hs
  set f : ℕ → ℕ := fun p ↦ p ^ q.factorization p with hf
  have hprod : ∏ p ∈ s, f p = q := by
    rw [hs, hf]
    exact (Nat.prod_primeFactors_pow_factorization hqne).symm
  -- Each factor is non-zero.
  have hf1 : ∀ p ∈ s, 1 ≤ f p := by
    intro p hp
    rw [hf]
    exact Nat.one_le_pow _ p ((Nat.mem_primeFactors.mp (hs ▸ hp)).1.pos)
  -- Distinct prime powers are coprime.
  have hcop : ∀ p ∈ s, ∀ r ∈ s, p ≠ r → (f p).Coprime (f r) := by
    intro p hp r hr hpr
    have hpp : p.Prime := (Nat.mem_primeFactors.mp (hs ▸ hp)).1
    have hrp : r.Prime := (Nat.mem_primeFactors.mp (hs ▸ hr)).1
    rw [hf]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hrp).mpr hpr)
  -- Chinese remainder theorem: bound the torsion of the whole product by that of the factors.
  have h1 := mtorsion_prod_le s f m hf1 hcop
  -- Identify the count of `m`-th roots of unity with the cardinality of the subgroup.
  have hLHS : ((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card
      = Nat.card (rootsOfUnity m (ZMod (∏ p ∈ s, f p))) := by
    rw [hprod]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [mem_rootsOfUnity]
  -- Each prime-power factor contributes at most `2 * m`.
  have hfac : ∀ p ∈ s, Nat.card (rootsOfUnity m (ZMod (f p))) ≤ 2 * m := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp (hs ▸ hp)).1
    by_cases hp2 : p = 2
    · subst hp2
      rw [hf]
      simp only []
      exact mtorsion_two_pow (q.factorization 2) m hm
    · rw [hf]
      simp only []
      have := mtorsion_odd_prime_pow p (q.factorization p) m hpp hp2 hm
      omega
  calc ((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card
      = Nat.card (rootsOfUnity m (ZMod (∏ p ∈ s, f p))) := hLHS
    _ ≤ ∏ p ∈ s, Nat.card (rootsOfUnity m (ZMod (f p))) := h1
    _ ≤ ∏ p ∈ s, (2 * m) := Finset.prod_le_prod hfac
    _ = (2 * m) ^ s.card := Finset.prod_const (2 * m)
    _ = (2 * m) ^ q.primeFactors.card := by rw [hs]

/-- **N4 auxiliary: the `m`-torsion of `(ZMod q)ˣ`.**  The number of `m`-th roots of unity
modulo `q` is at most `(2m)^{ω(q)}`, where `ω(q) = q.primeFactors.card`.

Route: CRT gives `(ZMod q)ˣ ≅ ∏_{p^e ‖ q} (ZMod (p^e))ˣ`, the `m`-torsion of a product is at
most the product of the `m`-torsions (`mtorsion_prod_le`), for odd `p` the group
`(ZMod (p^e))ˣ` is cyclic and its `m`-torsion has at most `m` elements
(`mtorsion_odd_prime_pow`), and for `p = 2` at most `2m` (`mtorsion_two_pow`).  These three
lemmas are already proved in this directory. -/
theorem n4_torsion_bound (q m : ℕ) [NeZero q] (hm : 1 ≤ m) :
    (((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card := by
  have h := n4_torsion_bound_nat q m hm
  have hcast : ((((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card : ℕ) : ℝ)
      ≤ (((2 * m) ^ q.primeFactors.card : ℕ) : ℝ) := Nat.cast_le.mpr h
  simpa [Nat.cast_pow] using hcast

end Work.BMF
