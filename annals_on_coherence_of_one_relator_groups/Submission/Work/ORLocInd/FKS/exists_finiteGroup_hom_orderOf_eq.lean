import Mathlib
import Submission.Work.ORLocInd.Hall.Basic
import Submission.Work.ORLocInd.Hall.exists_finite_pGroup_hom_ne_one_of_finset
import Submission.Work.ORLocInd.FKS.exists_finite_pGroup_quotient_orderOf_eq
import Submission.Work.ORLocInd.FKS.exists_finiteGroup_prod_of_components

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.ORLocInd.FKS

/-- In a free group, a nontrivial element has infinite order: `u ^ j ≠ 1` for every `j ≥ 1`.
(This is the torsion-freeness of free groups, `IsMulTorsionFree (FreeGroup α)`.) -/
lemma pow_ne_one_of_ne_one {α : Type u} {u : FreeGroup α} (hu : u ≠ 1) {j : ℕ} (hj : 0 < j) :
    u ^ j ≠ 1 :=
  fun h => hu (IsMulTorsionFree.pow_left_injective hj.ne' (by simpa using h))

/-- **Fischer--Karrass--Solitar 1972, Theorem 2, prime-power case.**  For a nontrivial element `u` of
a finitely generated free group and a prime power `p ^ e` with `e ≥ 1`, there is a finite quotient in
which the image of `u` has order exactly `p ^ e`.

Proof: by `Work.ORLocInd.Hall.exists_finite_pGroup_hom_ne_one_of_finset` (P. Hall: free groups are
residually finite `p`-groups), applied to the set of words `u, u ^ 2, …, u ^ (p ^ e - 1)` (all
nontrivial by torsion-freeness of the free group, `pow_ne_one_of_ne_one`), one finds a finite
`p`-group quotient `Q` with `ψ u` of order not dividing any of `1, …, p ^ e - 1`; as `Q` is a finite
`p`-group, `orderOf (ψ u) = p ^ m` for some `m ≥ e`.  The order reduction lemma
`Work.ORLocInd.FKS.exists_finite_pGroup_quotient_orderOf_eq` then cuts the order down to `p ^ e`. -/
theorem exists_pGroup_hom_orderOf_eq_prime_pow {α : Type u} [Fintype α]
    (H : ResiduallyFinitePGroup α) {u : FreeGroup α} (hu : u ≠ 1) {p : ℕ} (hp : p.Prime)
    {e : ℕ} (_he : 1 ≤ e) :
    ∃ (R : Type u) (_ : Group R) (_ : Finite R) (ψ : FreeGroup α →* R),
      orderOf (ψ u) = p ^ e := by
  classical
  obtain ⟨Q, _hQg, _hQf, hQp, ψ, hψ⟩ :=
    Hall.exists_finite_pGroup_hom_ne_one_of_finset H p hp
      ((Finset.Ico 1 (p ^ e)).image (fun j => u ^ j))
      (by
        intro w hw
        rw [Finset.mem_image] at hw
        obtain ⟨j, hj, rfl⟩ := hw
        rw [Finset.mem_Ico] at hj
        exact pow_ne_one_of_ne_one hu hj.1)
  haveI : Fact p.Prime := ⟨hp⟩
  -- the order of `ψ u` is a power of `p`, and the exponent is at least `e`
  obtain ⟨m, hm⟩ := hQp.exists_orderOf_eq_pow (ψ u)
  have hme : e ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 ≤ p ^ m := Nat.one_le_pow m p hp.pos
    have h2 : p ^ m < p ^ e := Nat.pow_lt_pow_right hp.one_lt hlt
    have hmem : u ^ p ^ m ∈ (Finset.Ico 1 (p ^ e)).image (fun j => u ^ j) := by
      rw [Finset.mem_image]
      exact ⟨p ^ m, by rw [Finset.mem_Ico]; exact ⟨h1, h2⟩, rfl⟩
    exact hψ _ hmem (by
      rw [map_pow]
      exact (orderOf_dvd_iff_pow_eq_one (x := ψ u) (n := p ^ m)).mp (by rw [hm]))
  -- cut the order down to exactly `p ^ e`
  have hquot : ∃ (R : Type u) (_ : Group R) (_ : Finite R) (_ : IsPGroup p R)
      (θ : Q →* R), orderOf (θ (ψ u)) = p ^ e :=
    exists_finite_pGroup_quotient_orderOf_eq hp hQp hm hme
  obtain ⟨R, hRg, hRf, _hRp, θ, hθ⟩ := hquot
  exact ⟨R, hRg, hRf, θ.comp ψ, hθ⟩

/-- **Fischer--Karrass--Solitar 1972, Theorem 2 (free-group form).**  For a finitely generated free
group `FreeGroup α`, a nontrivial element `u` and any `n ≥ 1`, there is a finite group quotient in
which the image of `u` has order exactly `n`.

Proof route (as in Fischer--Karrass--Solitar): write `n = ∏_{p ∈ P} p ^ (n.factorization p)` over
the primes `p` dividing `n`.  For each such `p`, let `e := n.factorization p ≥ 1`.  Since the free
group is torsion-free, the elements `u ^ j` (`1 ≤ j < p ^ e`) are all nontrivial, so
`Work.ORLocInd.Hall.exists_finite_pGroup_hom_ne_one_of_finset` (P. Hall's theorem, packaged as
`Work.ORLocInd.ResiduallyFinitePGroup`) produces one finite `p`-group quotient `Q p` separating all
of them; hence `p ^ e ∣ orderOf (ψ u)`, and since `Q p` is a finite `p`-group,
`orderOf (ψ u) = p ^ m` with `m ≥ e`.  Apply the order reduction
`Work.ORLocInd.FKS.exists_finite_pGroup_quotient_orderOf_eq` to cut the order down to exactly
`p ^ e`.  Finally take the product of the finitely many resulting quotients over the primes `p | n`
(a product of finite groups, again finite), where the order of the image of `u` is the product of
its orders in the factors because those orders are pairwise coprime
(`orderOf_mul_eq_mul_orderOf_of_coprime` together with the multiplicativity of the order along
coprime products), so the order is `∏_p p ^ e = n`. -/
theorem exists_finiteGroup_hom_orderOf_eq {α : Type u} [Fintype α] (H : ResiduallyFinitePGroup α)
    {u : FreeGroup α} (hu : u ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (ψ : FreeGroup α →* Q), orderOf (ψ u) = n := by
  have hn0 : n ≠ 0 := by omega
  -- the prime-power components, for the primes dividing `n`
  obtain ⟨Q, hQg, hQf, ψ, hψ⟩ :=
    exists_finiteGroup_prod_of_components (G := FreeGroup α) u n.primeFactors
      (fun p => n.factorization p)
      (by
        intro p hp q hq hpq
        exact Nat.Coprime.pow _ _
          ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors hq)).mpr hpq))
      (by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        exact exists_pGroup_hom_orderOf_eq_prime_pow H hu hpp
          (Nat.Prime.factorization_pos_of_dvd hpp hn0 (Nat.mem_primeFactors.mp hp).2.1))
  refine ⟨Q, hQg, hQf, ψ, ?_⟩
  -- the product of the prime powers is `n`
  rw [hψ]
  exact Nat.prod_factorization_pow_eq_self hn0

end Work.ORLocInd.FKS
