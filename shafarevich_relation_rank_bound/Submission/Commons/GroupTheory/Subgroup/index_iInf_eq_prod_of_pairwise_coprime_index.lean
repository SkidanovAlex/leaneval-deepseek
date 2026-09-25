import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.GroupTheory.Index

namespace Commons.GroupTheory.Subgroup

/-- A finite product of pairwise coprime naturals, each dividing `z`, divides `z`. -/
theorem prod_dvd_of_pairwise_coprime_index {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j))
    (hdvd : ∀ i ∈ s, f i ∣ z) : s.prod f ∣ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : f a ∣ z := hdvd a (Finset.mem_insert_self a s)
    have hprod : s.prod f ∣ z :=
      ih (fun i hi j hj hij =>
            hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
         (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
    have hc : (f a).Coprime (s.prod f) :=
      Nat.Coprime.prod_right (fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi)))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc hfa hprod

/-- **Multiplicativity of the index of a finite intersection with pairwise coprime indices.**

If `N i` (`i : ι`, `ι` finite) is a family of subgroups of a group `G` whose indices `[G : N i]`
are finite and pairwise coprime, then the index of the intersection `⨅ i, N i` is the product of
the indices: `[G : ⨅ i, N i] = ∏ i, [G : N i]`.

This is used to combine the norm index identities for the `ℓ`-Sylow subextensions of an abelian
extension of local fields.

See `Commons.GroupTheory.Subgroup.index_iInf_eq_prod_of_pairwise_coprime_index` if already
present; the proof is the `≤` bound `Subgroup.index_iInf_le` together with the divisibility
`∏ i, (N i).index ∣ (⨅ i, N i).index` obtained from `(N i).index ∣ (⨅ i, N i).index`
(`Subgroup.relIndex_mul_index` and `iInf_le`) and `Nat.Coprime.mul_dvd_of_dvd_of_dvd`. -/
theorem index_iInf_eq_prod_of_pairwise_coprime_index
    {G : Type*} [Group G] {ι : Type*} [Fintype ι] (N : ι → Subgroup G)
    (hfin : ∀ i, (N i).FiniteIndex)
    (hcop : Pairwise fun i j => (N i).index.Coprime (N j).index) :
    (⨅ i, N i).index = ∏ i, (N i).index := by
  have hfin' : (⨅ i, N i).FiniteIndex := Subgroup.finiteIndex_iInf hfin
  refine le_antisymm (Subgroup.index_iInf_le N) ?_
  -- Each index `(N i).index` divides the index of the whole intersection.
  have hsingle : ∀ i, (N i).index ∣ (⨅ i, N i).index := by
    intro i
    have h := Subgroup.relIndex_mul_index (iInf_le N i : (⨅ i, N i) ≤ N i)
    exact ⟨(⨅ i, N i).relIndex (N i), by rw [mul_comm]; exact h.symm⟩
  -- The whole product divides the index of the intersection.
  have hdivprod : ∏ i, (N i).index ∣ (⨅ i, N i).index :=
    prod_dvd_of_pairwise_coprime_index Finset.univ (fun i => (N i).index) (⨅ i, N i).index
      (fun i _ j _ hij => hcop hij) (fun i _ => hsingle i)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hfin'.index_ne_zero) hdivprod

end Commons.GroupTheory.Subgroup