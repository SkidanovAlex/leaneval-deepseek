import Mathlib

namespace Work.ORLocInd.FKS

set_option linter.style.haveILetI false

universe u

/-- **Assembling components with pairwise coprime orders.**  Let `g` be an element of a group `G`.
Suppose that for each `p` in a finite set `s : Finset ℕ` we are given a finite group `R p` in the same
universe as `G` together with a homomorphism `ψ p : G →* R p` for which the image of `g` has order
exactly `p ^ e p`.  If the numbers `p ^ e p` are pairwise coprime over `p ∈ s`, then there is a single
finite group `Q` (again in the same universe) and a homomorphism `ψ : G →* Q` such that the image of
`g` has order exactly `∏ p ∈ s, p ^ e p`.

The intended proof is induction on `s`: the empty set is handled by the trivial group
`↥(⊥ : Subgroup G)`, and in the insert step one takes the product `R a × Q'` of the new component with
the one given by the induction hypothesis and uses `Prod.orderOf_mk` together with
`Nat.Coprime.lcm_eq_mul` (the hypothesis `hcop` supplies the coprimality of the two orders) and
`Finset.prod_insert`.  Both `Group` and `Finite` instances of a product are already available. -/
theorem exists_finiteGroup_prod_of_components {G : Type u} [Group G] (g : G)
    (s : Finset ℕ) (e : ℕ → ℕ)
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → (p ^ e p).Coprime (q ^ e q))
    (h : ∀ p ∈ s, ∃ (R : Type u) (_ : Group R) (_ : Finite R) (ψ : G →* R),
      orderOf (ψ g) = p ^ e p) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (ψ : G →* Q),
      orderOf (ψ g) = ∏ p ∈ s, p ^ e p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨↥(⊥ : Subgroup G), inferInstance, inferInstance, 1, ?_⟩
      simp
  | insert a t ha ih =>
      obtain ⟨R, iR, fR, ψ, hψ⟩ := h a (Finset.mem_insert_self a t)
      letI := iR
      letI := fR
      obtain ⟨Q', iQ, fQ, ψ', hψ'⟩ := ih
        (fun p hp q hq hpq =>
          hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq)
        (fun p hp => h p (Finset.mem_insert_of_mem hp))
      refine ⟨R × Q', inferInstance, inferInstance, ψ.prod ψ', ?_⟩
      have hcop' : (a ^ e a).Coprime (∏ p ∈ t, p ^ e p) :=
        Nat.Coprime.prod_right
          (fun b hb => hcop a (Finset.mem_insert_self a t) b (Finset.mem_insert_of_mem hb)
            (by rintro rfl; exact ha hb))
      have hord : orderOf ((ψ.prod ψ') g) = (a ^ e a).lcm (∏ p ∈ t, p ^ e p) := by
        rw [show (ψ.prod ψ') g = (ψ g, ψ' g) from rfl, Prod.orderOf_mk, hψ, hψ']
      rw [hord, hcop'.lcm_eq_mul, Finset.prod_insert ha]

end Work.ORLocInd.FKS
