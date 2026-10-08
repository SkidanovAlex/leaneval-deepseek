import Mathlib
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj
import Submission.Work.Solvable.exists_normal_prime_quotient
import Submission.Work.Frobenius.Complement.exists_invariant_sylow_of_isPGroup_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

universe u v

namespace Work.Frobenius.Complement

/-- **Auxiliary induction** on `Nat.card A` for the coprime-action theorem: a finite solvable group
`A` acting by automorphisms on a finite group `N` with `Nat.card A` coprime to `Nat.card N` leaves
invariant a Sylow `r`-subgroup of `N`.

The induction step takes a normal subgroup `M ⊴ A` with `A ⧸ M` of prime order `q`
(`Work.Solvable.exists_normal_prime_quotient`), gets an `M`-invariant Sylow `P` from the induction
hypothesis, and lifts it to an `A`-invariant Sylow using
`Work.Frobenius.Complement.exists_invariant_sylow_of_isPGroup_quotient`. -/
private theorem main : ∀ (n : ℕ) (A : Type u) (N : Type v) [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N], Group.IsSolvable A → (Nat.card A).Coprime (Nat.card N) →
    ∀ {r : ℕ}, r.Prime → Nat.card A = n →
    ∃ P : Sylow r N, ∀ a : A, ∀ x : N, (x ∈ (P : Subgroup N) ↔ a • x ∈ (P : Subgroup N)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro A N hGA hGN hFA hFN hAct hsol hcop r hr hcard
    by_cases hnt : Nontrivial A
    · obtain ⟨q, hq, M, hMnorm, hMlt, hMcard⟩ := Work.Solvable.exists_normal_prime_quotient hsol hnt
      haveI : M.Normal := hMnorm
      haveI hsolM : Group.IsSolvable M := inferInstance
      have hMA : Nat.card M < Nat.card A := by
        have hdvd := Subgroup.card_subgroup_dvd_card M
        have hne : Nat.card M ≠ Nat.card A := fun h => hMlt.ne (Subgroup.eq_top_of_card_eq M h)
        exact Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.card_pos) hdvd) hne
      have hcopM : (Nat.card M).Coprime (Nat.card N) :=
        hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card M)
      have hMAn : Nat.card M < n := hcard ▸ hMA
      obtain ⟨P, hP⟩ := ih (Nat.card M) hMAn (A := ↥M) (N := N) hsolM hcopM hr rfl
      have hP'' : ∀ a : M, ∀ x : N,
          (x ∈ (P : Subgroup N) ↔ (a : A) • x ∈ (P : Subgroup N)) := by
        intro a x
        change x ∈ (P : Subgroup N) ↔ a • x ∈ (P : Subgroup N)
        exact hP a x
      obtain ⟨P', hP'⟩ := exists_invariant_sylow_of_isPGroup_quotient hsol hcop hr hq hMcard hP''
      exact ⟨P', hP'⟩
    · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hnt
      refine ⟨Sylow.nonempty.some, ?_⟩
      intro a x
      rw [Subsingleton.elim a 1, one_smul]

theorem exists_invariant_sylow_of_isSolvable {A N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] (hsol : Group.IsSolvable A) (hcop : (Nat.card A).Coprime (Nat.card N))
    {r : ℕ} (hr : r.Prime) :
    ∃ P : Sylow r N, ∀ a : A, ∀ x : N, (x ∈ (P : Subgroup N) ↔ a • x ∈ (P : Subgroup N)) :=
  main (Nat.card A) A N hsol hcop hr rfl

end Work.Frobenius.Complement
